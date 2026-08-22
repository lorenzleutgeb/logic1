"""Benchmark the Logic1 RCF simplifier on SMT-LIB problems.

Run this module from a Logic1 source checkout, for example::

    python -m logic1.theories.RCF.smtlib.benchmark 'Pine:1,ezsmt:-20,Geo'
    python -m logic1.theories.RCF.smtlib.benchmark --logic=QF_NRA all
    python -m logic1.theories.RCF.smtlib.benchmark --convert-only all

The selected instances are processed concurrently.  Each instance runs in a
fresh process so that it can be stopped reliably when its timeout expires.
Standard output is JSON Lines: one metadata record followed by one result
record per completed instance.  The coordinating process serializes both JSON
results and human-readable progress; the latter is written to standard error.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import json
import multiprocessing as mp
from multiprocessing.connection import Connection, wait
from multiprocessing.process import BaseProcess
import os
from pathlib import Path
import re
import sys
from time import perf_counter
from typing import Any, Callable, cast, Iterator, Sequence, TypeVar


DEFAULT_TIMEOUT_SECONDS = 30.0
DEFAULT_LOGIC = 'QF_NRA'
DEFAULT_BENCHMARK_BASE = Path(__file__).resolve().parents[4] / 'smtlib'
DEFAULT_BENCHMARK_ROOT = DEFAULT_BENCHMARK_BASE / DEFAULT_LOGIC

_DATE_PREFIX = re.compile(r'^\d+-')
_NATURAL_PART = re.compile(r'(\d+)')
_SINGLE_INDEX = re.compile(r'([1-9]\d*)')
_FIRST_RANGE = re.compile(r'-([1-9]\d*)')
_LAST_RANGE = re.compile(r'([1-9]\d*)-')
_CLOSED_RANGE = re.compile(r'([1-9]\d*)-([1-9]\d*)')


class SelectionError(ValueError):
    """An invalid benchmark root or suite selector."""


@dataclass(frozen=True)
class FamilyDirectory:
    """A named SMT-LIB family directory."""

    name: str
    directory: Path


@dataclass(frozen=True)
class Family(FamilyDirectory):
    """A family with its deterministically ordered SMT-LIB problems."""

    problems: tuple[Path, ...]


@dataclass(frozen=True)
class Instance:
    """One selected benchmark problem."""

    family: str
    path: Path
    problem: str


def friendly_family_name(directory_name: str) -> str:
    """Remove the optional SMT-LIB date prefix from a family directory."""

    return _DATE_PREFIX.sub('', directory_name, count=1)


def benchmark_root(logic: str) -> Path:
    """Return the corpus directory for one SMT-LIB logic."""

    component = Path(logic)
    if not logic or component.is_absolute() or len(component.parts) != 1 \
            or logic in {'.', '..'}:
        raise SelectionError(f'invalid SMT-LIB logic: {logic!r}')
    return DEFAULT_BENCHMARK_BASE / logic


def _natural_key(value: str) -> tuple[tuple[int, int | str], ...]:
    """Return a case-insensitive key with numerical digit groups."""

    parts: list[tuple[int, int | str]] = []
    for part in _NATURAL_PART.split(value.casefold()):
        if part.isdigit():
            parts.append((1, int(part)))
        else:
            parts.append((0, part))
    return tuple(parts)


def _discover_family_directories(root: Path) -> tuple[FamilyDirectory, ...]:
    if not root.is_dir():
        raise SelectionError(f'benchmark root is not a directory: {root}')

    families: list[FamilyDirectory] = []
    names: dict[str, Path] = {}
    for directory in root.iterdir():
        if not directory.is_dir():
            continue
        name = friendly_family_name(directory.name)
        folded_name = name.casefold()
        if folded_name in names:
            raise SelectionError(
                f'duplicate friendly family name {name!r}: '
                f'{names[folded_name]} and {directory}')
        names[folded_name] = directory
        families.append(FamilyDirectory(name, directory))

    return tuple(sorted(
        families,
        key=lambda family: (_natural_key(family.name),
                            _natural_key(family.directory.name))))


def _discover_problems(family: FamilyDirectory) -> Family:
    problems = tuple(sorted(
        family.directory.rglob('*.smt2'),
        key=lambda path: _natural_key(
            path.relative_to(family.directory).as_posix())))
    return Family(family.name, family.directory, problems)


def discover_families(root: Path = DEFAULT_BENCHMARK_ROOT) -> tuple[Family, ...]:
    """Discover all families and their SMT-LIB problems below ``root``."""

    return tuple(
        _discover_problems(family)
        for family in _discover_family_directories(root))


_FamilyT = TypeVar('_FamilyT', bound=FamilyDirectory)


def _resolve_family(prefix: str, families: Sequence[_FamilyT]) -> _FamilyT:
    folded_prefix = prefix.casefold()
    exact = [family for family in families
             if family.name.casefold() == folded_prefix]
    if exact:
        return exact[0]

    matches = [family for family in families
               if family.name.casefold().startswith(folded_prefix)]
    if not matches:
        raise SelectionError(f'unknown family prefix: {prefix!r}')
    if len(matches) > 1:
        names = ', '.join(family.name for family in matches)
        raise SelectionError(
            f'ambiguous family prefix {prefix!r}; matches: {names}')
    return matches[0]


def _problem_bounds(specification: str, count: int) -> tuple[int, int]:
    """Parse a 1-based inclusive range and return zero-based slice bounds."""

    match = _SINGLE_INDEX.fullmatch(specification)
    if match:
        first = last = int(match.group(1))
    else:
        match = _FIRST_RANGE.fullmatch(specification)
        if match:
            first, last = 1, int(match.group(1))
        else:
            match = _LAST_RANGE.fullmatch(specification)
            if match:
                first, last = int(match.group(1)), count
            else:
                match = _CLOSED_RANGE.fullmatch(specification)
                if not match:
                    raise SelectionError(
                        f'invalid problem range: {specification!r}')
                first, last = int(match.group(1)), int(match.group(2))

    if first > last:
        raise SelectionError(
            f'reversed problem range: {specification!r}')
    if first > count or last > count:
        raise SelectionError(
            f'problem range {specification!r} exceeds family size {count}')
    return first - 1, last


def _select_families(selector: str, families: Sequence[_FamilyT]) \
        -> list[tuple[_FamilyT, str | None]]:
    selector = selector.strip()
    if not selector:
        raise SelectionError('empty benchmark selector')

    if selector.casefold() == 'all':
        return [(family, None) for family in families]

    selected: list[tuple[_FamilyT, str | None]] = []
    seen: set[Path] = set()
    for raw_item in selector.split(','):
        item = raw_item.strip()
        if not item:
            raise SelectionError(f'invalid empty selector item in {selector!r}')
        if item.count(':') > 1:
            raise SelectionError(f'invalid selector item: {item!r}')
        if ':' in item:
            prefix, range_specification = (
                component.strip() for component in item.split(':', 1))
            if not prefix or not range_specification:
                raise SelectionError(f'invalid selector item: {item!r}')
        else:
            prefix, range_specification = item, None

        family = _resolve_family(prefix, families)
        if family.directory in seen:
            raise SelectionError(
                f'family selected more than once: {family.name!r}')
        seen.add(family.directory)
        selected.append((family, range_specification))

    return selected


def _instances_from_families(
        selected: Sequence[tuple[Family, str | None]],
        root: Path, logic: str) -> tuple[Instance, ...]:
    selected_problems: list[tuple[Family, Sequence[Path]]] = []
    for family, range_specification in selected:
        if range_specification is None:
            problems: Sequence[Path] = family.problems
        else:
            first, last = _problem_bounds(
                range_specification, len(family.problems))
            problems = family.problems[first:last]
        selected_problems.append((family, problems))

    return tuple(
        Instance(
            family=family.name,
            path=path.resolve(),
            problem=(Path(logic) / path.relative_to(root)).as_posix())
        for family, problems in selected_problems
        for path in problems)


def select_instances(selector: str, families: Sequence[Family],
                     root: Path, logic: str = DEFAULT_LOGIC) \
        -> tuple[Instance, ...]:
    """Resolve ``selector`` among already discovered ``families``."""

    return _instances_from_families(
        _select_families(selector, families), root, logic)


def discover_instances(selector: str, root: Path,
                       logic: str = DEFAULT_LOGIC) -> tuple[Instance, ...]:
    """Discover problems only in the families selected by ``selector``."""

    families = _discover_family_directories(root)
    selected = _select_families(selector, families)
    discovered = [
        (_discover_problems(family), range_specification)
        for family, range_specification in selected]
    return _instances_from_families(discovered, root, logic)


def _send(connection: Connection, message: dict[str, Any]) -> None:
    """Send a worker event unless the supervisor has already disconnected."""

    try:
        connection.send(message)
    except (BrokenPipeError, EOFError, OSError):
        pass


def _benchmark_worker(problem: str, convert_only: bool,
                      connection: Connection) -> None:
    """Parse, convert, and simplify one problem in a child process."""

    total_start = perf_counter()
    phase = 'parse'
    atoms_before: int | None = None
    smtlib_variables: dict[str, int] | None = None
    simplification_start: float | None = None
    _send(connection, {'kind': 'started'})
    _send(connection, {'kind': 'phase', 'phase': phase})

    try:
        # PySMT 0.9.5's optional Cython parser loader imports the removed
        # ``imp`` module on Python 3.14.
        os.environ['PYSMT_CYTHON'] = '0'

        from pysmt.environment import Environment  # type: ignore[import-untyped]
        from pysmt.smtlib.parser import SmtLibParser  # type: ignore[import-untyped]

        from logic1.firstorder import Formula
        from logic1.theories.RCF import simplify

        environment = Environment()
        manager = environment.formula_manager
        script = SmtLibParser(environment=environment).get_script_fname(problem)
        pysmt_formula = script.get_strict_formula(manager)
        smtlib_variables = {}
        for variable in pysmt_formula.get_free_variables():
            type_name = str(variable.symbol_type())
            smtlib_variables[type_name] = smtlib_variables.get(type_name, 0) + 1
        smtlib_variables = dict(sorted(smtlib_variables.items()))

        phase = 'convert'
        _send(connection, {
            'kind': 'phase',
            'phase': phase,
            'smtlib_variables': smtlib_variables,
        })
        formula = Formula.from_smtlib(pysmt_formula)
        atoms_before = sum(1 for _ in formula.atoms())

        if convert_only:
            _send(connection, {
                'kind': 'result',
                'status': 'ok',
                'phase': 'convert',
                'runtime_seconds': perf_counter() - total_start,
                'simplification_runtime_seconds': None,
                'smtlib_variables': smtlib_variables,
                'atoms_before': atoms_before,
                'atoms_after': None,
                'error': None,
            })
            return

        phase = 'simplify'
        prepared_at = perf_counter()
        _send(connection, {
            'kind': 'prepared',
            'atoms_before': atoms_before,
            'elapsed_seconds': prepared_at - total_start,
        })
        simplification_start = perf_counter()
        simplified = simplify(formula)
        simplification_runtime = perf_counter() - simplification_start
        atoms_after = sum(1 for _ in simplified.atoms())

        _send(connection, {
            'kind': 'result',
            'status': 'ok',
            'phase': 'complete',
            'runtime_seconds': perf_counter() - total_start,
            'simplification_runtime_seconds': simplification_runtime,
            'smtlib_variables': smtlib_variables,
            'atoms_before': atoms_before,
            'atoms_after': atoms_after,
            'error': None,
        })
    except Exception as exc:
        simplification_runtime = None
        if simplification_start is not None:
            simplification_runtime = perf_counter() - simplification_start
        _send(connection, {
            'kind': 'result',
            'status': 'error',
            'phase': phase,
            'runtime_seconds': perf_counter() - total_start,
            'simplification_runtime_seconds': simplification_runtime,
            'smtlib_variables': smtlib_variables,
            'atoms_before': atoms_before,
            'atoms_after': None,
            'error': {
                'type': type(exc).__name__,
                'message': str(exc),
            },
        })
    finally:
        connection.close()


def _stop_process(process: BaseProcess) -> None:
    if process.is_alive():
        process.terminate()
    process.join(timeout=1.0)
    if process.is_alive():
        process.kill()
        process.join()


def _record(instance: Instance, **values: Any) -> dict[str, Any]:
    return {
        'family': instance.family,
        'problem': instance.problem,
        'smtlib': {
            'variables': values.pop('smtlib_variables', None),
        },
        **values,
    }


@dataclass
class _RunningInstance:
    instance: Instance
    receive: Connection
    process: BaseProcess
    startup_start: float
    deadline: float
    phase: str = 'startup'
    atoms_before: int | None = None
    smtlib_variables: dict[str, int] | None = None
    prepared_elapsed: float | None = None
    run_start: float | None = None


def benchmark_worker_count() -> int:
    """Return the number of concurrent workers for this machine."""

    return max(1, (os.process_cpu_count() or 1) - 2)


def _start_instance(instance: Instance, timeout_seconds: float,
                    convert_only: bool, context: Any) \
        -> _RunningInstance | dict[str, Any]:
    receive, send = context.Pipe(duplex=False)
    process = context.Process(
        target=_benchmark_worker,
        args=(str(instance.path), convert_only, send))
    startup_start = perf_counter()
    try:
        process.start()
    except Exception as exc:
        receive.close()
        send.close()
        return _record(
            instance,
            status='error',
            phase='startup',
            runtime_seconds=perf_counter() - startup_start,
            simplification_runtime_seconds=None,
            atoms_before=None,
            atoms_after=None,
            error={'type': type(exc).__name__, 'message': str(exc)})
    send.close()
    return _RunningInstance(
        instance=instance,
        receive=receive,
        process=process,
        startup_start=startup_start,
        deadline=startup_start + timeout_seconds)


def _timeout_result(run: _RunningInstance, now: float) -> dict[str, Any]:
    start = run.run_start if run.run_start is not None else run.startup_start
    elapsed = now - start
    simplification_runtime = None
    if run.prepared_elapsed is not None:
        simplification_runtime = max(0.0, elapsed - run.prepared_elapsed)
    return _record(
        run.instance,
        status='timeout',
        phase=run.phase,
        runtime_seconds=elapsed,
        simplification_runtime_seconds=simplification_runtime,
        smtlib_variables=run.smtlib_variables,
        atoms_before=run.atoms_before,
        atoms_after=None,
        error=None)


def _worker_error_result(run: _RunningInstance, now: float) -> dict[str, Any]:
    start = run.run_start if run.run_start is not None else run.startup_start
    if run.run_start is None:
        message = 'worker exited before its startup handshake'
    else:
        message = f'worker exited with code {run.process.exitcode}'
    return _record(
        run.instance,
        status='error',
        phase=run.phase,
        runtime_seconds=now - start,
        simplification_runtime_seconds=None,
        smtlib_variables=run.smtlib_variables,
        atoms_before=run.atoms_before,
        atoms_after=None,
        error={'type': 'WorkerProcessError', 'message': message})


def _handle_message(run: _RunningInstance, message: Any,
                    timeout_seconds: float) -> dict[str, Any] | None:
    if not isinstance(message, dict):
        return _worker_error_result(run, perf_counter())

    kind = message.get('kind')
    if run.run_start is None:
        if kind != 'started':
            return _worker_error_result(run, perf_counter())
        run.run_start = perf_counter()
        run.deadline = run.run_start + timeout_seconds
    elif kind == 'phase':
        run.phase = message['phase']
        run.smtlib_variables = message.get('smtlib_variables')
    elif kind == 'prepared':
        run.phase = 'simplify'
        run.atoms_before = message['atoms_before']
        run.prepared_elapsed = message['elapsed_seconds']
    elif kind == 'result':
        message.pop('kind', None)
        return _record(run.instance, **message)
    return None


def benchmark_instances(
        instances: Sequence[Instance], timeout_seconds: float,
        convert_only: bool = False, workers: int = 1,
        context: Any | None = None) -> Iterator[dict[str, Any]]:
    """Run fresh instance processes concurrently and yield completed records."""

    if timeout_seconds <= 0:
        raise ValueError('timeout_seconds must be positive')
    if workers <= 0:
        raise ValueError('workers must be positive')
    if context is None:
        # Fork inherits Logic1's expensive imports from the supervisor.  The
        # workers are still isolated in their own processes and can therefore be
        # terminated reliably when the timeout expires.
        context = mp.get_context('fork')

    pending = iter(instances)
    exhausted = False
    running: dict[Connection, _RunningInstance] = {}
    try:
        while running or not exhausted:
            while len(running) < workers and not exhausted:
                try:
                    instance = next(pending)
                except StopIteration:
                    exhausted = True
                    break
                started = _start_instance(
                    instance, timeout_seconds, convert_only, context)
                if isinstance(started, dict):
                    yield started
                else:
                    running[started.receive] = started

            if not running:
                continue

            now = perf_counter()
            remaining = min(run.deadline for run in running.values()) - now
            ready = wait(running, timeout=max(0.0, remaining))
            for ready_connection in ready:
                connection = cast(Connection, ready_connection)
                run = running.get(connection)
                if run is None:
                    continue
                result: dict[str, Any] | None
                try:
                    message = connection.recv()
                except EOFError:
                    result = _worker_error_result(run, perf_counter())
                else:
                    result = _handle_message(run, message, timeout_seconds)
                if result is not None:
                    del running[connection]
                    connection.close()
                    _stop_process(run.process)
                    yield result

            now = perf_counter()
            expired = [
                connection for connection, run in running.items()
                if run.deadline <= now]
            for connection in expired:
                run = running.pop(connection)
                result = _timeout_result(run, now)
                connection.close()
                _stop_process(run.process)
                yield result
    finally:
        for run in running.values():
            run.receive.close()
            _stop_process(run.process)


def benchmark_instance(instance: Instance, timeout_seconds: float,
                       convert_only: bool = False,
                       context: Any | None = None) \
        -> dict[str, Any]:
    """Run one instance with a hard timeout and return its JSON record."""

    return next(benchmark_instances(
        [instance], timeout_seconds, convert_only, context=context))


def run_benchmarks(selector: str, root: Path | None = None,
                   timeout_seconds: float = DEFAULT_TIMEOUT_SECONDS,
                   convert_only: bool = False,
                   workers: int | None = None,
                   logic: str = DEFAULT_LOGIC,
                   on_start: Callable[[dict[str, Any]], None] | None = None,
                   on_result: Callable[[dict[str, Any]], None] | None = None) \
        -> dict[str, Any]:
    """Select and concurrently benchmark a QF_NRA suite."""

    expected_root = benchmark_root(logic)
    if root is None:
        root = expected_root
    instances = discover_instances(selector, root, logic)
    if workers is None:
        workers = benchmark_worker_count()
    metadata = {
        'selector': selector,
        'logic': logic,
        'timeout_seconds': timeout_seconds,
        'convert_only': convert_only,
        'workers': workers,
    }
    if on_start is not None:
        on_start(metadata)
    results: list[dict[str, Any]] = []
    total = len(instances)
    completed = benchmark_instances(
        instances, timeout_seconds, convert_only, workers)
    for number, result in enumerate(completed, start=1):
        results.append(result)
        if on_result is not None:
            on_result(result)
        print(
            f'[{number}/{total}] {result["problem"]}: {result["status"]} '
            f'({result["phase"]}, {result["runtime_seconds"]:.3f}s)',
            file=sys.stderr,
            flush=True)
    return {**metadata, 'results': results}


def _write_json_line(record: dict[str, Any]) -> None:
    json.dump(record, sys.stdout)
    sys.stdout.write('\n')
    sys.stdout.flush()


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description='Benchmark Logic1 RCF simplification on SMT-LIB files.')
    parser.add_argument(
        '--logic',
        default=DEFAULT_LOGIC,
        help=f'SMT-LIB logic directory (default: {DEFAULT_LOGIC})')
    parser.add_argument(
        'selector',
        help="suite selector such as 'Pine:1,ezsmt:-20,Geo' or 'all'")
    parser.add_argument(
        '--convert-only',
        action='store_true',
        help='stop after conversion to Logic1, without simplification')
    arguments = parser.parse_args(argv)

    try:
        run_benchmarks(
            arguments.selector,
            convert_only=arguments.convert_only,
            logic=arguments.logic,
            on_start=lambda metadata: _write_json_line({
                'type': 'metadata',
                **metadata,
            }),
            on_result=lambda result: _write_json_line({
                'type': 'result',
                **result,
            }))
    except SelectionError as exc:
        print(f'{parser.prog}: error: {exc}', file=sys.stderr)
        return 2

    return 0


if __name__ == '__main__':
    raise SystemExit(main())
