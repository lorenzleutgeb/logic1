"""Benchmark the Logic1 RCF simplifier on SMT-LIB QF_NRA problems.

Run this module from a Logic1 source checkout, for example::

    python -m logic1.theories.RCF.smtlib.benchmark 'Pine:1,ezsmt:-20,Geo'
    python -m logic1.theories.RCF.smtlib.benchmark --convert-only all

The selected instances are processed sequentially.  Each instance runs in a
fresh process so that it can be stopped reliably when its timeout expires.
Standard output is JSON Lines: one metadata record followed by one result
record per completed instance.  Human-readable progress is written to standard
error.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import json
import multiprocessing as mp
from multiprocessing.connection import Connection
from multiprocessing.process import BaseProcess
import os
from pathlib import Path
import re
import sys
from time import perf_counter
from typing import Any, Callable, Sequence


DEFAULT_TIMEOUT_SECONDS = 30.0
DEFAULT_BENCHMARK_ROOT = Path(__file__).resolve().parents[4] / 'smtlib' / 'QF_NRA'

_DATE_PREFIX = re.compile(r'^\d+-')
_NATURAL_PART = re.compile(r'(\d+)')
_SINGLE_INDEX = re.compile(r'([1-9]\d*)')
_FIRST_RANGE = re.compile(r'-([1-9]\d*)')
_LAST_RANGE = re.compile(r'([1-9]\d*)-')
_CLOSED_RANGE = re.compile(r'([1-9]\d*)-([1-9]\d*)')


class SelectionError(ValueError):
    """An invalid benchmark root or suite selector."""


@dataclass(frozen=True)
class Family:
    """A named directory of deterministically ordered SMT-LIB problems."""

    name: str
    directory: Path
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


def _natural_key(value: str) -> tuple[tuple[int, int | str], ...]:
    """Return a case-insensitive key with numerical digit groups."""

    parts: list[tuple[int, int | str]] = []
    for part in _NATURAL_PART.split(value.casefold()):
        if part.isdigit():
            parts.append((1, int(part)))
        else:
            parts.append((0, part))
    return tuple(parts)


def discover_families(root: Path = DEFAULT_BENCHMARK_ROOT) -> tuple[Family, ...]:
    """Discover all immediate family directories below ``root``."""

    if not root.is_dir():
        raise SelectionError(f'benchmark root is not a directory: {root}')

    families: list[Family] = []
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
        problems = tuple(sorted(
            directory.rglob('*.smt2'),
            key=lambda path: _natural_key(path.relative_to(directory).as_posix())))
        families.append(Family(name, directory, problems))

    return tuple(sorted(
        families,
        key=lambda family: (_natural_key(family.name),
                            _natural_key(family.directory.name))))


def _resolve_family(prefix: str, families: Sequence[Family]) -> Family:
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


def select_instances(selector: str, families: Sequence[Family],
                     root: Path) -> tuple[Instance, ...]:
    """Resolve ``selector`` to an ordered sequence of benchmark instances."""

    selector = selector.strip()
    if not selector:
        raise SelectionError('empty benchmark selector')

    selected: list[tuple[Family, Sequence[Path]]]
    if selector.casefold() == 'all':
        selected = [(family, family.problems) for family in families]
    else:
        selected = []
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

            if range_specification is None:
                problems: Sequence[Path] = family.problems
            else:
                first, last = _problem_bounds(
                    range_specification, len(family.problems))
                problems = family.problems[first:last]
            selected.append((family, problems))

    return tuple(
        Instance(
            family=family.name,
            path=path.resolve(),
            problem=path.relative_to(root).as_posix())
        for family, problems in selected
        for path in problems)


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


def benchmark_instance(instance: Instance, timeout_seconds: float,
                       convert_only: bool = False,
                       context: Any | None = None) \
        -> dict[str, Any]:
    """Run one instance with a hard timeout and return its JSON record."""

    if timeout_seconds <= 0:
        raise ValueError('timeout_seconds must be positive')
    if context is None:
        # Fork inherits Logic1's expensive imports from the supervisor.  The
        # worker is still isolated in its own process and can therefore be
        # terminated reliably when the timeout expires.
        context = mp.get_context('fork')

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

    phase = 'startup'
    atoms_before: int | None = None
    smtlib_variables: dict[str, int] | None = None
    prepared_elapsed: float | None = None
    run_start: float | None = None
    final: dict[str, Any] | None = None

    try:
        # Worker initialization is not part of the benchmark.  The same limit
        # prevents a broken child from blocking the suite before its handshake.
        if not receive.poll(timeout_seconds):
            elapsed = perf_counter() - startup_start
            return _record(
                instance,
                status='timeout',
                phase=phase,
                runtime_seconds=elapsed,
                simplification_runtime_seconds=None,
                atoms_before=None,
                atoms_after=None,
                error=None)

        try:
            started = receive.recv()
        except EOFError:
            started = None
        if not isinstance(started, dict) or started.get('kind') != 'started':
            return _record(
                instance,
                status='error',
                phase=phase,
                runtime_seconds=perf_counter() - startup_start,
                simplification_runtime_seconds=None,
                atoms_before=None,
                atoms_after=None,
                error={
                    'type': 'WorkerProcessError',
                    'message': 'worker exited before its startup handshake',
                })

        run_start = perf_counter()
        deadline = run_start + timeout_seconds
        while final is None:
            remaining = deadline - perf_counter()
            if remaining <= 0 or not receive.poll(remaining):
                elapsed = perf_counter() - run_start
                simplification_runtime = None
                if prepared_elapsed is not None:
                    simplification_runtime = max(0.0, elapsed - prepared_elapsed)
                return _record(
                    instance,
                    status='timeout',
                    phase=phase,
                    runtime_seconds=elapsed,
                    simplification_runtime_seconds=simplification_runtime,
                    smtlib_variables=smtlib_variables,
                    atoms_before=atoms_before,
                    atoms_after=None,
                    error=None)
            try:
                message = receive.recv()
            except EOFError:
                break
            kind = message.get('kind')
            if kind == 'phase':
                phase = message['phase']
                smtlib_variables = message.get('smtlib_variables')
            elif kind == 'prepared':
                phase = 'simplify'
                atoms_before = message['atoms_before']
                prepared_elapsed = message['elapsed_seconds']
            elif kind == 'result':
                final = message

        if final is None:
            elapsed = perf_counter() - run_start
            return _record(
                instance,
                status='error',
                phase=phase,
                runtime_seconds=elapsed,
                simplification_runtime_seconds=None,
                smtlib_variables=smtlib_variables,
                atoms_before=atoms_before,
                atoms_after=None,
                error={
                    'type': 'WorkerProcessError',
                    'message': f'worker exited with code {process.exitcode}',
                })

        final.pop('kind', None)
        return _record(instance, **final)
    finally:
        receive.close()
        _stop_process(process)


def run_benchmarks(selector: str, root: Path = DEFAULT_BENCHMARK_ROOT,
                   timeout_seconds: float = DEFAULT_TIMEOUT_SECONDS,
                   convert_only: bool = False,
                   on_start: Callable[[dict[str, Any]], None] | None = None,
                   on_result: Callable[[dict[str, Any]], None] | None = None) \
        -> dict[str, Any]:
    """Select and sequentially benchmark a QF_NRA suite."""

    families = discover_families(root)
    instances = select_instances(selector, families, root)
    metadata = {
        'selector': selector,
        'timeout_seconds': timeout_seconds,
        'convert_only': convert_only,
    }
    if on_start is not None:
        on_start(metadata)
    results: list[dict[str, Any]] = []
    total = len(instances)
    for number, instance in enumerate(instances, start=1):
        result = benchmark_instance(instance, timeout_seconds, convert_only)
        results.append(result)
        if on_result is not None:
            on_result(result)
        print(
            f'[{number}/{total}] {instance.problem}: {result["status"]} '
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
        description='Benchmark Logic1 RCF simplification on QF_NRA SMT-LIB files.')
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
