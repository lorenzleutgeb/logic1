import json
import os
from pathlib import Path
from time import sleep
from typing import Any

import pytest

from logic1.theories.RCF.smtlib import benchmark


def _problem(path: Path, contents: str = '') -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(contents)
    return path


@pytest.fixture
def benchmark_root(tmp_path: Path) -> Path:
    root = tmp_path / 'QF_NRA'
    for number in range(1, 26):
        _problem(root / '20200911-Pine' / f'problem{number}.smt2')
    for number in range(1, 21):
        _problem(root / '2019-ezsmt' / f'problem{number}.smt2')
    _problem(root / '20211101-Geogebra' / 'problem1.smt2')
    _problem(root / 'Sturm-MBO' / 'problem1.smt2')
    _problem(root / 'Sturm-MGC' / 'problem1.smt2')
    return root


def test_discover_and_select(benchmark_root: Path) -> None:
    families = benchmark.discover_families(benchmark_root)
    by_name = {family.name: family for family in families}

    assert set(by_name) == {
        'Pine', 'ezsmt', 'Geogebra', 'Sturm-MBO', 'Sturm-MGC'}
    assert [path.name for path in by_name['Pine'].problems[:3]] == [
        'problem1.smt2', 'problem2.smt2', 'problem3.smt2']
    assert by_name['Pine'].problems[-1].name == 'problem25.smt2'

    selected = benchmark.select_instances(
        'pine:1,EZS:-20,Geo', families, benchmark_root)
    assert [(instance.family, instance.path.name) for instance in selected[:2]] == [
        ('Pine', 'problem1.smt2'),
        ('ezsmt', 'problem1.smt2'),
    ]
    assert selected[-2].family == 'ezsmt'
    assert selected[-2].path.name == 'problem20.smt2'
    assert selected[-1].family == 'Geogebra'


def test_inclusive_range_forms(benchmark_root: Path) -> None:
    families = benchmark.discover_families(benchmark_root)

    def names(selector: str) -> list[str]:
        return [instance.path.name for instance in
                benchmark.select_instances(selector, families, benchmark_root)]

    assert names('Pine:4') == ['problem4.smt2']
    assert names('Pine:-3') == [
        'problem1.smt2', 'problem2.smt2', 'problem3.smt2']
    assert names('Pine:23-') == [
        'problem23.smt2', 'problem24.smt2', 'problem25.smt2']
    assert names('Pine:10-12') == [
        'problem10.smt2', 'problem11.smt2', 'problem12.smt2']
    assert len(names('Pine')) == 25


def test_all_selector(benchmark_root: Path) -> None:
    families = benchmark.discover_families(benchmark_root)
    selected = benchmark.select_instances('all', families, benchmark_root)

    assert len(selected) == 48
    assert {instance.family for instance in selected} == {
        'Pine', 'ezsmt', 'Geogebra', 'Sturm-MBO', 'Sturm-MGC'}


def test_discover_instances_only_traverses_selected_families(
        benchmark_root: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    rglob = Path.rglob
    traversed: list[str] = []

    def recording_rglob(directory: Path, pattern: str) -> Any:
        traversed.append(directory.name)
        return rglob(directory, pattern)

    monkeypatch.setattr(Path, 'rglob', recording_rglob)

    selected = benchmark.discover_instances(
        'Pine:1,Geo', benchmark_root)

    assert [instance.family for instance in selected] == ['Pine', 'Geogebra']
    assert traversed == ['20200911-Pine', '20211101-Geogebra']

    traversed.clear()
    with pytest.raises(benchmark.SelectionError):
        benchmark.discover_instances('Sturm', benchmark_root)
    assert traversed == []

    all_instances = benchmark.discover_instances('all', benchmark_root)
    assert len(all_instances) == 48
    assert set(traversed) == {
        '20200911-Pine', '2019-ezsmt', '20211101-Geogebra',
        'Sturm-MBO', 'Sturm-MGC'}


def test_problem_path_includes_logic(benchmark_root: Path) -> None:
    selected = benchmark.discover_instances(
        'Pine:1', benchmark_root, logic='QF_LRA')

    assert selected[0].problem == 'QF_LRA/20200911-Pine/problem1.smt2'


@pytest.mark.parametrize('logic', ['', '.', '..', '../QF_NRA', '/QF_NRA'])
def test_invalid_logic(logic: str) -> None:
    with pytest.raises(benchmark.SelectionError):
        benchmark.benchmark_root(logic)


@pytest.mark.parametrize('selector', [
    '',
    'unknown',
    'Sturm',
    'Pine,Pine:1',
    'Pine:0',
    'Pine:',
    'Pine:1:2',
    'Pine:5-2',
    'Pine:26',
    'Pine:-26',
    'Pine:1-26',
    'Pine,,Geo',
])
def test_invalid_selectors(benchmark_root: Path, selector: str) -> None:
    families = benchmark.discover_families(benchmark_root)
    with pytest.raises(benchmark.SelectionError):
        benchmark.select_instances(selector, families, benchmark_root)


def test_missing_root(tmp_path: Path) -> None:
    with pytest.raises(benchmark.SelectionError):
        benchmark.discover_families(tmp_path / 'missing')


def test_success_and_conversion_error_continue(
        tmp_path: Path, capsys: pytest.CaptureFixture[str]) -> None:
    root = tmp_path / 'QF_NRA'
    _problem(root / '20200101-Demo' / 'problem1.smt2', '''
(set-logic QF_NRA)
(declare-fun x () Real)
(declare-fun y () Real)
(assert (= (/ x y) 1))
(check-sat)
''')
    _problem(root / '20200101-Demo' / 'problem2.smt2', '''
(set-logic QF_NRA)
(declare-fun x () Real)
(assert (and (> x 0) (>= x 0)))
(check-sat)
''')

    coordinator_pid = os.getpid()
    callback_pids: list[int] = []
    report = benchmark.run_benchmarks(
        'Demo', root, timeout_seconds=10.0, workers=2,
        on_result=lambda _: callback_pids.append(os.getpid()))

    assert report['timeout_seconds'] == 10.0
    assert report['logic'] == 'QF_NRA'
    assert report['workers'] == 2
    assert callback_pids == [coordinator_pid, coordinator_pid]
    by_problem = {result['problem']: result for result in report['results']}
    first = by_problem['QF_NRA/20200101-Demo/problem1.smt2']
    second = by_problem['QF_NRA/20200101-Demo/problem2.smt2']
    assert first['status'] == 'error'
    assert first['phase'] == 'convert'
    assert first['error']['type'] == 'NotImplementedError'
    assert first['smtlib']['variables'] == {'Real': 2}
    assert first['atoms_before'] is None
    assert second['status'] == 'ok'
    assert second['phase'] == 'complete'
    assert second['smtlib']['variables'] == {'Real': 1}
    assert second['atoms_before'] == 2
    assert second['atoms_after'] == 1
    assert second['runtime_seconds'] >= second['simplification_runtime_seconds']
    captured = capsys.readouterr()
    progress = captured.err.splitlines()
    assert captured.out == ''
    assert len(progress) == 2
    assert {line.split('] ', 1)[1].split(': ', 1)[0] for line in progress} == {
        'QF_NRA/20200101-Demo/problem1.smt2',
        'QF_NRA/20200101-Demo/problem2.smt2'}


def test_worker_count_reserves_two_cores(
        monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(benchmark.os, 'process_cpu_count', lambda: 8)
    assert benchmark.benchmark_worker_count() == 6

    monkeypatch.setattr(benchmark.os, 'process_cpu_count', lambda: 2)
    assert benchmark.benchmark_worker_count() == 1

    monkeypatch.setattr(benchmark.os, 'process_cpu_count', lambda: None)
    assert benchmark.benchmark_worker_count() == 1


def test_benchmark_instances_run_concurrently(
        tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    context = benchmark.mp.get_context('fork')
    active = context.Value('i', 0)
    peak = context.Value('i', 0)

    def delayed_worker(problem: str, convert_only: bool,
                       connection: Any) -> None:
        benchmark._send(connection, {'kind': 'started'})
        with active.get_lock():
            active.value += 1
            peak.value = max(peak.value, active.value)
        sleep(0.1)
        with active.get_lock():
            active.value -= 1
        benchmark._send(connection, {
            'kind': 'result',
            'status': 'ok',
            'phase': 'convert',
            'runtime_seconds': 0.1,
            'simplification_runtime_seconds': None,
            'smtlib_variables': {},
            'atoms_before': 0,
            'atoms_after': None,
            'error': None,
        })
        connection.close()

    monkeypatch.setattr(benchmark, '_benchmark_worker', delayed_worker)
    instances = tuple(
        benchmark.Instance('Demo', tmp_path / f'{number}.smt2',
                           f'Demo/{number}.smt2')
        for number in range(4))

    results = list(benchmark.benchmark_instances(
        instances, 10.0, True, workers=2, context=context))

    assert len(results) == 4
    assert peak.value == 2


def test_parallel_timeout_does_not_stop_other_instances(
        tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    context = benchmark.mp.get_context('fork')

    def mixed_worker(problem: str, convert_only: bool,
                     connection: Any) -> None:
        benchmark._send(connection, {'kind': 'started'})
        benchmark._send(connection, {'kind': 'phase', 'phase': 'parse'})
        if problem.endswith('slow.smt2'):
            sleep(1.0)
            return
        benchmark._send(connection, {
            'kind': 'result',
            'status': 'ok',
            'phase': 'convert',
            'runtime_seconds': 0.01,
            'simplification_runtime_seconds': None,
            'smtlib_variables': {},
            'atoms_before': 0,
            'atoms_after': None,
            'error': None,
        })
        connection.close()

    monkeypatch.setattr(benchmark, '_benchmark_worker', mixed_worker)
    instances = tuple(
        benchmark.Instance('Demo', tmp_path / name, f'Demo/{name}')
        for name in ('slow.smt2', 'fast1.smt2', 'fast2.smt2'))

    results = list(benchmark.benchmark_instances(
        instances, 0.05, True, workers=2, context=context))
    by_problem = {result['problem']: result for result in results}

    assert by_problem['Demo/slow.smt2']['status'] == 'timeout'
    assert by_problem['Demo/slow.smt2']['phase'] == 'parse'
    assert by_problem['Demo/fast1.smt2']['status'] == 'ok'
    assert by_problem['Demo/fast2.smt2']['status'] == 'ok'


def test_timeout_is_structured(tmp_path: Path,
                               monkeypatch: pytest.MonkeyPatch) -> None:
    root = tmp_path / 'QF_NRA'
    _problem(root / 'Demo' / 'problem1.smt2', '''
(set-logic QF_NRA)
(declare-fun x () Real)
(assert (> x 0))
(check-sat)
''')
    family = benchmark.discover_families(root)[0]
    instance = benchmark.select_instances('Demo:1', [family], root)[0]
    get_context = benchmark.mp.get_context
    start_methods: list[str] = []

    def recording_get_context(method: str) -> Any:
        start_methods.append(method)
        return get_context(method)

    monkeypatch.setattr(benchmark.mp, 'get_context', recording_get_context)

    result = benchmark.benchmark_instance(instance, timeout_seconds=0.01)

    assert start_methods == ['fork']
    assert result['status'] == 'timeout'
    assert result['phase'] in {'startup', 'parse', 'convert', 'simplify'}
    assert 'variables' in result['smtlib']
    assert result['atoms_after'] is None
    assert result['error'] is None


def test_convert_only_stops_before_simplification(tmp_path: Path) -> None:
    root = tmp_path / 'QF_NRA'
    _problem(root / 'Demo' / 'problem1.smt2', '''
(set-logic QF_NRA)
(declare-fun x () Real)
(declare-fun flag () Bool)
(assert (and flag (not flag) (> x 0) (>= x 0)))
(check-sat)
''')

    report = benchmark.run_benchmarks(
        'Demo:1', root, timeout_seconds=10.0, convert_only=True, workers=1)

    assert report['convert_only'] is True
    assert report['logic'] == 'QF_NRA'
    assert report['workers'] == 1
    result = report['results'][0]
    assert result['status'] == 'ok'
    assert result['phase'] == 'convert'
    assert result['simplification_runtime_seconds'] is None
    assert result['smtlib']['variables'] == {'Bool': 1, 'Real': 1}
    assert result['atoms_before'] == 5
    assert result['atoms_after'] is None
    assert result['error'] is None


@pytest.mark.parametrize(('logic_arguments', 'logic'), [
    ([], 'QF_NRA'),
    (['--logic=QF_NRA'], 'QF_NRA'),
    (['--logic=QF_LRA'], 'QF_LRA'),
])
def test_main_streams_json_lines(
        monkeypatch: pytest.MonkeyPatch,
        capsys: pytest.CaptureFixture[str],
        logic_arguments: list[str], logic: str) -> None:
    metadata: dict[str, Any] = {
        'selector': 'Pine:1',
        'logic': logic,
        'timeout_seconds': 30.0,
        'convert_only': True,
        'workers': 6,
    }
    result = {
        'family': 'Pine',
        'problem': f'{logic}/20200911-Pine/problem1.smt2',
        'status': 'ok',
    }

    def fake_run(
            selector: str, *, convert_only: bool = False,
            logic: str = benchmark.DEFAULT_LOGIC,
            on_start: Any = None, on_result: Any = None) -> dict[str, Any]:
        current_metadata = {
            **metadata,
            'selector': selector,
            'logic': logic,
            'convert_only': convert_only,
        }
        current_result = {
            **result,
            'problem': f'{logic}/20200911-Pine/problem1.smt2',
        }
        on_start(current_metadata)
        on_result(current_result)
        return {**current_metadata, 'results': [current_result]}

    monkeypatch.setattr(benchmark, 'run_benchmarks', fake_run)

    assert benchmark.main([
        '--convert-only', *logic_arguments, 'Pine:1']) == 0
    captured = capsys.readouterr()
    lines = [json.loads(line) for line in captured.out.splitlines()]
    assert lines == [
        {'type': 'metadata', **metadata},
        {'type': 'result', **result},
    ]
    assert captured.err == ''


def test_main_reports_selection_error(monkeypatch: pytest.MonkeyPatch,
                                      capsys: pytest.CaptureFixture[str]) -> None:
    def fail(selector: str, *, convert_only: bool = False,
             logic: str = benchmark.DEFAULT_LOGIC,
             on_start: Any = None, on_result: Any = None) -> dict[str, Any]:
        raise benchmark.SelectionError(f'bad selector: {selector}')

    monkeypatch.setattr(benchmark, 'run_benchmarks', fail)

    assert benchmark.main(['bad']) == 2
    captured = capsys.readouterr()
    assert captured.out == ''
    assert 'bad selector: bad' in captured.err
