import json
from pathlib import Path
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

    report = benchmark.run_benchmarks('Demo', root, timeout_seconds=10.0)

    assert report['timeout_seconds'] == 10.0
    first, second = report['results']
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
    assert progress[0].startswith(
        '[1/2] 20200101-Demo/problem1.smt2: error (convert, ')
    assert progress[1].startswith(
        '[2/2] 20200101-Demo/problem2.smt2: ok (complete, ')


def test_timeout_is_structured(tmp_path: Path) -> None:
    root = tmp_path / 'QF_NRA'
    _problem(root / 'Demo' / 'problem1.smt2', '''
(set-logic QF_NRA)
(declare-fun x () Real)
(assert (> x 0))
(check-sat)
''')
    family = benchmark.discover_families(root)[0]
    instance = benchmark.select_instances('Demo:1', [family], root)[0]

    result = benchmark.benchmark_instance(instance, timeout_seconds=0.01)

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
        'Demo:1', root, timeout_seconds=10.0, convert_only=True)

    assert report['convert_only'] is True
    result = report['results'][0]
    assert result['status'] == 'ok'
    assert result['phase'] == 'convert'
    assert result['simplification_runtime_seconds'] is None
    assert result['smtlib']['variables'] == {'Bool': 1, 'Real': 1}
    assert result['atoms_before'] == 5
    assert result['atoms_after'] is None
    assert result['error'] is None


def test_main_streams_json_lines(monkeypatch: pytest.MonkeyPatch,
                                 capsys: pytest.CaptureFixture[str]) -> None:
    metadata: dict[str, Any] = {
        'selector': 'Pine:1',
        'timeout_seconds': 30.0,
        'convert_only': True,
    }
    result = {
        'family': 'Pine',
        'problem': '20200911-Pine/problem1.smt2',
        'status': 'ok',
    }

    def fake_run(
            selector: str, *, convert_only: bool = False,
            on_start: Any = None, on_result: Any = None) -> dict[str, Any]:
        current_metadata = {
            **metadata,
            'selector': selector,
            'convert_only': convert_only,
        }
        on_start(current_metadata)
        on_result(result)
        return {**current_metadata, 'results': [result]}

    monkeypatch.setattr(benchmark, 'run_benchmarks', fake_run)

    assert benchmark.main(['--convert-only', 'Pine:1']) == 0
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
             on_start: Any = None, on_result: Any = None) -> dict[str, Any]:
        raise benchmark.SelectionError(f'bad selector: {selector}')

    monkeypatch.setattr(benchmark, 'run_benchmarks', fail)

    assert benchmark.main(['bad']) == 2
    captured = capsys.readouterr()
    assert captured.out == ''
    assert 'bad selector: bad' in captured.err
