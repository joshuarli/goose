"""Verify a historical Goose bug on pinned pre-fix and fixed compilers."""

import argparse
from dataclasses import dataclass
import json
from pathlib import Path
import shutil
import sys
import tempfile

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
from fuzz import driver

BASE_REVISION = 'de24a15659248fce28a1d5bdc8a6375bea322a0a'


@dataclass(frozen=True)
class Calibration:
    lane: str
    seed: int
    sanitize: bool
    failure_class: str
    failure_stage: str
    fixed_revision: str


CALIBRATIONS = {
    'pr21': Calibration(
        'parse_flt', 0, False, 'output_mismatch', 'program',
        'c08f1d79b3aa3a85fd15e5aab728a30516a5a113'),
    'pr22': Calibration(
        'serialize', 0, True, 'sanitizer', 'program',
        '39b8d7a93458bc4da567275d6ca709eb814829e9'),
    'pr23': Calibration(
        'reference', 0, False, 'output_mismatch', 'program',
        'ba822e8e5048442b171dad151246f9ab7b6df13b'),
}


def matches_failure(observed, failure_class: str, stage: str) -> bool:
    return (observed is not None and observed.get('class') == failure_class
            and observed.get('stage') == stage)


def _write_json(path: Path, value) -> None:
    path.write_text(json.dumps(value, indent=2) + '\n', encoding='utf-8')


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('case', choices=sorted(CALIBRATIONS))
    parser.add_argument('--buggy-exe', type=Path, required=True)
    parser.add_argument('--fixed-exe', type=Path, required=True)
    parser.add_argument('--cc', default='clang-23')
    parser.add_argument('--timeout', type=float, default=10)
    parser.add_argument('--output-limit', type=int, default=65536)
    parser.add_argument('--output', type=Path, default=ROOT / 'build' / 'fuzz')
    args = parser.parse_args(argv)
    if min(args.timeout, args.output_limit) <= 0:
        parser.error('calibration bounds must be positive')
    case = CALIBRATIONS[args.case]
    buggy = args.buggy_exe.resolve()
    fixed = args.fixed_exe.resolve()
    cc_name = shutil.which(args.cc)
    if not buggy.is_file() or not fixed.is_file():
        raise ValueError('both calibration compiler binaries must exist')
    if cc_name is None:
        raise ValueError(f'C compiler is unavailable: {args.cc}')
    cc = Path(cc_name).resolve()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    campaign = Path(tempfile.mkdtemp(prefix=f'calibrate-{args.case}-', dir=output))
    program = driver.MODELS[case.lane].generate(case.seed)
    reports = {}
    matrix = driver.FULL_MATRIX
    for name, executable in (('buggy', buggy), ('fixed', fixed)):
        with tempfile.TemporaryDirectory(prefix=f'{name}-work-', dir=campaign) as temporary:
            work = Path(temporary)
            report = driver.check(
                program, executable, cc, matrix, work, args.timeout,
                args.output_limit, case.sanitize)
            reports[name] = report
            artifact = driver.save_artifact(
                campaign / name, program, report,
                {'goose': str(executable),
                 'goose_sha256': driver.binary_hash(executable),
                 'cc': str(cc), 'cc_sha256': driver.binary_hash(cc)})
            driver.preserve(work, artifact)
    passed = (matches_failure(reports['buggy']['failure'], case.failure_class, case.failure_stage)
              and reports['fixed']['failure'] is None)
    summary = {
        'case': args.case,
        'lane': case.lane,
        'seed': case.seed,
        'base_revision': BASE_REVISION,
        'fixed_revision': case.fixed_revision,
        'sanitize': case.sanitize,
        'expected_buggy_failure': {
            'class': case.failure_class, 'stage': case.failure_stage},
        'buggy_failure': reports['buggy']['failure'],
        'fixed_failure': reports['fixed']['failure'],
        'passed': passed,
    }
    _write_json(campaign / 'summary.json', summary)
    print(json.dumps({'campaign': str(campaign), **summary}))
    return int(not passed)


if __name__ == '__main__':
    try:
        sys.exit(main())
    except (OSError, ValueError, RuntimeError) as error:
        print(f'calibration: {error}', file=sys.stderr)
        sys.exit(2)
