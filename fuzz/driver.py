"""Bounded differential compiler correctness campaigns for generated programs."""

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import secrets
import shlex
import shutil
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
from fuzz import aggregate_model
from fuzz import model as scalar_model
from fuzz import numeric_model
from fuzz import order_model
from fuzz import parse_flt_model
from fuzz import reference_model
from fuzz import resize_model
from fuzz import serialize_model
from fuzz import trap_model
from fuzz.expectation import RejectExpectation
from fuzz.process import run
from scripts.toolchain import find_goose, sanitizer_failure, SANITIZER_FLAGS

FULL_MATRIX = [(0, 0), (0, 2), (2, 0), (2, 2)]
SMOKE_MATRIX = [(0, 0), (2, 2)]
MODELS = {'aggregate': aggregate_model, 'numeric': numeric_model, 'order': order_model,
          'parse_flt': parse_flt_model, 'reference': reference_model,
          'resize': resize_model, 'scalar': scalar_model, 'serialize': serialize_model,
          'trap': trap_model}


def model_for_program(program):
    for lane, model in MODELS.items():
        if isinstance(program, model.Program):
            return lane, model
    raise ValueError('unknown fuzz program type')


def load_recipe(recipe):
    if type(recipe) is not dict or recipe.get('lane') not in MODELS:
        raise ValueError('unknown fuzz lane')
    model = MODELS[recipe['lane']]
    return model, model.Program.from_dict(recipe)


def classify(stage, result, expected=None):
    diagnostic = (result.stdout + result.stderr).decode('utf-8', errors='replace')
    if sanitizer_failure(diagnostic):
        return 'sanitizer'
    if result.limit:
        return 'timeout' if result.limit == 'timeout' else 'output_limit'
    if isinstance(expected, RejectExpectation):
        if stage != 'goose':
            raise ValueError('MustReject is decided by the Goose compiler')
        if result.returncode < 0:
            return 'compiler_crash'
        if not result.returncode:
            return 'false_acceptance'
        if not all(fragment in diagnostic for fragment in expected.diagnostic_contains):
            return 'rejection_diagnostic'
        return None
    if stage == 'goose' and result.returncode:
        return 'compiler_crash' if result.returncode < 0 else 'false_rejection'
    if stage == 'c' and result.returncode:
        return 'c_compile_failure'
    if stage == 'program':
        if isinstance(expected, trap_model.TrapExpectation):
            if not result.returncode:
                return 'missing_trap'
            if result.stdout != expected.stdout_prefix:
                return 'output_mismatch'
            stderr = result.stderr.decode('utf-8', errors='replace')
            if not all(fragment in stderr for fragment in expected.stderr_contains):
                return 'trap_diagnostic'
        elif result.returncode:
            return 'unexpected_trap'
        elif result.stdout != expected or result.stderr:
            return 'output_mismatch'
    return None


def describe_expectation(expected):
    if isinstance(expected, RejectExpectation):
        return {'kind': 'MustReject',
                'diagnostic_contains': list(expected.diagnostic_contains)}
    if isinstance(expected, trap_model.TrapExpectation):
        return {'kind': 'MustTrap', 'stdout_prefix': expected.stdout_prefix.decode('ascii'),
                'stderr_contains': list(expected.stderr_contains)}
    return {'kind': 'MustCompileAndReturn', 'stdout': expected.decode('ascii')}


def check(program, exe, cc, matrix, work, timeout=10, output_limit=65536, sanitize=False,
          deadline=None):
    lane, model = model_for_program(program)
    work.mkdir(parents=True, exist_ok=True)
    for previous in work.iterdir():
        if previous.is_file():
            previous.unlink()
    source = work / 'source.goose'
    source.write_text(model.render(program), encoding='utf-8')
    expected = model.evaluate(program)
    report = {'failure': None, 'results': [], 'expected': describe_expectation(expected),
              'lane': lane, 'matrix': matrix, 'sanitize': sanitize}
    by_goose_opt = {}
    for goose_opt, c_opt in matrix:
        by_goose_opt.setdefault(goose_opt, []).append(c_opt)
    for goose_opt, c_opts in by_goose_opt.items():
        cfile = work / f'goose-O{goose_opt}.c'
        command = [str(exe), f'-O{goose_opt}', '--standalone', '-o', str(cfile), str(source)]
        budget = timeout if deadline is None else min(timeout, max(0.001, deadline - time.monotonic()))
        result = run(command, work, budget, output_limit)
        report['results'].append({'stage': 'goose', 'goose_opt': goose_opt,
                                  'c_opt': None, **result.to_dict()})
        failure = classify('goose', result, expected)
        if failure:
            report['failure'] = {'class': failure, 'stage': 'goose',
                                 'goose_opt': goose_opt, 'c_opt': None}
            return report
        if isinstance(expected, RejectExpectation):
            continue
        for c_opt in c_opts:
            binary = work / f'program-g{goose_opt}-c{c_opt}'
            commands = [
                ('c', [str(cc), f'-O{c_opt}', '-Werror=implicit-function-declaration',
                       *(SANITIZER_FLAGS if sanitize else ()), str(cfile), '-o', str(binary),
                       '-pthread', '-lm']),
                ('program', [str(binary)])]
            for stage, command in commands:
                budget = timeout if deadline is None else min(timeout, max(0.001, deadline - time.monotonic()))
                environment = {'LSAN_OPTIONS': 'detect_leaks=0'} if sanitize and stage == 'program' else None
                result = run(command, work, budget, output_limit, env=environment)
                report['results'].append({'stage': stage, 'goose_opt': goose_opt,
                                          'c_opt': c_opt, **result.to_dict()})
                failure = classify(stage, result, expected)
                if failure:
                    report['failure'] = {'class': failure, 'stage': stage,
                                         'goose_opt': goose_opt, 'c_opt': c_opt}
                    return report
    return report


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n', encoding='utf-8')


def save_artifact(directory, program, report, identity):
    _, model = model_for_program(program)
    # Never replace existing evidence, even if two campaigns use the same seed.
    directory.mkdir(parents=True, exist_ok=False)
    write_json(directory / 'recipe.json', program.to_dict())
    (directory / 'source.goose').write_text(model.render(program), encoding='utf-8')
    write_json(directory / 'report.json', report)
    write_json(directory / 'identity.json', identity)
    replay = ['python3', 'fuzz/driver.py', 'replay', str(directory.resolve()),
              '--exe', identity['goose'], '--cc', identity['cc']]
    (directory / 'replay.txt').write_text(shlex.join(replay) + '\n', encoding='utf-8')
    return directory


def binary_hash(path):
    with path.open('rb') as source:
        return hashlib.file_digest(source, 'sha256').hexdigest()


def identity(exe, cc, timeout, output_limit):
    def capture(command):
        result = run(command, ROOT, timeout, output_limit)
        if result.limit or result.returncode:
            raise RuntimeError(f'preflight failed: {command}: {result.to_dict()}')
        return result.stdout.decode('utf-8', errors='replace')
    diff = capture(['git', 'diff', 'HEAD', '--binary'])
    status = capture(['git', 'status', '--porcelain'])
    # Untracked files are hashed too: a binary may have been built from them.
    untracked = capture(['git', 'ls-files', '--others', '--exclude-standard', '-z'])
    return {'goose': str(exe), 'goose_sha256': binary_hash(exe),
            'cc': str(cc), 'cc_sha256': binary_hash(cc),
            'cc_version': capture([str(cc), '--version']),
            'revision': capture(['git', 'rev-parse', 'HEAD']).strip(),
            'dirty_status': status, 'tracked_diff': diff,
            'untracked_hashes': {name: binary_hash(ROOT / name)
                                 for name in untracked.split('\0') if name},
            'timeout_seconds': timeout, 'output_limit_bytes': output_limit}


def resolve_tools(args):
    if not sys.platform.startswith('linux'):
        raise ValueError('this slice supports Linux process cleanup and native C toolchains')
    exe = Path(find_goose(args.exe)).resolve()
    candidate = shutil.which(args.cc)
    if not candidate:
        raise ValueError(f'requested C compiler is unavailable: {args.cc}')
    cc = Path(candidate).resolve()
    if not exe.is_file():
        raise ValueError(f'Goose compiler is unavailable: {exe}')
    return exe, cc


def preserve(work, artifact):
    for cfile in work.glob('*.c'):
        shutil.copyfile(cfile, artifact / cfile.name)


def reduce_case(program, target, exe, cc, matrix, work, seconds, timeout, output_limit, sanitize):
    _, model = model_for_program(program)
    deadline = time.monotonic() + seconds
    attempts = 0
    best = program
    while time.monotonic() < deadline:
        for candidate in model.reductions(best):
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                return best, attempts
            report = check(candidate, exe, cc, matrix, work,
                           min(timeout, remaining), output_limit, sanitize, deadline=deadline)
            attempts += 1
            if report['failure'] == target:
                best = candidate
                break
        else:
            break
    return best, attempts


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('operation', choices=['doctor', 'smoke', 'run', 'replay', 'reduce'])
    parser.add_argument('artifact', nargs='?', type=Path)
    parser.add_argument('--exe')
    parser.add_argument('--cc', default='clang')
    parser.add_argument('--seed', type=int)
    parser.add_argument('--count', type=int)
    parser.add_argument('--duration', type=float, default=60)
    parser.add_argument('--timeout', type=float, default=10)
    parser.add_argument('--output-limit', type=int, default=65536)
    parser.add_argument('--reduction-seconds', type=float, default=30)
    parser.add_argument('--output', type=Path, default=ROOT / 'build' / 'fuzz')
    parser.add_argument('--matrix', choices=['smoke', 'full'])
    parser.add_argument('--lane', choices=sorted(MODELS), default='scalar')
    parser.add_argument('--sanitize', action='store_true', help='instrument generated C and embedded runtime')
    args = parser.parse_args(argv)
    if min(args.duration, args.timeout, args.reduction_seconds, args.output_limit) <= 0:
        parser.error('budgets must be positive')
    if args.count is not None and args.count < 1:
        parser.error('--count must be positive')
    if (args.operation in ('replay', 'reduce')) != (args.artifact is not None):
        parser.error('replay and reduce require an artifact; other operations do not take one')
    exe, cc = resolve_tools(args)
    args.output = args.output.resolve()
    args.output.mkdir(parents=True, exist_ok=True)
    # A unique directory preserves both successful reports and prior failures.
    campaign = Path(tempfile.mkdtemp(prefix=args.operation + '-', dir=args.output))
    build = identity(exe, cc, args.timeout, args.output_limit)
    write_json(campaign / 'identity.json', build)
    matrix = SMOKE_MATRIX if args.matrix == 'smoke' or (args.matrix is None and args.operation == 'smoke') else FULL_MATRIX
    with tempfile.TemporaryDirectory(prefix='work-', dir=campaign) as temporary:
        work = Path(temporary)
        if args.operation in ('replay', 'reduce'):
            model, program = load_recipe(json.loads((args.artifact / 'recipe.json').read_text()))
            original = json.loads((args.artifact / 'report.json').read_text())
            if args.matrix is None:
                matrix = [tuple(pair) for pair in original['matrix']]
            sanitize = args.sanitize or original['sanitize']
            report = check(program, exe, cc, matrix, work, args.timeout, args.output_limit, sanitize)
            artifact = save_artifact(campaign / 'original', program, report, build)
            preserve(work, artifact)
            if args.operation == 'reduce':
                if not report['failure'] or report['failure'] != original['failure']:
                    raise ValueError('saved failure did not reproduce with the same class, stage and configuration')
                confirmation = check(program, exe, cc, matrix, work, args.timeout, args.output_limit, sanitize)
                if confirmation['failure'] != report['failure']:
                    raise ValueError('failure is flaky; original evidence preserved')
                best, attempts = reduce_case(program, report['failure'], exe, cc, matrix, work,
                                             args.reduction_seconds, args.timeout, args.output_limit, sanitize)
                reduced = check(best, exe, cc, matrix, work, args.timeout, args.output_limit, sanitize)
                if reduced['failure'] != report['failure']:
                    raise ValueError('reduced failure did not reconfirm; original evidence preserved')
                reduced['reduction_attempts'] = attempts
                minimized = save_artifact(campaign / 'minimized', best, reduced, build)
                preserve(work, minimized)
                print(f'minimized: {minimized} ({attempts} attempts)')
            else:
                print(json.dumps({'failure': report['failure'], 'artifact': str(artifact)}))
            return int(report['failure'] is not None) if args.operation == 'replay' else 0
        seed = args.seed if args.seed is not None else secrets.randbits(64)
        count = args.count if args.count is not None else (1 if args.operation == 'doctor' else 8 if args.operation == 'smoke' else 100)
        if seed < 0 or seed + count > 1 << 64:
            raise ValueError('the seed range must fit in unsigned 64 bits')
        if args.operation == 'doctor':
            matrix = [(0, 0)]
        print(f'seed={seed} matrix={matrix} cc={cc} output={campaign}', flush=True)
        started = time.monotonic()
        stages = Counter()
        completed = attempted = 0
        failure = None
        for index in range(count):
            if time.monotonic() - started >= args.duration:
                break
            case_seed = seed + index
            program = MODELS[args.lane].generate(case_seed)
            report = check(program, exe, cc, matrix, work,
                           args.timeout, args.output_limit, args.sanitize)
            report['seed'] = case_seed
            attempted += 1
            stages.update(item['stage'] for item in report['results'])
            if report['failure']:
                failure = save_artifact(campaign / f'failure-{case_seed}', program, report, build)
                preserve(work, failure)
                print(f'finding: {report["failure"]} artifact={failure}', flush=True)
                break
            completed += 1
        elapsed = time.monotonic() - started
        summary = {'seed': seed, 'lane': args.lane, 'attempted_cases': attempted, 'completed_cases': completed,
                   'matrix': matrix, 'sanitize': args.sanitize, 'stage_invocations': dict(stages),
                   'seconds': elapsed, 'cases_per_second': completed / elapsed,
                   'failure': str(failure) if failure else None}
        write_json(campaign / 'summary.json', summary)
        print(json.dumps(summary))
        return int(failure is not None or completed == 0)


if __name__ == '__main__':
    try:
        sys.exit(main())
    except (ValueError, RuntimeError, OSError) as error:
        print(f'fuzz: {error}', file=sys.stderr)
        sys.exit(2)
