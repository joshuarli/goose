#!/usr/bin/env python3
"""Compare parser time and peak RSS using two identically built Goose compilers.

Linux-only: GNU time records peak RSS and taskset pins each compiler run. Inputs
and JSON samples remain in the output directory so measurements can be repeated.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import resource
import signal
import statistics
import subprocess
import time


CORPUS = (
    'samples/01_tour.goose', 'samples/12_huffman.goose',
    'samples/14_bst.goose', 'samples/17_calc.goose',
    'samples/18_json.goose', 'samples/19_vm.goose',
    'bench/goose/interp.goose', 'bench/goose/lru.goose',
    'bench/goose/records_var.goose', 'bench/goose/respond.goose',
    'bench/goose/scene.goose', 'bench/goose/sexp.goose',
)


PATHOLOGICAL_SOURCE = "// error: expected ']' in indexing, found 'i'\n// Each `<` can begin either a comparison or generic arguments. Failed\n// speculative parses at an inner `<` must not be repeated from every outer one.\nfn main() {\n    let x = [a<T[a<T[a<T[a<T[a<T[a<T[a<T[a<T[a<T[a<T[a<T[a<T[a<T[a<T[a<T[a<T[a<T[a<T[a<T[a<T i\n"

def command_output(*command):
    return subprocess.check_output(command, text=True).strip()


def generated_source(kind, sites):
    lines = ['fn identity<T>(value: T) -> T { value }'] if kind == 'generics' else []
    for function in range((sites + 199) // 200):
        lines.append(f'fn workload_{function}(left: i64, right: i64) {{')
        for index in range(min(200, sites - function * 200)):
            expression = 'left < right' if kind == 'comparisons' else 'identity<i64>(left)'
            lines.append(f'    let result_{index} = {expression};')
        lines.append('}')
    lines.append('fn main() {}')
    return '\n'.join(lines) + '\n'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base-exe', type=Path, required=True)
    parser.add_argument('--head-exe', type=Path, required=True)
    parser.add_argument('--source-root', type=Path, required=True)
    parser.add_argument('--output-dir', type=Path, required=True)
    parser.add_argument('--base-revision', required=True)
    parser.add_argument('--head-revision', required=True)
    parser.add_argument('--build-flags', required=True)
    parser.add_argument('--compiler', default='c++', help='compiler used to build both executables')
    parser.add_argument('--cpu', type=int, default=min(os.sched_getaffinity(0)))
    parser.add_argument('--sites', type=int, default=50000)
    parser.add_argument('--rounds', type=int, default=9)
    parser.add_argument('--repeats', type=int, default=5)
    args = parser.parse_args()
    if args.sites < 1 or args.rounds < 3 or args.repeats < 1:
        parser.error('sites/repeats must be positive and rounds at least three')
    root = args.source_root.resolve()
    output = args.output_dir.resolve()
    output.mkdir(parents=True, exist_ok=True)
    executables = {'base': args.base_exe.resolve(), 'head': args.head_exe.resolve()}
    workloads = {}
    for kind in ('comparisons', 'generics'):
        path = output / f'{kind}.goose'
        path.write_text(generated_source(kind, args.sites), encoding='utf-8')
        workloads[kind] = [path] * args.repeats
    workloads['corpus'] = [root / path for path in CORPUS] * (args.repeats * 4)
    pathological = output / 'pathological.goose'
    pathological.write_text(PATHOLOGICAL_SOURCE, encoding='utf-8')
    workloads['pathological'] = [pathological]

    def measure(version, paths, expected_status):
        rss_file = output / 'peak-rss.txt'
        command = [
            'taskset', '-c', str(args.cpu), '/usr/bin/time', '-f', '%M',
            '-o', str(rss_file), str(executables[version]),
            '--stdlib', str(root / 'stdlib'),
            *(['--multi-test'] if expected_status == 0 else []), '--parse',
            *map(str, paths),
        ]
        start = time.perf_counter()
        result = subprocess.run(command, capture_output=True, timeout=120)
        elapsed_ms = (time.perf_counter() - start) * 1000
        if result.returncode != expected_status:
            raise RuntimeError(f'{version}: {result.stderr.decode()}\n{result.stdout.decode()}')
        if expected_status == 1 and b"expected ']' in indexing, found 'i'" not in result.stderr:
            raise RuntimeError(f'{version}: unexpected parser diagnostic: {result.stderr.decode()}')
        return {'ms': elapsed_ms, 'rss_kib': int(rss_file.read_text().splitlines()[-1])}, result.stdout

    libc = subprocess.run(['ldd', '--version'], capture_output=True, text=True)
    if libc.returncode not in (0, 1) or not ('musl' in libc.stdout + libc.stderr or 'GLIBC' in libc.stdout):
        raise RuntimeError(f'cannot identify libc: {libc.stdout}{libc.stderr}')
    report = {
        'platform': platform.platform(),
        'kernel': command_output('uname', '-srvm'),
        'cpu': command_output('sh', '-c', "lscpu | sed -n 's/^Model name: *//p'"),
        'compiler': command_output(args.compiler, '--version').splitlines()[0],
        'libc': (libc.stdout + libc.stderr).splitlines()[:2],
        'base_revision': args.base_revision, 'head_revision': args.head_revision,
        'build_flags': args.build_flags, 'cpu_affinity': args.cpu,
        'rounds': args.rounds, 'warmup_pairs': 2, 'sites_per_generated_file': args.sites,
        'generated_file_repeats': args.repeats,
        'corpus': list(CORPUS), 'corpus_repeats': args.repeats * 4,
        'pathological_fixture': 'test/errors/generic_comparison_backtrack.goose (rejected patch)',
        'command': ['--stdlib', str(root / 'stdlib'), '--multi-test', '--parse'],
        'pathological_command': ['--stdlib', str(root / 'stdlib'), '--parse'],
        'workloads': {},
    }
    print(json.dumps({key: report[key] for key in
                      ('compiler', 'libc', 'kernel', 'cpu', 'cpu_affinity', 'build_flags')},
                     indent=2), flush=True)
    # A CPU budget makes the exponential retry failure observable independently
    # of wall-clock contention. The deeper malformed input remains small.
    budget_fixture = output / 'cpu-budget.goose'
    budget_fixture.write_text('fn main() {\n    let x = [' + 'a<T[' * 23 + 'a<T i\n')

    def limit_cpu():
        resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
        resource.setrlimit(resource.RLIMIT_CPU, (1, 2))

    for version, executable in executables.items():
        result = subprocess.run(['taskset', '-c', str(args.cpu), executable,
                                 '--parse', budget_fixture], capture_output=True,
                                preexec_fn=limit_cpu, timeout=10)
        expected_status = -signal.SIGXCPU if version == 'base' else 1
        if result.returncode != expected_status:
            raise RuntimeError(f'{version}: CPU-budget regression returned {result.returncode}: {result.stderr.decode()}')
        if version == 'head' and b"expected ']' in indexing, found 'i'" not in result.stderr:
            raise RuntimeError(f'head: unexpected CPU-budget diagnostic: {result.stderr.decode()}')
    report['cpu_budget_regression'] = {'nested_prefixes': 24, 'cpu_seconds': 1,
                                      'base_status': -signal.SIGXCPU, 'head_status': 1}
    print('CPU-budget regression: base exceeds 1 CPU second; head returns the expected diagnostic.', flush=True)
    # Validate generated workloads beyond parsing once; timing isolates the
    # parser and name resolver rather than specialization and C generation.
    for version, executable in executables.items():
        for kind in ('comparisons', 'generics'):
            subprocess.run([executable, '--stdlib', root / 'stdlib', '--check',
                            output / f'{kind}.goose'], check=True, capture_output=True)

    for name, paths in workloads.items():
        expected_output = None
        samples = {'base': [], 'head': []}
        for round_index in range(args.rounds + 2):
            order = ('base', 'head') if round_index % 2 == 0 else ('head', 'base')
            for version in order:
                sample, stdout = measure(version, paths, 1 if name == 'pathological' else 0)
                if expected_output is None:
                    expected_output = stdout
                elif stdout != expected_output:
                    raise RuntimeError(f'compiler outputs differ for {name}')
                if round_index >= 2:
                    samples[version].append(sample)
        summary = {}
        for version in ('base', 'head'):
            times = [sample['ms'] for sample in samples[version]]
            summary[version] = {
                'median_ms': statistics.median(times),
                'min_ms': min(times), 'max_ms': max(times),
                'median_rss_kib': statistics.median(sample['rss_kib'] for sample in samples[version]),
            }
        summary['time_change_percent'] = (
            summary['head']['median_ms'] / summary['base']['median_ms'] - 1
        ) * 100
        report['workloads'][name] = {
            'input_bytes_per_invocation': sum(path.stat().st_size for path in paths),
            'input_sha256': {str(path.relative_to(root) if path.is_relative_to(root) else path.name):
                             hashlib.sha256(path.read_bytes()).hexdigest() for path in dict.fromkeys(paths)},
            'summary': summary, 'samples': samples,
        }
        (output / 'results.json').write_text(json.dumps(report, indent=2) + '\n')
        print(name, json.dumps(summary), flush=True)


if __name__ == '__main__':
    main()
