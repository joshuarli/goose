"""Run one native libFuzzer target with isolated corpus and measured reach."""

import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import sys
import tempfile

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
from fuzz.process import run

ARTIFACT_PREFIXES = ('crash-', 'leak-', 'oom-', 'slow-unit-', 'timeout-')
PROGRESS = re.compile(
    rb'#\d+\s+\w+\s+cov: (\d+) ft: (\d+) corp: (\d+)/(\d+)([KMG]?)b')
STATISTIC = re.compile(rb'^stat::([^:]+):\s+(\d+)\s*$', re.MULTILINE)
PIPELINE = re.compile(rb'^goose_pipeline_metrics (.+)$', re.MULTILINE)


def parse_statistics(output: bytes) -> dict:
    """Extract stable libFuzzer and Goose reach metrics from stderr."""
    summary = {}
    progress = PROGRESS.findall(output)
    if progress:
        coverage, features, units, size, unit = progress[-1]
        scale = {b'': 1, b'K': 1024, b'M': 1024 ** 2, b'G': 1024 ** 3}[unit]
        summary.update({
            'coverage_edges': int(coverage),
            'coverage_features': int(features),
            'corpus_units': int(units),
            'corpus_bytes': int(size) * scale,
        })
    names = {
        b'number_of_executed_units': 'executed_units',
        b'average_exec_per_sec': 'executions_per_second',
        b'new_units_added': 'new_units',
        b'peak_rss_mb': 'peak_rss_mb',
    }
    for name, value in STATISTIC.findall(output):
        if name in names:
            summary[names[name]] = int(value)
    metrics = PIPELINE.findall(output)
    if metrics:
        pipeline = {}
        for item in metrics[-1].split():
            name, value = item.split(b'=', 1)
            pipeline[name.decode('ascii')] = int(value)
        inputs = pipeline.get('inputs', 0)
        pipeline['acceptance_rate'] = pipeline.get('accepted', 0) / inputs if inputs else 0.0
        summary['pipeline'] = pipeline
    return summary


def artifact_fingerprints(directory: Path) -> list[dict]:
    findings = []
    for path in sorted(directory.iterdir()):
        if path.is_file() and path.name.startswith(ARTIFACT_PREFIXES):
            findings.append({
                'name': path.name,
                'sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
                'bytes': path.stat().st_size,
            })
    return findings


def _copy_seeds(sources: list[Path], destination: Path) -> int:
    copied = 0
    for source in sources:
        if not source.is_dir():
            raise ValueError(f'seed directory does not exist: {source}')
        for path in sorted(source.rglob('*')):
            if not path.is_file():
                continue
            digest = hashlib.sha256(path.read_bytes()).hexdigest()[:12]
            target = destination / f'{digest}-{path.name}'
            if not target.exists():
                shutil.copyfile(path, target)
                copied += 1
    if not copied:
        raise ValueError('native campaign has no seed files')
    return copied


def _write_json(path: Path, value) -> None:
    path.write_text(json.dumps(value, indent=2) + '\n', encoding='utf-8')


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--target', choices=('parser', 'pipeline'), required=True)
    parser.add_argument('--exe', type=Path, required=True)
    parser.add_argument('--seed-dir', type=Path, action='append')
    parser.add_argument('--output', type=Path, default=ROOT / 'build' / 'fuzz')
    parser.add_argument('--duration', type=int, default=300)
    parser.add_argument('--timeout', type=int, default=10)
    parser.add_argument('--max-len', type=int, default=4096)
    parser.add_argument('--seed', type=int)
    parser.add_argument('--output-limit', type=int, default=8 * 1024 * 1024)
    args = parser.parse_args(argv)
    if min(args.duration, args.timeout, args.max_len, args.output_limit) <= 0:
        parser.error('campaign bounds must be positive')
    executable = args.exe.resolve()
    if not executable.is_file():
        raise ValueError(f'native fuzz target does not exist: {executable}')
    sources = args.seed_dir
    if sources is None:
        sources = [ROOT / ('test/syntax' if args.target == 'parser' else 'fuzz/native/corpus')]
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    campaign = Path(tempfile.mkdtemp(prefix=f'native-{args.target}-', dir=output))
    corpus = campaign / 'corpus'
    artifacts = campaign / 'artifacts'
    corpus.mkdir()
    artifacts.mkdir()
    seed_count = _copy_seeds([source.resolve() for source in sources], corpus)
    command = [
        str(executable), str(corpus),
        f'-max_total_time={args.duration}', f'-timeout={args.timeout}',
        f'-max_len={args.max_len}', f'-artifact_prefix={artifacts}/',
        '-print_final_stats=1',
    ]
    if args.seed is not None:
        if not 0 <= args.seed < 1 << 32:
            raise ValueError('libFuzzer seed must fit unsigned 32 bits')
        command.append(f'-seed={args.seed}')
    if args.target == 'pipeline':
        command.append(f'-dict={ROOT / "fuzz/native/goose.dict"}')
    result = run(
        command, ROOT, args.duration + args.timeout + 15, args.output_limit,
        env={'LSAN_OPTIONS': 'detect_leaks=0'})
    combined = result.stdout + result.stderr
    summary = {
        'target': args.target,
        'seed_files': seed_count,
        'duration_seconds': args.duration,
        'timeout_seconds': args.timeout,
        'max_input_bytes': args.max_len,
        'binary': str(executable),
        'binary_sha256': hashlib.sha256(executable.read_bytes()).hexdigest(),
        'command': command,
        'result': result.to_dict(),
        'statistics': parse_statistics(combined),
        'findings': artifact_fingerprints(artifacts),
    }
    _write_json(campaign / 'summary.json', summary)
    print(json.dumps({
        'campaign': str(campaign),
        'statistics': summary['statistics'],
        'findings': summary['findings'],
    }))
    return int(bool(summary['findings']) or result.limit is not None or result.returncode != 0)


if __name__ == '__main__':
    try:
        sys.exit(main())
    except (OSError, ValueError, RuntimeError) as error:
        print(f'native fuzz: {error}', file=sys.stderr)
        sys.exit(2)
