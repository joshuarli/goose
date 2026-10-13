#!/usr/bin/env python3
"""Qualify a units-built goose-lint beside a sibling Goose install.

  python test/scale/lint_units.py --goose GOOSE --baseline GOOSE

The candidate companion is built with `goose build --units`. The default run
compares it with the baseline single-file companion using lint_parity.py and
runs the existing linter suite against the sibling install. `--subset` checks
representative text/JSONL results without running those broad checks.
"""

import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[2]
WORK_ROOT = (ROOT / ".work").resolve()
LINT_SOURCE = ROOT / "tools" / "lint" / "main.goose"
STDLIB = ROOT / "stdlib"


def companion_for(goose):
    return goose.with_name("goose-lint.exe" if os.name == "nt" else "goose-lint")


def run(command, *, env, cwd=ROOT):
    return subprocess.run([str(part) for part in command], cwd=cwd, env=env,
                          text=True, capture_output=True)


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def lint_result(goose, source, options, env):
    return run([goose, "lint", source, "--stdlib", STDLIB, *options], env=env)


def check_subset(units_goose, baseline_goose, work):
    sources = [ROOT / "test/lint/rules.goose",
               ROOT / "test/lint/suppressions.goose",
               ROOT / "test/lint/fanout_root_depth.goose"]
    option_sets = [[], ["--format", "jsonl"], ["--format", "jsonl", "--group", "correctness"],
                   ["--format", "jsonl", "--enable", "specialization_fanout"]]
    envs = {}
    for name in ("units", "baseline"):
        envs[name] = os.environ.copy()
        envs[name]["GOOSE_HOME"] = str(work / f"{name}-home")
        envs[name]["TMPDIR"] = str(WORK_ROOT / "tmp")
    compared = 0
    for source in sources:
        for options in option_sets:
            units = lint_result(units_goose, source, options, envs["units"])
            baseline = lint_result(baseline_goose, source, options, envs["baseline"])
            if (units.returncode, units.stdout, units.stderr) != (
                    baseline.returncode, baseline.stdout, baseline.stderr):
                label = " ".join(options) or "default text"
                raise RuntimeError(
                    f"units companion differs from baseline for {source.relative_to(ROOT)} ({label})\n"
                    f"units exit {units.returncode}:\n{units.stdout}{units.stderr}\n"
                    f"baseline exit {baseline.returncode}:\n{baseline.stdout}{baseline.stderr}")
            compared += 1
    print(json.dumps({"kind": "lint_units_subset", "identical_runs": compared}, sort_keys=True))


def check_full(units_goose, baseline_goose, work, env):
    parity = run([sys.executable, ROOT / "test/scale/lint_parity.py",
                  "--goose", units_goose, "--baseline", baseline_goose], env=env)
    sys.stdout.write(parity.stdout)
    sys.stderr.write(parity.stderr)
    require(parity.returncode == 0, f"linter parity failed with exit {parity.returncode}")

    suite = run([sys.executable, ROOT / "test/lint/run_tests.py", "--goose", units_goose], env=env)
    sys.stdout.write(suite.stdout)
    sys.stderr.write(suite.stderr)
    require(suite.returncode == 0, f"existing linter suite failed with exit {suite.returncode}")


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--goose", type=Path, required=True, help="candidate Goose compiler")
    parser.add_argument("--baseline", type=Path, required=True,
                        help="compiler whose adjacent single-file goose-lint is the reference")
    parser.add_argument("--work", type=Path, help="scratch directory under .work (default: .work/lint_units)")
    parser.add_argument("--subset", action="store_true",
                        help="compare representative output without the full parity and linter suite")
    args = parser.parse_args()

    goose = args.goose.resolve()
    baseline_goose = args.baseline.resolve()
    baseline_companion = companion_for(baseline_goose)
    require(goose.is_file(), f"candidate compiler does not exist: {goose}")
    require(baseline_goose.is_file(), f"baseline compiler does not exist: {baseline_goose}")
    require(baseline_companion.is_file(), f"baseline companion does not exist: {baseline_companion}")

    requested_work = args.work if args.work else Path(".work/lint_units")
    if not requested_work.is_absolute():
        requested_work = ROOT / requested_work
    work = requested_work.resolve()
    require(work != WORK_ROOT and WORK_ROOT in work.parents,
            f"scratch directory must be a child of {WORK_ROOT}: {work}")
    if work.exists():
        # Resolve symlinks before this point, and only remove a target inside .work.
        shutil.rmtree(work)
    work.mkdir(parents=True)

    tmp_root = WORK_ROOT / "tmp"
    tmp_root.mkdir(parents=True, exist_ok=True)
    env = os.environ.copy()
    env["GOOSE_HOME"] = str(work / "goose-home")
    env["TMPDIR"] = str(tmp_root)
    bin_dir = work / "install" / "bin"
    bin_dir.mkdir(parents=True)
    sibling_goose = bin_dir / goose.name
    shutil.copy2(goose, sibling_goose)
    units_companion = companion_for(sibling_goose)

    build = run([goose, "build", "--units", "--stdlib", STDLIB, "-o", units_companion,
                 LINT_SOURCE], env=env)
    if build.returncode != 0:
        raise RuntimeError(f"goose build --units failed with exit {build.returncode}\n"
                           f"{build.stdout}{build.stderr}")
    require(units_companion.is_file(), f"units build did not create {units_companion}")
    print(f"built units companion: {units_companion}")

    if args.subset:
        check_subset(sibling_goose, baseline_goose, work)
    else:
        check_full(sibling_goose, baseline_goose, work, env)
        print("lint_units: parity and existing linter suite passed")


if __name__ == "__main__":
    try:
        main()
    except (OSError, RuntimeError) as error:
        sys.exit(str(error))
