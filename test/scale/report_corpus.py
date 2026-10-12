#!/usr/bin/env python3
"""`--check --build-report` over every positive fixture and sample.

  python test/scale/report_corpus.py --goose GOOSE [-j N] [--allow-unclassified N]

Each program is checked with a report. A program the runner accepts must be
accepted, must not crash the compiler, and must give a report that
report_check.py passes. The reports' counts are summed: every context whose
key equals an earlier context's of the same function is counted by
`duplicate_contexts` with a reason, and none may be left `unclassified`, so a
dimension the key lacks cannot hide as a duplicate.

Prints the totals as JSON and one line per violation; exits 1 on any.
"""

import argparse
import concurrent.futures
import json
import os
import shutil
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(ROOT / "test"))
import report_check  # noqa: E402
import run_tests  # noqa: E402


def programs():
    found = [f for f in sorted((ROOT / "test").glob("*/*.goose"))
             if f.parent.name not in ("goose_in_goose", "lint", "errors", "errors_tc")
             and f.name != "lexer_tokens.goose"]
    # Not the fixtures that expect the compiler to reject them.
    found = [f for f in found if "parse-only" not in run_tests.first_line(f)
             and not run_tests.error_markers(f)]
    return found + sorted((ROOT / "samples").glob("*.goose"))


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--goose", required=True)
    ap.add_argument("-j", "--jobs", type=int, default=min(os.cpu_count() or 1, 16))
    ap.add_argument("--work")
    a = ap.parse_args()
    work = Path(a.work) if a.work else ROOT / ".work" / "report_corpus"
    shutil.rmtree(work, ignore_errors=True)
    work.mkdir(parents=True)
    goose = str(Path(a.goose).resolve())
    bad = []
    totals = {"programs": 0, "functions": 0, "contexts": 0, "duplicate_contexts": 0,
              "reasons": {}}

    def one(f):
        out = work / f"{f.parent.name}-{f.stem}.json"
        defines = ["-D" + d for d in run_tests.runtime_defines(f)]
        r = subprocess.run([goose, *defines, "--check", "--build-report", str(out), str(f)],
                           capture_output=True, text=True, cwd=ROOT)
        return f, r, out

    with concurrent.futures.ThreadPoolExecutor(a.jobs) as pool:
        for f, r, out in pool.map(one, programs()):
            name = f"{f.parent.name}/{f.stem}"
            if r.returncode != 0:
                bad.append(f"{name}: exit {r.returncode}: {(r.stdout + r.stderr)[-200:]}")
                continue
            report = json.loads(out.read_text())
            problems = report_check.check(report, None)
            bad += [f"{name}: {p}" for p in problems]
            counts = report["counts"]
            totals["programs"] += 1
            totals["functions"] += counts["source_functions"]
            totals["contexts"] += counts["checked_contexts"]
            dup = counts["duplicate_contexts"]
            totals["duplicate_contexts"] += dup["count"]
            for reason, n in dup.items():
                if reason != "count":
                    totals["reasons"][reason] = totals["reasons"].get(reason, 0) + n
            if dup["unclassified"]:
                bad.append(f"{name}: {dup['unclassified']} contexts share a key without a reason")
    print(json.dumps(totals))
    for line in bad:
        print(f"report_corpus: {line}")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
