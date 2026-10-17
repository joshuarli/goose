#!/usr/bin/env python3

import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]


def build(goose, work, source, exe):
    report = work / "build-report.json"
    report.unlink(missing_ok=True)
    result = subprocess.run(
        [str(goose), "build", "--units", "-O2", "--build-report", str(report),
         "-o", str(exe), str(source)],
        cwd=work,
        env=dict(os.environ, GOOSE_HOME=str(work / "home"), TMPDIR=str(work / "tmp")),
        capture_output=True,
        text=True,
        errors="replace",
    )
    if result.returncode != 0:
        raise RuntimeError(f"build failed ({result.returncode}):\n{result.stdout}{result.stderr}")
    return json.loads(report.read_text(encoding="utf-8"))["extensions"]["native_compile"]


def run(exe, work):
    result = subprocess.run([str(exe)], cwd=work, capture_output=True, text=True, errors="replace")
    if result.returncode != 0 or result.stdout != "14065\n":
        raise RuntimeError(f"program output changed: exit {result.returncode}: {result.stdout!r}{result.stderr}")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--goose", required=True, type=Path)
    parser.add_argument("--work", type=Path, default=ROOT / ".work" / "tmp" / "units_last_record")
    args = parser.parse_args()
    goose = args.goose.resolve()
    work = args.work.resolve()
    if not work.is_relative_to(ROOT / ".work"):
        raise ValueError(f"work path must be under {ROOT / '.work'}: {work}")
    shutil.rmtree(work, ignore_errors=True)
    (work / "tmp").mkdir(parents=True)
    source = work / "same.goose"
    source.write_text(
        "fn calc(x: i64) -> i64 {\n"
        "    var total = 0;\n"
        "    for i in 0..x { total += i * 3 + 1; }\n"
        "    return total;\n"
        "}\n"
        "fn main() { print(calc(97)); }\n",
        encoding="utf-8",
    )
    exe = work / ("program.exe" if os.name == "nt" else "program")
    cold = build(goose, work, source, exe)
    if cold["no_op"] or not cold["link"]["ran"]:
        raise RuntimeError("cold units build did not compile and link")
    run(exe, work)

    damaged = bytearray(exe.read_bytes())
    if not damaged:
        raise RuntimeError("cold units build produced an empty executable")
    damaged[len(damaged) // 2] ^= 1
    exe.write_bytes(damaged)
    repaired = build(goose, work, source, exe)
    if repaired["no_op"] or not repaired["link"]["ran"]:
        raise RuntimeError("units build reused an executable whose contents changed")
    run(exe, work)
    print("units_last_record: ok")


if __name__ == "__main__":
    try:
        sys.exit(main() or 0)
    except Exception as e:
        print(f"units_last_record: {e}", file=sys.stderr)
        sys.exit(1)
