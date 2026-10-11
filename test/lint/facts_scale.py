#!/usr/bin/env python3
"""Exercise lint facts beyond the original stream and record ceilings."""

import argparse
import json
import os
from pathlib import Path
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[2]
TYPE_COUNT = 4096
CALLS_PER_ROOT = 256


def check(condition, message):
    if not condition:
        raise AssertionError(message)


def find_built_goose():
    executable = "goose.exe" if os.name == "nt" else "goose"
    for configuration in ("Debug", "", "Release", "RelWithDebInfo"):
        candidate = ROOT / "build" / configuration / executable
        if candidate.is_file():
            return candidate
    raise AssertionError("no Goose executable under build/; pass --goose or build the default CMake targets")


def scale_source():
    lines = ["var counter: i64 = 0;", "fn ping() { counter += 1; }", "fn fanout<T>(value: T) {"]
    lines.extend("    ping();" for _ in range(CALLS_PER_ROOT))
    lines.append("}")
    for index in range(TYPE_COUNT):
        lines.append(f"struct Variant{index:04d} {{ value: i64 }}")
    lines.append("fn main() {")
    for index in range(TYPE_COUNT):
        lines.append(f"    let value_{index:04d} = Variant{index:04d} {{ value: {index} }};")
        lines.append(f"    fanout(value_{index:04d});")
    lines.append("}")
    return "\n".join(lines) + "\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--goose", type=Path, help="built goose executable (default: find it under build/)")
    args = parser.parse_args()
    goose = (args.goose or find_built_goose()).resolve()

    with tempfile.TemporaryDirectory(prefix="goose-lint-facts-scale-") as directory:
        source = Path(directory) / "generic-fanout.goose"
        source.write_text(scale_source())
        command = [str(goose), "lint", str(source), "--stdlib", str(ROOT / "stdlib"),
                   "--format", "jsonl", "-O1"]
        result = subprocess.run(command, cwd=ROOT, text=True, capture_output=True)
    try:
        records = [json.loads(line) for line in result.stdout.splitlines() if line]
    except json.JSONDecodeError as error:
        raise AssertionError(f"invalid lint JSONL: {error}\n{result.stdout}\n{result.stderr}")
    check(records and records[0].get("kind") == "header" and records[-1].get("kind") == "summary",
          f"lint omitted its JSONL envelope\n{result.stdout}\n{result.stderr}")
    coverage = [record for record in records if record.get("kind") == "coverage"]
    check(result.returncode == 0 and not any(record.get("kind") == "error" for record in records),
          f"large facts lint failed with status {result.returncode}\n{result.stdout}\n{result.stderr}")
    check(len(coverage) == 1 and coverage[0].get("parse") == "complete" and
          coverage[0].get("check") == "complete" and
          coverage[0].get("checked_specializations") == TYPE_COUNT + 2 and
          coverage[0].get("unchecked_generic_bodies") == 0 and
          not coverage[0].get("unsupported"),
          f"large facts lint reported incomplete coverage: {coverage}")
    summary = records[-1]
    check(summary.get("errors") == 0 and summary.get("findings") == 0 and summary.get("exit_status") == 0,
          f"large facts lint returned an unexpected summary: {summary}")
    print(f"PASS: {TYPE_COUNT} generic instantiations, {TYPE_COUNT * CALLS_PER_ROOT} body calls, "
          f"{coverage[0]['checked_specializations']} checked specializations")


if __name__ == "__main__":
    main()
