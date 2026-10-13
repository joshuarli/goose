#!/usr/bin/env python3
"""Check shrink support diagnostics and atomic Core/GIR export rejection."""

from pathlib import Path
import os
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]
CASES = {
    "exit": "shrink-exit-exception",
    "balanced": "shrink-balanced-call",
    "demand": "shrink-demand",
    "demand_recursive": "shrink-demand",
    "demand_slice_slot": "shrink-demand",
    "parameter": "shrink-parameter-alias",
    "parameter_capture": "shrink-parameter-alias",
}


def check(goose):
    scratch = ROOT / ".work" / "tmp"
    scratch.mkdir(parents=True, exist_ok=True)
    os.environ["TMPDIR"] = str(scratch)
    with tempfile.TemporaryDirectory(dir=scratch) as temporary:
        directory = Path(temporary)
        for name, feature in CASES.items():
            source = ROOT / "test" / "core" / f"core_export_shrink_{name}.goose"
            report = subprocess.run([goose, "--check", "--emit-core-report", source],
                                    capture_output=True, check=True)
            expected = ('{"unsupported":["' + feature + '"]}\n').encode()
            assert report.stdout == expected, (name, report.stdout, report.stderr)
            for flags in (("--emit-core",), ("--emit-gir-high",), ("--emit-gir-low",),
                          ("--emit-core", "--emit-gir-high", "--emit-gir-low")):
                outputs = [directory / str(index) for index in range(len(flags))]
                command = [goose, "--check"]
                for flag, output in zip(flags, outputs):
                    command.extend((flag, output))
                result = subprocess.run([*command, source], capture_output=True)
                assert result.returncode != 0, (name, flags)
                assert f"unsupported in core-pilot: {feature}".encode() in result.stderr, result.stderr
                assert all(not output.exists() for output in outputs), (name, flags)
                for output in outputs:
                    output.write_bytes(b"existing artifact")
                result = subprocess.run([*command, source], capture_output=True)
                assert result.returncode != 0, (name, flags)
                assert all(output.read_bytes() == b"existing artifact" for output in outputs)
                for output in outputs:
                    output.unlink()
        for name in ("supported", "globals"):
            source = ROOT / "test" / "core" / f"core_export_shrink_{name}.goose"
            report = subprocess.run([goose, "--check", "--emit-core-report", source],
                                    capture_output=True, check=True)
            assert report.stdout == b'{"unsupported":[]}\n', (name, report.stdout, report.stderr)
            subprocess.run([goose, "--check", "--emit-core", directory / name, source], check=True)
        for name in (*CASES, "supported", "globals"):
            stem = f"core_export_shrink_{name}"
            source = ROOT / "test" / "core" / f"{stem}.goose"
            result = subprocess.run([goose, source], capture_output=True, check=True)
            expected = (ROOT / "test" / "expected" / f"{stem}.out").read_bytes()
            assert result.stdout == expected, (name, result.stdout, result.stderr)
    print("shrink boundaries ok")


if __name__ == "__main__":
    check(str(Path(sys.argv[1]).resolve()))
