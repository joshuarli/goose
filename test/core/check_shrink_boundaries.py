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
SOURCE_CASES = {
    "sem_mem11_boundary_limited_whole": ("limited-value",),
    "sem_mem11_boundary_limited_cap": ("limited-capacity", "limited-value"),
    "sem_mem11_boundary_runtime_capacity": ("runtime-capacity",),
    "sem_mem11_boundary_limited_nonliteral_initializer": ("limited-initializer",),
}
REJECTION_CASES = {
    "sem_mem09_reject_retained_call_argument": (
        """fn consume(view: i64[:], value: i64) { print(value, " ", view[0]); }
fn remove(values: i64[>..<]&) -> i64 { values.pop(); return 0; }
fn main() { var values: i64[>..<] = [1, 2]; consume(values[..], remove(values)); }
""",
        "cannot call remove, which shrinks values: values[..]",
    ),
    "sem_mem09_reject_retained_index_destination": (
        """fn remove(values: i64[>..<]&) -> i64 { values.pop(); return 9; }
fn main() { var values: i64[>..<] = [1, 2]; values[0] = remove(values); }
""",
        "cannot call remove, which shrinks values: values[0]",
    ),
    "sem_mem09_reject_retained_slice_run": (
        """fn first(view: i64[:], value: i64) -> i64 { return view[0] + value; }
fn remove(values: i64[>..<]&) -> i64 { values.pop(); return 0; }
fn main() { var values: i64[>..<] = [1, 2]; print(first(values[1..], remove(values))); }
""",
        "cannot call remove, which shrinks values: values[1..]",
    ),
    "sem_mem09_reject_retained_append_run": (
        """fn choose(view: i64[:], value: i64) -> i64[:] { return view; }
fn remove(values: i64[>..<]&) -> i64 { values.pop(); return 0; }
fn main() { var values: i64[>..<] = [1, 2]; values.append(choose(values[..], remove(values))); }
""",
        "cannot call remove, which shrinks values: values[..]",
    ),
    "sem_mem10_reject_loop_carried_slice": (
        """fn main() {
    var values: i64[>..<] = [1, 2, 3]; let view = values[..]; var round = 0;
    while round < 2 { values.pop(); print(view[0]); round += 1; }
}
""",
        "cannot pop values while view",
    ),
    "sem_mem10_reject_nested_loop_backedge": (
        """fn main() {
    var values: i64[>..<] = [1, 2, 3, 4]; let view = values[..]; var round = 0;
    while round < 2 { for step in 1 { values.pop(); } round += 1; }
    print(view[0]);
}
""",
        "cannot pop values while view",
    ),
    "sem_mem10_reject_byref_iteration_shrink": (
        """fn main() {
    var values: i64[>..<] = [1, 2, 3];
    for &item in values { values.pop(); print(item); }
}
""",
        "cannot pop values while item",
    ),
    "sem_mem10_reject_live_slice_iteration_shrink": (
        """fn main() {
    var values: i64[>..<] = [1, 2, 3]; let view = values[..];
    for item in view { values.pop(); print(item); }
}
""",
        "cannot pop values while view",
    ),
    "sem_mem11_reject_direct_let_replacement": (
        """fn main() { let values: i64[>..<] = [1, 2, 3]; values = [8, 9]; }
""",
        "cannot assign to let values",
    ),
    "sem_mem11_reject_rhs_owner_read": (
        """fn main() { var values: i64[>..<] = [1, 2, 3]; values = [values[0], 9]; }
""",
        "cannot use values in the value assigned to values",
    ),
    "sem_mem11_reject_rhs_owner_call": (
        """fn main() {
    var values: i64[>..<] = [1, 2, 3];
    fn replacement() -> i64[>..<] { let first = values[0]; return [first]; }
    values = replacement();
}
""",
        "cannot call replacement in the value assigned to values",
    ),
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
        for name, features in SOURCE_CASES.items():
            source = ROOT / "test" / "semantics" / f"{name}.goose"
            report = subprocess.run([goose, "--check", "--emit-core-report", source],
                                    capture_output=True, check=True)
            feature_json = ",".join('"' + feature + '"' for feature in features)
            expected = ('{"unsupported":[' + feature_json + ']}\n').encode()
            assert report.stdout == expected, (name, report.stdout, report.stderr)
            for flags in (("--emit-core",), ("--emit-gir-high",), ("--emit-gir-low",),
                          ("--emit-core", "--emit-gir-high", "--emit-gir-low")):
                outputs = [directory / f"{name}-{index}" for index in range(len(flags))]
                command = [goose, "--check"]
                for flag, output in zip(flags, outputs):
                    command.extend((flag, output))
                result = subprocess.run([*command, source], capture_output=True)
                assert result.returncode != 0, (name, flags)
                assert f"unsupported in core-pilot: {features[0]}".encode() in result.stderr, result.stderr
                assert all(not output.exists() for output in outputs), (name, flags)
                for output in outputs:
                    output.write_bytes(b"existing artifact")
                result = subprocess.run([*command, source], capture_output=True)
                assert result.returncode != 0, (name, flags)
                assert all(output.read_bytes() == b"existing artifact" for output in outputs)
                for output in outputs:
                    output.unlink()
        for name, (program, diagnostic) in REJECTION_CASES.items():
            source = directory / f"{name}.goose"
            source.write_text(program, encoding="utf-8")
            result = subprocess.run([goose, "--check", source], capture_output=True)
            assert result.returncode != 0, name
            assert diagnostic.encode() in result.stderr, (name, result.stderr)
            for flags in (("--emit-core",), ("--emit-gir-high",), ("--emit-gir-low",),
                          ("--emit-core", "--emit-gir-high", "--emit-gir-low")):
                outputs = [directory / f"{name}-artifact-{index}" for index in range(len(flags))]
                command = [goose, "--check"]
                for flag, output in zip(flags, outputs):
                    command.extend((flag, output))
                result = subprocess.run([*command, source], capture_output=True)
                assert result.returncode != 0, (name, flags)
                assert diagnostic.encode() in result.stderr, (name, flags, result.stderr)
                assert all(not output.exists() for output in outputs), (name, flags)
                for output in outputs:
                    output.write_bytes(b"existing artifact")
                result = subprocess.run([*command, source], capture_output=True)
                assert result.returncode != 0, (name, flags)
                assert diagnostic.encode() in result.stderr, (name, flags, result.stderr)
                assert all(output.read_bytes() == b"existing artifact" for output in outputs)
                for output in outputs:
                    output.unlink()
    print("shrink boundaries ok")


if __name__ == "__main__":
    check(str(Path(sys.argv[1]).resolve()))
