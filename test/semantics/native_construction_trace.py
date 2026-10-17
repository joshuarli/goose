import argparse
import json
import os
from pathlib import Path
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[2]
FIXTURES = (
    ROOT / "test/semantics/golden/construction_raw_bytes.goose",
    ROOT / "test/semantics/sem_construction_source_values.goose",
    ROOT / "test/semantics/sem_construction_source_exit.goose",
    ROOT / "test/semantics/sem_construction_source_exit_recursive_multi.goose",
)
NUMERIC_PROFILES = ("release", "debug")
OPT_LEVELS = ("-O0", "-O2")


class CheckFailure(Exception):
    pass


def invoke(arguments, cwd, timeout):
    environment = os.environ.copy()
    environment["TMPDIR"] = str(ROOT / ".work/tmp")
    try:
        return subprocess.run([str(value) for value in arguments], cwd=cwd, env=environment,
                              stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
                              stderr=subprocess.PIPE, timeout=timeout)
    except (OSError, subprocess.TimeoutExpired) as error:
        raise CheckFailure(f"could not run {arguments[0]}: {error}") from error


def require_success(result, command):
    if result.returncode != 0:
        detail = result.stderr.decode("utf-8", errors="replace").strip()
        raise CheckFailure(f"{command} failed with {result.returncode}: {detail[:500]}")


def require_failure(result, command, diagnostic):
    detail = result.stderr.decode("utf-8", errors="replace")
    if result.returncode == 0 or diagnostic not in detail:
        raise CheckFailure(f"{command} did not fail with {diagnostic!r}: "
                           f"status={result.returncode}, stderr={detail[:500]!r}")


def one_json_line(data, label):
    lines = data.splitlines()
    if len(lines) != 1:
        raise CheckFailure(f"{label} wrote {len(lines)} lines instead of one")
    try:
        return json.loads(lines[0])
    except ValueError as error:
        raise CheckFailure(f"{label} did not write JSON: {lines[0][:200]!r}") from error


def core_answer(tool, core, profile, directory, timeout):
    result = invoke([tool, "run", core, "--numeric", profile], directory, timeout)
    answer = one_json_line(result.stdout, f"Core {core.name} {profile}")
    if result.returncode != 0 or not isinstance(answer, list) or len(answer) != 4 or answer[0] != "done":
        raise CheckFailure(f"Core {core.name} {profile} did not return a construction result: "
                           f"status={result.returncode}, answer={answer!r}")
    if not isinstance(answer[2], list) or any(type(byte) is not int or not 0 <= byte <= 255
                                               for byte in answer[2]):
        raise CheckFailure(f"Core {core.name} {profile} returned invalid stdout bytes")
    if not isinstance(answer[3], list):
        raise CheckFailure(f"Core {core.name} {profile} returned invalid events")
    outcome = answer[1]
    if outcome == ["returned"]:
        status = 0
    elif isinstance(outcome, list) and len(outcome) == 2 and outcome[0] == "exited":
        status = outcome[1]
    else:
        raise CheckFailure(f"unexpected outcome for {core.name}: {outcome!r}")
    return bytes(answer[2]), answer[3], status


def compile_c(cc, source, executable, optimization, profile, directory, timeout):
    command = [cc, optimization]
    if profile == "debug":
        command.append("-DGS_DEBUG=1")
    command += [source, "-o", executable, "-lm", "-pthread"]
    result = invoke(command, directory, timeout)
    require_success(result, f"C compilation {source.name} {optimization} {profile}")


def check_cli_contract(goose, directory, timeout):
    source = FIXTURES[0]
    result = invoke([goose, "--trace-construction", source], directory, timeout)
    require_failure(result, "trace without pipeline", "--trace-construction requires --pipeline gir")
    result = invoke([goose, "--trace-construction"], directory, timeout)
    require_failure(result, "trace without path", "--trace-construction needs a file path")
    result = invoke([goose, "--pipeline", "gir", "--trace-construction", "", "--standalone",
                     "-o", directory / "empty-path.c", source], directory, timeout)
    require_failure(result, "empty trace path", "valid file path")
    pilot = ROOT / "test/semantics/sem_num01_unsigned_wrap.goose"
    result = invoke([goose, "--pipeline", "gir", "--trace-construction",
                     directory / "pilot.json", "--standalone", "-o", directory / "pilot.c", pilot],
                    directory, timeout)
    require_failure(result, "trace outside construction profile", "construction profile")
    result = invoke([goose, "check", "--pipeline", "gir", "--trace-construction",
                     directory / "check.json", source], directory, timeout)
    require_failure(result, "trace with check", "cannot be combined with --check")


def compare_fixture(goose, semantics, cc, fixture, root_work, timeout):
    name = fixture.stem
    directory = root_work / name
    directory.mkdir(parents=True, exist_ok=True)
    core = directory / "program.core.json"
    traced_c = directory / "traced.c"
    default_c = directory / "default.c"
    trace = directory / "trace.json"
    compile_result = invoke([goose, "--emit-core", core, "--check", fixture], directory, timeout)
    require_success(compile_result, f"Core export {name}")
    traced_result = invoke([goose, "--pipeline", "gir", "--trace-construction", trace,
                            "--standalone", "-o", traced_c, fixture], directory, timeout)
    require_success(traced_result, f"traced GIR export {name}")
    default_result = invoke([goose, "--pipeline", "gir", "--standalone", "-o", default_c, fixture],
                            directory, timeout)
    require_success(default_result, f"default GIR export {name}")
    differences = []
    for profile in NUMERIC_PROFILES:
        expected_stdout, expected_events, expected_status = core_answer(
            semantics, core, profile, directory, timeout)
        for optimization in OPT_LEVELS:
            traced_program = directory / f"traced-{profile}-{optimization[2:]}"
            default_program = directory / f"default-{profile}-{optimization[2:]}"
            compile_c(cc, traced_c, traced_program, optimization, profile, directory, timeout)
            compile_c(cc, default_c, default_program, optimization, profile, directory, timeout)
            trace.unlink(missing_ok=True)
            traced_run = invoke([traced_program], directory, timeout)
            if traced_run.returncode != expected_status or traced_run.stdout != expected_stdout:
                differences.append(f"traced {profile} {optimization} stdout/status: "
                                   f"got {traced_run.returncode}/{traced_run.stdout!r}, "
                                   f"expected {expected_status}/{expected_stdout!r}")
            if not trace.is_file():
                differences.append(f"traced {profile} {optimization} wrote no trace")
            else:
                record = one_json_line(trace.read_bytes(), f"native {name} {profile} {optimization}")
                if record != ["construction", expected_events]:
                    differences.append(f"events differ at {profile} {optimization}: "
                                       f"native={record!r}, Core={expected_events!r}")
            trace.unlink()
            default_run = invoke([default_program], directory, timeout)
            if default_run.returncode != expected_status or default_run.stdout != expected_stdout:
                differences.append(f"default {profile} {optimization} stdout/status: "
                                   f"got {default_run.returncode}/{default_run.stdout!r}, "
                                   f"expected {expected_status}/{expected_stdout!r}")
            if trace.exists():
                differences.append(f"default {profile} {optimization} created a trace")
            if not differences:
                print(f"{name} {profile} {optimization}: exact events, stdout and status")
    if differences:
        raise CheckFailure(f"{name}: " + "; ".join(differences))


def check_trace_io_failure(goose, cc, root_work, timeout):
    fixture = FIXTURES[0]
    directory = root_work / "trace-io-failure"
    directory.mkdir(parents=True, exist_ok=True)
    missing = directory / "missing" / "trace.json"
    cfile = directory / "failure.c"
    program = directory / "failure"
    result = invoke([goose, "--pipeline", "gir", "--trace-construction", missing,
                     "--standalone", "-o", cfile, fixture], directory, timeout)
    require_success(result, "GIR export for trace I/O failure")
    compile_c(cc, cfile, program, "-O0", "release", directory, timeout)
    result = invoke([program], directory, timeout)
    detail = result.stderr.decode("utf-8", errors="replace")
    if result.returncode != 74 or "construction trace" not in detail:
        raise CheckFailure(f"native trace open failure was not reported: "
                           f"status={result.returncode}, stderr={detail!r}")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--goose", type=Path, required=True)
    parser.add_argument("--semantics", type=Path, required=True)
    parser.add_argument("--cc", default="clang")
    parser.add_argument("--timeout", type=float, default=120)
    args = parser.parse_args()
    for executable in (args.goose, args.semantics):
        if not executable.is_file():
            parser.error(f"not a file: {executable}")
    args.goose = args.goose.resolve()
    args.semantics = args.semantics.resolve()
    work = ROOT / ".work/tmp/native-construction-trace"
    work.mkdir(parents=True, exist_ok=True)
    try:
        check_cli_contract(args.goose, work, args.timeout)
    except CheckFailure as error:
        print(f"native construction trace: {error}", file=sys.stderr)
        return 1
    differences = []
    for fixture in FIXTURES:
        try:
            compare_fixture(args.goose, args.semantics, args.cc, fixture, work, args.timeout)
        except CheckFailure as error:
            differences.append(str(error))
    try:
        check_trace_io_failure(args.goose, args.cc, work, args.timeout)
    except CheckFailure as error:
        differences.append(str(error))
    if differences:
        print("native construction trace: " + "\n".join(differences), file=sys.stderr)
        return 1
    print("native construction trace checks passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
