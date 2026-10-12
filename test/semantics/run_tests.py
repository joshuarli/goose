#!/usr/bin/env python3
"""Compare the Lean reference model with the expectations of the semantic fixtures.

For every runnable fixture in this directory and every golden in `golden/`, the
Goose compiler exports the program (`--emit-core FILE --check SOURCE`), the
reference tool runs the export (`TOOL run FILE --numeric MODE`), and the
tool's outcome and standard output are compared with the fixture's expectation.
With `--pipeline gir` the compiler also builds and runs the fixture through
that pipeline, and the native result is compared with the same expectation.

A case ends in one of five classes: agree, mismatch, unsupported (the exporter
named a feature outside the profile), harness-failure (a tool broke its
contract or could not be run) and inconclusive (a timeout). Only `agree` passes.
Exit status 0 means every selected case agreed; 1 means some did not; 2 means
the harness was misused.

The tool prints exactly one JSON line and exits:

    ["done",["returned"],STDOUT]            exit 0
    ["done",["aborted",KIND,LINE],STDOUT]   exit 0
    ["done",["exited",CODE],STDOUT]         exit 0
    ["timeout",STDOUT]                      exit 3
    ["fault",KIND]                          exit 4
    ["malformed",MESSAGE]                   exit 2
    ["rejected",RULE,MESSAGE]               exit 5

Run `python3 test/semantics/run_tests.py --self-test` to check the harness
against the fake tools in `fake/`.
"""

import argparse
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
FAKE = HERE / "fake"

AGREE = "agree"
MISMATCH = "mismatch"
UNSUPPORTED = "unsupported"
HARNESS_FAILURE = "harness-failure"
INCONCLUSIVE = "inconclusive"
CLASSES = (AGREE, MISMATCH, UNSUPPORTED, HARNESS_FAILURE, INCONCLUSIVE)
# The class of a case whose runs differ: the worse one is reported.
SEVERITY = {HARNESS_FAILURE: 4, MISMATCH: 3, INCONCLUSIVE: 2, UNSUPPORTED: 1, AGREE: 0}

RELEASE = "release"
DEBUG = "debug"

# What the runtime prints for each abort kind, as a prefix of the diagnostic
# text before the source location. A user abort prints its own message, so it
# is the kind of every diagnostic that matches none of the others.
DIAGNOSTICS = {
    "div_zero": r"division by zero",
    "div_overflow": r"integer overflow in division",
    "index_oob": r"index -?\d+ out of bounds \(length \d+\)",
    "slice_oob": r"slice bounds out of range",
    "assert": r"assert failed",
    "int_overflow": r"integer overflow \(debug\)",
    "cast_range": r"as conversion out of range \(debug\)",
}
ABORT_KINDS = frozenset(DIAGNOSTICS) | {"user_abort"}

# Tool answer tag, and the exit status that goes with it.
TOOL_EXIT = {"done": 0, "timeout": 3, "fault": 4, "malformed": 2, "rejected": 5}

UNSUPPORTED_PATTERN = re.compile(r"unsupported in core-pilot: (\S+)")
LOCATION_PATTERN = re.compile(r"\.goose:(\d+)\)\s*$")


class HarnessFailure(Exception):
    """A tool broke its contract, or a fixture's expectation is unusable."""


class Inconclusive(Exception):
    """A process outran its wall-clock budget."""


Outcome = tuple  # ("returned",) | ("aborted", kind, line) | ("exited", code)


@dataclass(frozen=True)
class Fixture:
    name: str
    source: Path
    out: Path
    stderr: Path | None
    aborts: bool
    expect: Path | None
    modes: tuple[str, ...]


@dataclass(frozen=True)
class Verdict:
    cls: str
    detail: str = ""


def joined(text: str) -> str:
    """Output as the main runner compares it: no trailing blank line."""
    return text.rstrip("\n")


def modes_for(source: Path) -> tuple[str, ...]:
    """The numeric profiles a fixture is checked in.

    A fixture whose first line defines GS_DEBUG=1 is only ever built as a debug
    program, so its expectation is the debug result. One marked `runtime-debug`
    gives the same result in both profiles.
    """
    with open(source, encoding="utf-8") as handle:
        first = handle.readline()
    if re.match(r"// runtime-define: GS_DEBUG=1$", first.strip()):
        return (DEBUG,)
    if "runtime-debug" in first:
        return (RELEASE, DEBUG)
    return (RELEASE,)


def discover(root: Path) -> list[Fixture]:
    """Runnable fixtures of `root` (expectations in ../expected) and its goldens."""
    fixtures = []
    expected = root.parent / "expected"
    for source in sorted(root.glob("*.goose")):
        name = source.stem
        stderr = expected / f"{name}.stderr"
        fixtures.append(Fixture(
            name, source, expected / f"{name}.out", stderr if stderr.exists() else None,
            (expected / f"{name}.aborts").exists(), None, modes_for(source)))
    for source in sorted((root / "golden").glob("*.goose")):
        name = source.stem
        expect = source.with_suffix(".expect.json")
        fixtures.append(Fixture(
            name, source, source.with_suffix(".out"), None, False,
            expect if expect.exists() else None, modes_for(source)))
    names = [fixture.name for fixture in fixtures]
    duplicates = sorted({name for name in names if names.count(name) > 1})
    if duplicates:
        raise HarnessFailure(f"fixture names are not unique: {', '.join(duplicates)}")
    return fixtures


def abort_kind(markers: list[str]) -> str:
    for kind, pattern in DIAGNOSTICS.items():
        if any(re.match(pattern, marker) for marker in markers):
            return kind
    return "user_abort"


def expected_outcome(fixture: Fixture) -> Outcome:
    """What a fixture expects of the program's termination.

    An explicit `.expect.json` (`["expect", OUTCOME]`) wins. Otherwise an
    expected abort (`.aborts`) gets its kind from the diagnostic text the
    fixture's `.stderr` requires and its line from the `NAME.goose:LINE)`
    location it requires.
    """
    if fixture.expect is not None:
        try:
            value = json.loads(fixture.expect.read_text(encoding="utf-8"))
            if value[0] != "expect":
                raise ValueError("not an expectation")
            return parse_outcome(value[1])
        except (ValueError, IndexError, TypeError, HarnessFailure) as error:
            raise HarnessFailure(f"unusable {fixture.expect.name}: {error}") from error
    if not fixture.aborts:
        return ("returned",)
    if fixture.stderr is None:
        raise HarnessFailure(f"expected abort without {fixture.name}.stderr")
    markers = [line.strip() for line in fixture.stderr.read_text(encoding="utf-8").splitlines()
               if line.strip()]
    lines = [int(match[1]) for marker in markers
             if (match := re.search(r"\.goose:(\d+)\)$", marker))]
    if len(lines) != 1:
        raise HarnessFailure(f"{fixture.name}.stderr must name exactly one NAME.goose:LINE) location")
    return ("aborted", abort_kind([m for m in markers if not LOCATION_PATTERN.search(m)]), lines[0])


def parse_outcome(value) -> Outcome:
    """Validate an outcome as the tool prints it."""
    if isinstance(value, list) and value == ["returned"]:
        return ("returned",)
    if (isinstance(value, list) and len(value) == 3 and value[0] == "aborted"
            and value[1] in ABORT_KINDS and type(value[2]) is int):
        return ("aborted", value[1], value[2])
    if isinstance(value, list) and len(value) == 2 and value[0] == "exited" and type(value[1]) is int:
        return ("exited", value[1])
    raise HarnessFailure(f"malformed outcome {value!r}")


def run(argv, timeout, cwd=None):
    try:
        return subprocess.run([str(a) for a in argv], capture_output=True, timeout=timeout,
                              cwd=cwd, stdin=subprocess.DEVNULL)
    except subprocess.TimeoutExpired as error:
        raise Inconclusive(f"{Path(str(argv[0])).name} exceeded {timeout}s") from error
    except OSError as error:
        raise HarnessFailure(f"cannot run {argv[0]}: {error}") from error


def text(data: bytes) -> str:
    return data.decode("utf-8", errors="replace")


def export(goose: Path, source: Path, work: Path, timeout: float) -> tuple[Path | None, str | None]:
    """Export one program. Returns (core file, None) or (None, unsupported feature id)."""
    core = work / "program.core"
    done = run([goose, "--emit-core", core, "--check", source], timeout)
    diagnostic = text(done.stderr)
    if done.returncode == 1 and (match := UNSUPPORTED_PATTERN.search(diagnostic)):
        return None, match[1]
    if done.returncode != 0:
        raise HarnessFailure(f"export failed (exit {done.returncode}): {diagnostic.strip()[:300]}")
    if not core.is_file():
        raise HarnessFailure("export succeeded but wrote no file")
    return core, None


def tool_result(tool: Path, core: Path, mode: str, timeout: float) -> tuple:
    """Run the reference tool and validate its one-line answer against the contract."""
    done = run([tool, "run", core, "--numeric", mode], timeout)
    return parse_tool_answer(done.returncode, text(done.stdout), text(done.stderr))


def parse_tool_answer(returncode: int, stdout: str, stderr: str = "") -> tuple:
    """Validate what the tool printed and its exit status against the contract.

    Returns ("done", outcome, stdout), ("timeout", stdout), ("fault", kind),
    ("malformed", message) or ("rejected", rule, message).
    """
    lines = stdout.splitlines()
    if len(lines) != 1:
        raise HarnessFailure(f"tool printed {len(lines)} lines, not one (exit {returncode}): "
                             f"{stderr.strip()[:300]}")
    try:
        answer = json.loads(lines[0])
    except ValueError as error:
        raise HarnessFailure(f"tool output is not JSON: {lines[0][:200]}") from error
    if not isinstance(answer, list) or not answer or answer[0] not in TOOL_EXIT:
        raise HarnessFailure(f"unknown tool answer {lines[0][:200]}")
    tag = answer[0]
    if returncode != TOOL_EXIT[tag]:
        raise HarnessFailure(f"tool answered {tag!r} but exited {returncode}, "
                             f"not {TOOL_EXIT[tag]}")
    shape = {"done": 3, "timeout": 2, "fault": 2, "malformed": 2, "rejected": 3}[tag]
    if len(answer) != shape:
        raise HarnessFailure(f"tool answer {tag!r} has {len(answer)} elements, not {shape}")
    if tag == "done":
        if not isinstance(answer[2], str):
            raise HarnessFailure("tool stdout is not a string")
        return ("done", parse_outcome(answer[1]), answer[2])
    if tag == "timeout":
        if not isinstance(answer[1], str):
            raise HarnessFailure("tool stdout is not a string")
        return ("timeout", answer[1])
    return tuple(answer)


def describe(outcome: Outcome) -> str:
    return json.dumps(list(outcome))


def judge_tool(fixture: Fixture, mode: str, answer: tuple, outcome: Outcome, stdout: str) -> Verdict:
    """Classify the tool's answer for one numeric profile."""
    tag = answer[0]
    if tag == "timeout":
        return Verdict(INCONCLUSIVE, f"[{mode}] the tool ran out of fuel")
    if tag != "done":
        return Verdict(MISMATCH, f"[{mode}] the tool answered {json.dumps(list(answer))} "
                                 f"for a program the compiler accepts")
    problems = []
    if answer[1] != outcome:
        problems.append(f"outcome {describe(answer[1])}, expected {describe(outcome)}")
    if joined(answer[2]) != stdout:
        problems.append(f"stdout {joined(answer[2])!r}, expected {stdout!r}")
    if problems:
        return Verdict(MISMATCH, f"[{mode}] " + "; ".join(problems))
    return Verdict(AGREE)


def build_and_run_pipeline(goose: Path, cc: str, pipeline: str, fixture: Fixture, mode: str,
                           work: Path, timeout: float) -> tuple[int, str, str]:
    """Build the fixture through the named compiler pipeline and run it natively."""
    defines = ["-DGS_DEBUG=1"] if mode == DEBUG else []
    cfile = work / f"{pipeline}-{mode}.c"
    program = work / f"{pipeline}-{mode}"
    built = run([goose, "--pipeline", pipeline, *defines, "--standalone", "-o", cfile, fixture.source],
                timeout)
    if built.returncode != 0:
        raise HarnessFailure(f"{pipeline} pipeline build failed (exit {built.returncode}): "
                             f"{text(built.stderr).strip()[:300]}")
    compiled = run([cc, "-O0", *defines, cfile, "-o", program, "-lm", "-pthread"], timeout)
    if compiled.returncode != 0:
        raise HarnessFailure(f"C compiler rejected the {pipeline} output: "
                             f"{text(compiled.stderr).strip()[:300]}")
    ran = run([program], timeout, cwd=work)
    return ran.returncode, text(ran.stdout), text(ran.stderr)


def judge_pipeline(pipeline: str, fixture: Fixture, mode: str, outcome: Outcome, stdout: str,
                   code: int, out: str, err: str) -> Verdict:
    """Compare a natively run program with the fixture's expectation."""
    problems = []
    if (outcome[0] == "returned") != (code == 0):
        problems.append(f"exit status {code}, expected {describe(outcome)}")
    if outcome[0] == "exited" and code != outcome[1]:
        problems.append(f"exit status {code}, expected {outcome[1]}")
    if joined(out) != stdout:
        problems.append(f"stdout {joined(out)!r}, expected {stdout!r}")
    if fixture.stderr is not None:
        markers = [line.strip() for line in fixture.stderr.read_text(encoding="utf-8").splitlines()
                   if line.strip()]
        missing = [marker for marker in markers if marker not in err]
        if missing:
            problems.append(f"stderr lacks {missing}")
    if problems:
        return Verdict(MISMATCH, f"[{mode}] {pipeline}: " + "; ".join(problems))
    return Verdict(AGREE)


def run_case(fixture: Fixture, goose: Path, tool: Path, cc: str, pipeline: str | None,
             scratch: Path, timeout: float) -> Verdict:
    work = Path(tempfile.mkdtemp(prefix=f"{fixture.name}-", dir=scratch))
    verdicts = []

    def guarded(step):
        try:
            return step()
        except HarnessFailure as error:
            verdicts.append(Verdict(HARNESS_FAILURE, str(error)))
        except Inconclusive as error:
            verdicts.append(Verdict(INCONCLUSIVE, str(error)))
        return None

    def prepare():
        if not fixture.out.is_file():
            raise HarnessFailure(f"missing expected output {fixture.out.name}")
        return expected_outcome(fixture), joined(fixture.out.read_text(encoding="utf-8"))

    expectation = guarded(prepare)
    if expectation is None:
        return verdicts[0]
    outcome, stdout = expectation
    core = guarded(lambda: export(goose, fixture.source, work, timeout))
    if core is None:
        return verdicts[0]
    core_file, feature = core
    if feature is not None:
        return Verdict(UNSUPPORTED, feature)
    for mode in fixture.modes:
        def check_tool():
            answer = tool_result(tool, core_file, mode, timeout)
            verdicts.append(judge_tool(fixture, mode, answer, outcome, stdout))
        guarded(check_tool)
        if pipeline is not None:
            def check_pipeline():
                code, out, err = build_and_run_pipeline(goose, cc, pipeline, fixture, mode, work, timeout)
                verdicts.append(judge_pipeline(pipeline, fixture, mode, outcome, stdout, code, out, err))
            guarded(check_pipeline)
    worst = max(verdicts, key=lambda verdict: SEVERITY[verdict.cls])
    if worst.cls == AGREE:
        return worst
    return Verdict(worst.cls, "; ".join(v.detail for v in verdicts if v.cls == worst.cls))


def run_all(fixtures: list[Fixture], goose: Path, tool: Path, cc: str, pipeline: str | None,
            timeout: float, jobs: int) -> dict[str, int]:
    scratch_root = ROOT / "build" / "semantics"
    scratch_root.mkdir(parents=True, exist_ok=True)
    counts = dict.fromkeys(CLASSES, 0)
    with tempfile.TemporaryDirectory(prefix="run-", dir=scratch_root) as scratch:
        with ThreadPoolExecutor(max_workers=jobs) as pool:
            verdicts = list(pool.map(
                lambda fixture: run_case(fixture, goose, tool, cc, pipeline, Path(scratch), timeout),
                fixtures))
    for fixture, verdict in zip(fixtures, verdicts):
        counts[verdict.cls] += 1
        if verdict.cls != AGREE:
            print(f"{verdict.cls} {fixture.name}: {verdict.detail}")
    print(json.dumps(counts))
    return counts


def self_test() -> int:
    """Run the harness against the fake tools, one case per outcome class."""
    import contextlib
    import io

    def fixture(name, out, source="fn main() {}\n", *, stderr=None, aborts=False, expect=None,
                golden=False):
        base = tree / "semantics" / ("golden" if golden else "")
        (base / f"{name}.goose").write_text(source)
        if golden:
            if out is not None:
                (base / f"{name}.out").write_text(out)
            if expect is not None:
                (base / f"{name}.expect.json").write_text(json.dumps(expect))
            return
        if out is not None:
            (tree / "expected" / f"{name}.out").write_text(out)
        if stderr is not None:
            (tree / "expected" / f"{name}.stderr").write_text(stderr)
        if aborts:
            (tree / "expected" / f"{name}.aborts").write_text("")

    def answer(value, code=0):
        return {"answer": value, "exit": code}

    def returns(stdout, mode=RELEASE):
        return {mode: answer(["done", ["returned"], stdout])}

    def aborts_with(kind, line, stdout="", mode=RELEASE):
        return {mode: answer(["done", ["aborted", kind, line], stdout])}

    debug_define = "// runtime-define: GS_DEBUG=1\nfn main() {}\n"
    both_modes = "// runtime-debug\nfn main() {}\n"
    scratch_root = ROOT / "build" / "semantics"
    scratch_root.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="self-test-", dir=scratch_root) as temporary:
        tree = Path(temporary) / "test"
        for sub in ("semantics/golden", "expected"):
            (tree / sub).mkdir(parents=True)
        runs, exports = {}, {}
        expected_class = {}

        def case(name, cls, tool, **kwargs):
            fixture(name, **kwargs)
            runs[name] = tool
            expected_class[name] = cls

        case("agree_returned", AGREE, returns("hi\n"), out="hi\n")
        case("agree_silent", AGREE, returns(""), out="")
        case("agree_division", AGREE, aborts_with("div_zero", 4, "x\n"), out="x\n", aborts=True,
             stderr="division by zero\nagree_division.goose:4)\n")
        case("agree_index", AGREE, aborts_with("index_oob", 9), out="", aborts=True,
             stderr="index 2 out of bounds (length 2)\nagree_index.goose:9)\n")
        case("agree_user_abort", AGREE, aborts_with("user_abort", 3, "a\n"), out="a\n", aborts=True,
             stderr="custom message\nagree_user_abort.goose:3)\n")
        case("agree_debug_only", AGREE,
             aborts_with("int_overflow", 5, mode=DEBUG), out="", aborts=True, source=debug_define,
             stderr="integer overflow (debug): 127 + 1 at i8\nagree_debug_only.goose:5)\n")
        case("agree_both_modes", AGREE, {**returns("1\n"), **returns("1\n", DEBUG)},
             out="1\n", source=both_modes)
        case("agree_golden", AGREE, aborts_with("index_oob", 15, "70 2\n"), out="70 2\n", golden=True,
             expect=["expect", ["aborted", "index_oob", 15]])
        case("mismatch_stdout", MISMATCH, returns("2\n"), out="1\n")
        case("mismatch_kind", MISMATCH, aborts_with("assert", 4), out="", aborts=True,
             stderr="division by zero\nmismatch_kind.goose:4)\n")
        case("mismatch_line", MISMATCH, aborts_with("div_zero", 5), out="", aborts=True,
             stderr="division by zero\nmismatch_line.goose:4)\n")
        case("mismatch_returned_not_aborted", MISMATCH, returns(""), out="", aborts=True,
             stderr="assert failed\nmismatch_returned_not_aborted.goose:2)\n")
        case("mismatch_one_mode", MISMATCH, {**returns("1\n"), **returns("2\n", DEBUG)},
             out="1\n", source=both_modes)
        case("mismatch_fault", MISMATCH, {RELEASE: answer(["fault", "root_absent"], 4)}, out="")
        case("mismatch_malformed", MISMATCH, {RELEASE: answer(["malformed", "bad tag"], 2)}, out="")
        case("mismatch_rejected", MISMATCH, {RELEASE: answer(["rejected", "V-ROOT", "no"], 5)}, out="")
        case("unsupported_feature", UNSUPPORTED, {}, out="")
        exports["unsupported_feature"] = {"unsupported": "optional"}
        case("failure_export", HARNESS_FAILURE, {}, out="")
        exports["failure_export"] = {"fail": "internal compiler error"}
        case("failure_export_no_file", HARNESS_FAILURE, {}, out="")
        exports["failure_export_no_file"] = "nofile"
        case("failure_not_json", HARNESS_FAILURE, {RELEASE: {"raw": "not json\n"}}, out="")
        case("failure_two_lines", HARNESS_FAILURE, {RELEASE: {"raw": '["timeout",""]\n["timeout",""]\n',
                                                              "exit": 3}}, out="")
        case("failure_wrong_exit", HARNESS_FAILURE, {RELEASE: answer(["done", ["returned"], ""], 3)}, out="")
        case("failure_unknown_kind", HARNESS_FAILURE,
             {RELEASE: answer(["done", ["aborted", "mystery", 1], ""])}, out="")
        case("failure_unknown_tag", HARNESS_FAILURE, {RELEASE: answer(["crashed"], 1)}, out="")
        case("failure_no_expected_output", HARNESS_FAILURE, returns(""), out=None)
        case("failure_abort_without_location", HARNESS_FAILURE, aborts_with("assert", 1), out="",
             aborts=True, stderr="assert failed\n")
        case("failure_tool_crash", HARNESS_FAILURE, {}, out="")
        case("inconclusive_fuel", INCONCLUSIVE, {RELEASE: answer(["timeout", "part"], 3)}, out="")
        case("inconclusive_hang", INCONCLUSIVE, {RELEASE: {"sleep": 30}}, out="")

        fake_script = Path(temporary) / "script.json"

        def write_script(**extra):
            fake_script.write_text(json.dumps({"run": runs, "export": exports, **extra}))

        os.environ["FAKE_SCRIPT"] = str(fake_script)
        failures = []

        def check(label, condition):
            if os.environ.get("SEMANTICS_SELF_TEST_VERBOSE"):
                print(("ok   " if condition else "FAIL ") + label)
            if not condition:
                failures.append(label)

        fake_goose, fake_tool = FAKE / "goose.py", FAKE / "semantics.py"
        names = sorted(expected_class)
        write_script()
        stdout = io.StringIO()
        with contextlib.redirect_stdout(stdout):
            status = main(["--goose", str(fake_goose), "--semantics", str(fake_tool),
                           "--timeout", "2"], root=tree / "semantics")
        report = stdout.getvalue().splitlines()
        reported = {line.split(" ", 2)[1].rstrip(":"): line.split(" ", 1)[0] for line in report[:-1]}
        summary = json.loads(report[-1])
        for name in names:
            want = expected_class[name]
            got = reported.get(name, AGREE)
            check(f"{name}: expected {want}, got {got}", got == want)
        for cls in CLASSES:
            check(f"summary count for {cls}",
                  summary[cls] == sum(1 for name in names if expected_class[name] == cls))
        check("a failing run exits 1", status == 1)
        check("the summary is the last line", list(summary) == list(CLASSES))

        # An all-agreeing selection exits 0, and --case narrows the run.
        stdout = io.StringIO()
        with contextlib.redirect_stdout(stdout):
            status = main(["--goose", str(fake_goose), "--semantics", str(fake_tool), "--timeout", "2",
                           "--case", "agree_returned", "--case", "agree_golden"], root=tree / "semantics")
        check("agreeing cases exit 0", status == 0)
        check("--case selects exactly the named cases",
              json.loads(stdout.getvalue().splitlines()[-1])[AGREE] == 2)

        # The gir pipeline: native results are compared with the same expectation.
        gir_runs = {
            "agree_returned": {RELEASE: {"stdout": "hi\n"}},
            "agree_division": {RELEASE: {"stdout": "x\n", "exit": 1,
                                         "stderr": "goose runtime error: division by zero (agree_division.goose:4)\n"}},
            "agree_debug_only": {DEBUG: {"exit": 1, "stderr": "integer overflow (debug): 127 + 1 at i8 "
                                                              "(agree_debug_only.goose:5)\n"}},
            "mismatch_stdout": {RELEASE: {"stdout": "1\n"}},
            "mismatch_line": {RELEASE: {"exit": 1, "stderr": "division by zero (mismatch_line.goose:6)\n"}},
        }
        gir_class = {"agree_returned": AGREE, "agree_division": AGREE, "agree_debug_only": AGREE,
                     "mismatch_stdout": MISMATCH, "mismatch_line": MISMATCH}
        # The tool agrees with `mismatch_stdout` here, so only the pipeline differs.
        runs["mismatch_stdout"] = returns("1\n")
        runs["mismatch_line"] = aborts_with("div_zero", 4)
        selection = []
        for name, cls in gir_class.items():
            selection += ["--case", name]
        gir_runs["mismatch_stdout"] = {RELEASE: {"stdout": "other\n"}}
        write_script(gir_runs=gir_runs)
        stdout = io.StringIO()
        with contextlib.redirect_stdout(stdout):
            status = main(["--goose", str(fake_goose), "--semantics", str(fake_tool), "--timeout", "10",
                           "--pipeline", "gir", *selection], root=tree / "semantics")
        report = stdout.getvalue().splitlines()
        reported = {line.split(" ", 2)[1].rstrip(":"): line.split(" ", 1)[0] for line in report[:-1]}
        for name, want in gir_class.items():
            check(f"gir {name}: expected {want}, got {reported.get(name, AGREE)}",
                  reported.get(name, AGREE) == want)
        check("a pipeline mismatch exits 1", status == 1)

        # A compiler that rejects the flag is a harness failure, never a pass.
        write_script(gir="reject", gir_runs=gir_runs)
        stdout = io.StringIO()
        with contextlib.redirect_stdout(stdout):
            status = main(["--goose", str(fake_goose), "--semantics", str(fake_tool), "--timeout", "10",
                           "--pipeline", "gir", "--case", "agree_returned"], root=tree / "semantics")
        report = stdout.getvalue().splitlines()
        check("a rejected --pipeline is a harness-failure",
              status == 1 and json.loads(report[-1])[HARNESS_FAILURE] == 1
              and "unknown option" in stdout.getvalue())
        os.environ.pop("FAKE_SCRIPT")
    for failure in failures:
        print(f"self-test FAIL: {failure}")
    print(f"self-test: {len(names)} classified cases, {len(failures)} failure(s)")
    return 1 if failures else 0


def main(argv=None, root: Path = HERE) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--goose", type=Path)
    parser.add_argument("--semantics", type=Path, help="the reference tool (goose-semantics)")
    parser.add_argument("--profile", choices=["core-pilot"], default="core-pilot")
    parser.add_argument("--case", action="append", default=[], metavar="NAME")
    parser.add_argument("--pipeline", choices=["gir"],
                        help="also build and run each fixture through this compiler pipeline")
    parser.add_argument("--cc", default="clang", help="C compiler for --pipeline builds")
    parser.add_argument("--timeout", type=float, default=120, help="seconds per process")
    parser.add_argument("-j", "--jobs", type=int, default=min(8, os.cpu_count() or 1))
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args(argv)
    if args.self_test:
        return self_test()
    if args.goose is None or args.semantics is None:
        parser.error("--goose and --semantics are required")
    for tool in (args.goose, args.semantics):
        if not tool.is_file():
            parser.error(f"not a file: {tool}")
    if args.pipeline and not shutil.which(args.cc):
        parser.error(f"C compiler not found: {args.cc}")
    fixtures = discover(root)
    if args.case:
        known = {fixture.name for fixture in fixtures}
        unknown = [name for name in args.case if name not in known]
        if unknown:
            parser.error(f"unknown case: {', '.join(unknown)}")
        fixtures = [fixture for fixture in fixtures if fixture.name in args.case]
    counts = run_all(fixtures, args.goose.resolve(), args.semantics.resolve(), args.cc,
                     args.pipeline, args.timeout, args.jobs)
    return 0 if counts[AGREE] == sum(counts.values()) else 1


if __name__ == "__main__":
    try:
        sys.exit(main())
    except HarnessFailure as error:
        print(f"semantics: {error}", file=sys.stderr)
        sys.exit(2)
