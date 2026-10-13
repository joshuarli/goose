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

With `--corpus` the same checks run over every positive fixture of the main
runner and every sample instead (see `discover_corpus`): a program the exporter
refuses is counted by feature id and not listed, and exit status 0 means no
exported program mismatched, failed or ran out of time.

Run `python3 test/semantics/run_tests.py --self-test` to check the harness
against the fake tools in `fake/`.
"""

import argparse
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass, field
import importlib.util
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


# ("returned",) | ("aborted", kind, line) | ("exited", code). A corpus fixture
# whose diagnostic file names no source location expects an abort at line None,
# which agrees with an abort of that kind anywhere.
Outcome = tuple


@dataclass(frozen=True)
class Fixture:
    name: str
    source: Path
    out: Path
    stderr: Path | None
    aborts: bool
    expect: Path | None
    modes: tuple[str, ...]
    # Corpus programs are the main runner's, whose expectations were not written
    # for this harness: extra compiler arguments, the -D defines of the fixture,
    # whether an expected stdout exists, and whether an abort's line is known.
    args: tuple[str, ...] = ()
    defines: tuple[str, ...] = ()
    corpus: bool = False

    @property
    def label(self) -> str:
        return self.name.replace("/", "_")


@dataclass(frozen=True)
class Verdict:
    cls: str
    detail: str = ""
    exported: bool = False


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


def load_main_runner(repo: Path):
    """The main runner's module, for its first-line directives and expectation rules."""
    spec = importlib.util.spec_from_file_location("main_runner", ROOT / "test" / "run_tests.py")
    module = importlib.util.module_from_spec(spec)
    sys.modules["main_runner"] = module
    spec.loader.exec_module(module)
    return module


def discover_corpus(repo: Path, builtin: list[str]) -> list[Fixture]:
    """Every program of the main runner's positive fixtures and of `samples/`.

    Skipped as the main runner skips them: the Goose-in-Goose, lint and
    rejection directories, the lexer token fixture, `parse-only` fixtures, and
    programs using a native module the compiler was not built with. A sample
    that reads standard input or takes arguments is skipped too, since the
    reference tool runs a program with neither. Expectations are the main
    runner's: `expected/NAME.out`, `.aborts` and `.stderr`.
    """
    runner = load_main_runner(repo)
    tests = repo / "test"
    expected = tests / "expected"
    fixtures = []
    for source in sorted(tests.glob("*/*.goose")):
        if (source.parent.name in ("goose_in_goose", "lint", "errors", "errors_tc")
                or source.name == "lexer_tokens.goose"):
            continue
        line = runner.first_line(source)
        modules = runner.native_modules(source, {m: True for m in runner.tc.NATIVE_MODULES})
        if ("parse-only" in line or runner.error_markers(source)
                or any(module not in builtin for module in modules)):
            continue
        name = source.stem
        stderr = expected / f"{name}.stderr"
        defines = tuple(d for d in runner.runtime_defines(source) if d != "GS_DEBUG=1")
        fixtures.append(Fixture(
            f"{source.parent.name}/{name}", source, expected / f"{name}.out",
            stderr if stderr.exists() else None, (expected / f"{name}.aborts").exists(), None,
            (RELEASE, DEBUG) if runner.debug_fixture(source, line) and RELEASE in modes_for(source)
            else modes_for(source), defines=defines, corpus=True))
    for source in sorted((repo / "samples").glob("*.goose")):
        name = re.sub(r"^\d+_", "", source.stem)
        data = repo / "samples" / "data"
        modules = runner.tc.native_imports(source.read_text(encoding="utf-8"))
        if (data / f"{name}.stdin").exists() or (data / f"{name}.args").exists() \
                or any(module not in builtin for module in modules):
            continue
        header = repo / "samples" / f"{name}.h"
        fixtures.append(Fixture(
            f"samples/{name}", source, repo / "samples" / "expected" / f"{name}.out", None, False,
            None, (RELEASE,), args=("--include", str(header)) if header.exists() else (),
            corpus=True))
    names = [fixture.name for fixture in fixtures]
    duplicates = sorted({name for name in names if names.count(name) > 1})
    if duplicates:
        raise HarnessFailure(f"corpus names are not unique: {', '.join(duplicates)}")
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
    if len(lines) != 1 and not (fixture.corpus and not lines):
        raise HarnessFailure(f"{fixture.name}.stderr must name exactly one NAME.goose:LINE) location")
    line = lines[0] if lines else None
    return ("aborted", abort_kind([m for m in markers if not LOCATION_PATTERN.search(m)]), line)


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


def export(goose: Path, fixture: Fixture, work: Path, timeout: float) -> tuple[Path | None, str | None]:
    """Export one program. Returns (core file, None) or (None, unsupported feature id)."""
    core = work / "program.core"
    source = fixture.source
    done = run([goose, *fixture.args, *map("-D{}".format, fixture.defines), "--emit-core", core,
                "--check", source], timeout)
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


def validate_result(tool: Path, core: Path, timeout: float) -> tuple:
    """Run the tool's validator: ("valid",) for `["ok"]` with exit 0, else the tool's own answer."""
    done = run([tool, "validate", core], timeout)
    out = text(done.stdout)
    if done.returncode == 0 and out.strip() == '["ok"]':
        return ("valid",)
    return parse_tool_answer(done.returncode, out, text(done.stderr))


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


def outcomes_agree(got: Outcome, expected: Outcome) -> bool:
    if got[0] == "aborted" and expected[0] == "aborted" and expected[2] is None:
        return got[1] == expected[1]
    # A fixture without an explicit expectation only says the process ends
    # with status 0, which `exit(0)` and returning from main both do.
    if expected == ("returned",) and got == ("exited", 0):
        return True
    return got == expected


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
    if not outcomes_agree(answer[1], outcome):
        problems.append(f"outcome {describe(answer[1])}, expected {describe(outcome)}")
    if joined(answer[2]) != stdout:
        problems.append(f"stdout {joined(answer[2])!r}, expected {stdout!r}")
    if problems:
        return Verdict(MISMATCH, f"[{mode}] " + "; ".join(problems))
    return Verdict(AGREE)


def build_and_run_pipeline(goose: Path, cc: str, pipeline: str, fixture: Fixture, mode: str,
                           work: Path, timeout: float) -> list[tuple[str, int, str, str]]:
    """Build the fixture through the named compiler pipeline and run it: natively
    at -O0 and -O2 of the C compiler, and in process through --jit. Returns each
    run's label, exit status, standard output and standard error."""
    defines = ["-DGS_DEBUG=1"] if mode == DEBUG else []
    cfile = work / f"{pipeline}-{mode}.c"
    extra = [*fixture.args, *map("-D{}".format, fixture.defines)]
    cdefines = [*defines, *map("-D{}".format, fixture.defines)]
    built = run([goose, "--pipeline", pipeline, *extra, *defines, "--standalone", "-o", cfile,
                 fixture.source], timeout)
    if built.returncode != 0:
        raise HarnessFailure(f"{pipeline} pipeline build failed (exit {built.returncode}): "
                             f"{text(built.stderr).strip()[:300]}")
    runs = []
    for opt in ("-O0", "-O2"):
        program = work / f"{pipeline}-{mode}{opt}"
        compiled = run([cc, opt, *cdefines, cfile, "-o", program, "-lm", "-pthread"], timeout)
        if compiled.returncode != 0:
            raise HarnessFailure(f"C compiler rejected the {pipeline} output at {opt}: "
                                 f"{text(compiled.stderr).strip()[:300]}")
        ran = run([program], timeout, cwd=work)
        runs.append((opt, ran.returncode, text(ran.stdout), text(ran.stderr)))
    ran = run([goose, "--pipeline", pipeline, *extra, *defines, "--jit", fixture.source], timeout, cwd=work)
    runs.append(("jit", ran.returncode, text(ran.stdout), text(ran.stderr)))
    return runs


# What the runtime's diagnostic says for each kind of abort, as far as it says it.
ABORT_TEXT = {
    "div_zero": "division by zero",
    "div_overflow": "integer overflow in division",
    "index_oob": "out of bounds",
    "slice_oob": "slice bounds out of range",
    "assert": "assert failed",
    "int_overflow": "overflow",
    "cast_range": "",
}


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
    if outcome[0] == "aborted":
        # The diagnostic names the kind of abort and the line of the operation.
        # An abort of unknown line (a corpus fixture) may also lack its location,
        # as a native stack overflow does.
        last = err.strip().splitlines()[-1] if err.strip() else ""
        match = re.search(r"goose runtime error: (.*) \((.*):(\d+)\)\s*$", last)
        if match is None and outcome[2] is None:
            match = re.search(r"goose runtime error: (.*?)()()\s*$", last)
        if match is None:
            problems.append(f"no abort diagnostic in stderr {err.strip()[-120:]!r}")
        else:
            if outcome[2] is not None and int(match[3]) != outcome[2]:
                problems.append(f"abort at line {match[3]}, expected {outcome[2]}")
            text_of = ABORT_TEXT.get(outcome[1])
            if text_of and text_of not in match[1]:
                problems.append(f"abort text {match[1]!r}, expected one with {text_of!r}")
    if problems:
        return Verdict(MISMATCH, f"[{mode}] {pipeline}: " + "; ".join(problems))
    return Verdict(AGREE)


def run_case(fixture: Fixture, goose: Path, tool: Path, cc: str, pipeline: str | None,
             scratch: Path, timeout: float) -> Verdict:
    work = Path(tempfile.mkdtemp(prefix=f"{fixture.label}-", dir=scratch))
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
    core = guarded(lambda: export(goose, fixture, work, timeout))
    if core is None:
        return verdicts[0]
    core_file, feature = core
    if feature is not None:
        return Verdict(UNSUPPORTED, feature)
    for mode in fixture.modes:
        def check_validation():
            answer = validate_result(tool, core_file, timeout)
            if answer[0] != "valid":
                verdicts.append(Verdict(MISMATCH, f"[{mode}] validation answered "
                                                  f"{json.dumps(list(answer))} for a program the compiler accepts"))
        if mode == fixture.modes[0]:
            guarded(check_validation)

        def check_tool():
            answer = tool_result(tool, core_file, mode, timeout)
            verdicts.append(judge_tool(fixture, mode, answer, outcome, stdout))
        guarded(check_tool)
        if pipeline is not None:
            def check_pipeline():
                for label, code, out, err in build_and_run_pipeline(goose, cc, pipeline, fixture, mode,
                                                                    work, timeout):
                    verdicts.append(judge_pipeline(f"{pipeline} {label}", fixture, mode, outcome, stdout,
                                                   code, out, err))
            guarded(check_pipeline)
    worst = max(verdicts, key=lambda verdict: SEVERITY[verdict.cls])
    if worst.cls == AGREE:
        return Verdict(AGREE, exported=True)
    return Verdict(worst.cls, "; ".join(v.detail for v in verdicts if v.cls == worst.cls),
                   exported=True)


def run_all(fixtures: list[Fixture], goose: Path, tool: Path, cc: str, pipeline: str | None,
            timeout: float, jobs: int, corpus: bool = False) -> dict:
    """Run every case and print the non-agreeing ones and the JSON summary line.

    In corpus mode unsupported programs are not listed, and the summary adds the
    number of exported programs and the unsupported feature ids with their counts.
    """
    scratch_root = ROOT / "build" / "semantics"
    scratch_root.mkdir(parents=True, exist_ok=True)
    counts = dict.fromkeys(CLASSES, 0)
    features: Counter = Counter()
    with tempfile.TemporaryDirectory(prefix="run-", dir=scratch_root) as scratch:
        with ThreadPoolExecutor(max_workers=jobs) as pool:
            verdicts = list(pool.map(
                lambda fixture: run_case(fixture, goose, tool, cc, pipeline, Path(scratch), timeout),
                fixtures))
    for fixture, verdict in zip(fixtures, verdicts):
        counts[verdict.cls] += 1
        if verdict.cls == UNSUPPORTED:
            features[verdict.detail] += 1
        if verdict.cls != AGREE and not (corpus and verdict.cls == UNSUPPORTED):
            print(f"{verdict.cls} {fixture.name}: {verdict.detail}")
    summary = dict(counts)
    if corpus:
        summary["exported"] = sum(verdict.exported for verdict in verdicts)
        summary["unsupported_features"] = dict(features.most_common())
    print(json.dumps(summary))
    return summary


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
            "agree_debug_only": {DEBUG: {"exit": 1, "stderr": "goose runtime error: integer overflow (debug): 127 + 1 at i8 "
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

        # Corpus mode: the main runner's fixtures and the samples, with its skip rules.
        repo = Path(temporary) / "repo"
        for sub in ("test/core", "test/lint", "test/errors_tc", "test/goose_in_goose", "test/gfx",
                    "test/expected", "samples/expected", "samples/data"):
            (repo / sub).mkdir(parents=True)
        corpus_runs, corpus_exports, corpus_validate = {}, {}, {}
        corpus_class = {}

        def program(path, name, cls, tool, out="", first="", **expected):
            (repo / path / f"{name}.goose").write_text(first + "fn main() {}\n")
            out_dir = repo / "samples" / "expected" if path == "samples" else repo / "test" / "expected"
            stem = re.sub(r"^\d+_", "", name) if path == "samples" else name
            if cls is not None:
                (out_dir / f"{stem}.out").write_text(out)
            for suffix, content in expected.items():
                (out_dir / f"{stem}.{suffix}").write_text(content)
            corpus_runs[name] = tool
            if cls is not None:
                corpus_class[name] = cls

        program("test/core", "plain", AGREE, returns(""))
        program("test/core", "debug_only", AGREE, returns("1\n", DEBUG), "1\n",
                first="// runtime-define: GS_DEBUG=1\n")
        program("test/core", "both_modes", AGREE, {**returns("2\n"), **returns("2\n", DEBUG)}, "2\n",
                first="// runtime-debug\n")
        program("test/core", "abort_without_location", AGREE, aborts_with("div_zero", 7, "a\n"), "a\n",
                aborts="", stderr="division by zero\n")
        program("test/core", "abort_wrong_kind", MISMATCH, aborts_with("assert", 7), "",
                aborts="", stderr="division by zero\n")
        program("test/core", "wrong_output", MISMATCH, returns("x\n"), "y\n")
        program("test/core", "invalid_export", MISMATCH, returns(""))
        corpus_validate["invalid_export"] = {"rejected": ["V-TYPE", "bad"]}
        program("test/core", "out_of_fuel", INCONCLUSIVE, {RELEASE: answer(["timeout", ""], 3)})
        for name, feature in (("uses_struct", "struct"), ("uses_struct_again", "struct"),
                              ("uses_float", "float")):
            program("test/core", name, UNSUPPORTED, {})
            corpus_exports[name] = {"unsupported": feature}
        # Skipped before anything runs: a call to the fake tools would be a failure.
        program("test/core", "parse_only_case", None, {}, first="// parse-only\n")
        program("test/core", "lexer_tokens", None, {})
        program("test/lint", "lint_input", None, {})
        program("test/errors_tc", "rejected_input", None, {})
        program("test/goose_in_goose", "bootstrap_part", None, {})
        program("test/gfx", "needs_gfx", None, {})
        program("samples", "01_tour", AGREE, returns("tour\n"), "tour\n")
        program("samples", "02_header", AGREE, returns(""))
        (repo / "samples" / "header.h").write_text("")
        program("samples", "03_calc", None, {})
        (repo / "samples" / "data" / "calc.stdin").write_text("1\n")
        write_script(run=corpus_runs, export=corpus_exports, validate=corpus_validate)
        stdout = io.StringIO()
        with contextlib.redirect_stdout(stdout):
            status = main(["--goose", str(fake_goose), "--semantics", str(fake_tool), "--timeout", "5",
                           "--corpus"], root=tree / "semantics", repo=repo)
        report = stdout.getvalue().splitlines()
        summary = json.loads(report[-1])
        listed = {line.split(" ", 2)[1].rstrip(":"): line.split(" ", 1)[0] for line in report[:-1]}
        for cls in (MISMATCH, INCONCLUSIVE):
            check(f"corpus {cls} count",
                  summary[cls] == sum(1 for v in corpus_class.values() if v == cls))
        check("corpus agree count", summary[AGREE] == 6)
        check("corpus unsupported count", summary[UNSUPPORTED] == 3)
        check("corpus exported count", summary["exported"] == 10)
        check("corpus feature histogram", summary["unsupported_features"] == {"struct": 2, "float": 1})
        check("corpus lists no unsupported program", UNSUPPORTED not in listed.values())
        check("corpus lists each non-agreeing exported program",
              sorted(listed) == ["core/abort_wrong_kind", "core/invalid_export", "core/out_of_fuel",
                                 "core/wrong_output"])
        check("corpus exit status is nonzero on a mismatch", status == 1)
        check("no skipped program was run", summary[HARNESS_FAILURE] == 0)

        # Unsupported programs alone do not fail the corpus.
        stdout = io.StringIO()
        with contextlib.redirect_stdout(stdout):
            status = main(["--goose", str(fake_goose), "--semantics", str(fake_tool), "--timeout", "5",
                           "--corpus", "--case", "plain", "--case", "core/uses_struct",
                           "--case", "samples/tour"], root=tree / "semantics", repo=repo)
        check("corpus without mismatches exits 0", status == 0)
        check("--case selects corpus programs by stem or name",
              json.loads(stdout.getvalue().splitlines()[-1])["exported"] == 2)
        os.environ.pop("FAKE_SCRIPT")
    for failure in failures:
        print(f"self-test FAIL: {failure}")
    print(f"self-test: {len(names)} classified cases, {len(failures)} failure(s)")
    return 1 if failures else 0


def main(argv=None, root: Path = HERE, repo: Path = ROOT) -> int:
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
    parser.add_argument("--corpus", action="store_true",
                        help="check every positive fixture of the main runner and every sample")
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
    goose = args.goose.resolve()
    if args.corpus:
        builtin = load_main_runner(repo).tc.builtin_modules(goose)
        fixtures = discover_corpus(repo, builtin)
    else:
        fixtures = discover(root)
    if args.case:
        known = {fixture.name for fixture in fixtures} | {fixture.name.split("/")[-1] for fixture in fixtures}
        unknown = [name for name in args.case if name not in known]
        if unknown:
            parser.error(f"unknown case: {', '.join(unknown)}")
        fixtures = [fixture for fixture in fixtures
                    if fixture.name in args.case or fixture.name.split("/")[-1] in args.case]
    summary = run_all(fixtures, goose, args.semantics.resolve(), args.cc,
                      args.pipeline, args.timeout, args.jobs, args.corpus)
    if args.corpus:
        return int(any(summary[cls] for cls in (MISMATCH, HARNESS_FAILURE, INCONCLUSIVE)))
    return 0 if summary[AGREE] == sum(summary[cls] for cls in CLASSES) else 1


if __name__ == "__main__":
    try:
        sys.exit(main())
    except HarnessFailure as error:
        print(f"semantics: {error}", file=sys.stderr)
        sys.exit(2)
