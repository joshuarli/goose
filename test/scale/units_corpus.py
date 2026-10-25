#!/usr/bin/env python3
"""Every runnable fixture and sample, built from `--emit-units` and run.

  python test/scale/units_corpus.py --goose GOOSE [--only GLOB] [-j N] [--work DIR]

For each positive fixture the main runner builds with the native C compiler,
and each sample, the program is emitted as units (at -O0 and -O2, once more
at -O2 with --share, and with GS_DEBUG where the runner also builds that),
every unit is compiled and the units are linked with the runtime object the
way the runner compiles single-file C (same flags, same per-fixture defines),
the program is run, and its stdout, exit status and abort diagnostics are
checked against the fixture's expectations exactly as the runner does.

The five test/packages entry points go through `goose build --units` so the
driver builds and links their native package parts.

With `--pipeline gir` the programs are emitted by the IR pipeline instead
(`--pipeline gir --emit-units`), restricted to those it supports: a program it
reports as unsupported is skipped and counted. The pilot fixtures of
test/semantics are built too, in release and where they have one in debug,
and judged against their expectations as that harness judges the IR
pipeline's programs. There is no --share variant.

Skipped, and counted apart: parse-only fixtures, and programs outside
test/packages that link a native layer or C of their own. Prints one line per
failure and a final JSON line with the
pass, fail and skip counts. The two failures that also fail in single-file
mode (native_stack_overflow, render_reference_cycle) are expected and
reported as such; any other failure exits 1.
"""

import argparse
import concurrent.futures
from dataclasses import replace
import importlib.util
import fnmatch
import json
import os
import re
import shutil
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
sys.path.insert(0, str(ROOT / "test"))
sys.path.insert(0, str(ROOT / "scripts"))
import run_tests  # noqa: E402  (the runner's per-fixture rules)
import toolchain as tc  # noqa: E402

EXPECTED_FAILURES = {"native_stack_overflow", "render_reference_cycle"}
# Under --pipeline gir: programs whose lowered module the verifiers refuse because
# the validators do not yet accept them (a mutable slice over a `let` array, a
# function that always exits, a mutable reference bound to a read-only one).
EXPECTED_GIR_FAILURES = {"loop_shapes_countdown_abort", "never_returns_exit", "return_const_recursion"}
TESTS = ROOT / "test"
SAMPLES = ROOT / "samples"


def fixtures():
    tests = [f for f in sorted(TESTS.glob("*/*.goose"))
             if f.parent.name not in ("goose_in_goose", "lint", "errors", "errors_tc")
             and f.name != "lexer_tokens.goose"]
    return [("fixture", f) for f in tests] + [("sample", f) for f in sorted(SAMPLES.glob("*.goose"))]


def semantics_harness():
    """The conformance harness's own module, for its fixtures and verdicts."""
    spec = importlib.util.spec_from_file_location("semantics_harness", ROOT / "test" / "semantics" / "run_tests.py")
    module = importlib.util.module_from_spec(spec)
    sys.modules["semantics_harness"] = module
    spec.loader.exec_module(module)
    return module


def expected_pilot_outcome(harness, fixture):
    """Read abort expectations using the main test runner's stderr contract."""
    if not fixture.aborts or fixture.stderr is None:
        return harness.expected_outcome(fixture)

    markers = [line.strip() for line in fixture.stderr.read_text(encoding="utf-8").splitlines()
               if line.strip()]
    locations = [marker for marker in markers if harness.LOCATION_PATTERN.search(marker)]
    malformed_locations = [marker for marker in markers
                           if ".goose" in marker and not harness.LOCATION_PATTERN.search(marker)]
    if malformed_locations:
        raise harness.HarnessFailure(f"{fixture.name}.stderr has malformed source location")
    if not markers or all(harness.LOCATION_PATTERN.search(marker) for marker in markers):
        raise harness.HarnessFailure(f"{fixture.name}.stderr must include an abort diagnostic")

    # Main-runner expected stderr may assert the diagnostic text without naming
    # a source line. Preserve strict location checks whenever the sidecar has one.
    if not locations:
        fixture = replace(fixture, corpus=True)
    return harness.expected_outcome(fixture)


class Corpus:
    def __init__(self, goose, work, cc, native, pipeline=None):
        self.goose, self.work, self.cc, self.native = goose, work, cc, native
        self.pipeline = pipeline
        self.runtime = tc.GooseRuntime(goose, work / "runtime")
        self.harness = semantics_harness() if pipeline else None

    def supported(self, f, defines_goose):
        """Whether the IR pipeline takes the program; None if so, else why not."""
        code, out, err = tc.run_capture([str(self.goose), "--pipeline", self.pipeline, *defines_goose,
                                         "--check", str(f)])
        text = out + err
        marker = f"unsupported in pipeline {self.pipeline}: "
        if code != 0 and marker in text:
            return text.split(marker, 1)[1].split()[0]
        return None

    def pilot(self, fixture):
        """(status, detail) of a conformance-harness fixture built as units."""
        h = self.harness
        why = self.supported(fixture.source, [])
        if why:
            return "skip", f"unsupported in pipeline {self.pipeline}: {why}"
        outcome = expected_pilot_outcome(h, fixture)
        stdout = h.joined(fixture.out.read_bytes())
        for mode in fixture.modes:
            defines = ["-DGS_DEBUG=1"] if mode == h.DEBUG else []
            ccdefs = ["GS_DEBUG=1"] if mode == h.DEBUG else []
            for opt in (0, 2):
                d = self.work / f"pilot-{fixture.name}-{mode}-O{opt}"
                shutil.rmtree(d, ignore_errors=True)
                d.mkdir(parents=True)
                argv = [str(self.goose), "--pipeline", self.pipeline, *defines, "--emit-units",
                        str(d / "units"), str(fixture.source)]
                code, out, err = tc.run_capture(argv)
                if code != 0:
                    return "FAIL", f"emit {fixture.name} {mode}: {(out + err)[-300:]}"
                units = sorted((d / "units").glob("*.c"))
                exe = d / ("prog" + tc.EXE_SUFFIX)
                ok, log = self.cc.compile(units, exe, opt=opt, defines=ccdefs, strict_decls=True,
                                          runtime=self.runtime, extra=[f"-I{d / 'units'}"],
                                          log=d / "cc.log")
                if not ok:
                    return "FAIL", f"cc {fixture.name} {mode} O{opt}: " + "\n".join(log.splitlines()[:6])
                ran = h.run([exe], 120, cwd=d)
                verdict = h.judge_pipeline("units", fixture, mode, outcome, stdout,
                                           ran.returncode, ran.stdout, h.text(ran.stderr))
                if verdict.cls != h.AGREE:
                    return "FAIL", f"{fixture.name} O{opt}: {verdict.detail}"
        return "ok", ""

    def variants(self, kind, f, line):
        """(label, goose flags, cc defines, optimization) builds of a program."""
        if self.pipeline:
            out = [("O0", ["--pipeline", self.pipeline], [], 0), ("O2", ["--pipeline", self.pipeline], [], 2)]
            if kind == "fixture" and run_tests.debug_fixture(f, line):
                out.append(("O2-debug", ["--pipeline", self.pipeline, "-DGS_DEBUG=1"], ["GS_DEBUG=1"], 2))
            return out
        out = [("O0", ["-O0"], [], 0), ("O2", ["-O2"], [], 2), ("O2-share", ["-O2", "--share"], [], 2)]
        if kind == "fixture" and run_tests.debug_fixture(f, line):
            out.append(("O2-debug", ["-O2"], ["GS_DEBUG=1"], 2))
        return out

    def check(self, name, aborts, code, out, err, what):
        if tc.sanitizer_failure(err):
            return f"sanitizer {what}"
        if (aborts and code == 0) or (not aborts and code != 0):
            return f"run {what} (exit {code}): {err[-200:]}"
        stderr_file = TESTS / "expected" / f"{name}.stderr"
        if aborts and not stderr_file.exists():
            return f"missing expected-stderr {what}"
        if stderr_file.exists():
            markers = [l.strip() for l in tc.decode(stderr_file.read_bytes()).splitlines() if l.strip()]
            if not markers or any(m not in err for m in markers):
                return f"expected-stderr {what}: {err[-200:]}"
        return None

    def one(self, kind, f):
        """(status, detail): 'ok', 'skip: why' or 'FAIL: why'."""
        text = f.read_text(encoding="utf-8")
        line = run_tests.first_line(f)
        if kind == "fixture":
            if "parse-only" in line:
                return "skip", "parse-only fixture"
            modules = run_tests.native_modules(f, self.native)
            name = f.stem
            sidecar = f.with_suffix(".build").exists() or f.parent.name == "packages"
            defines_goose = ["-D" + d for d in run_tests.runtime_defines(f)]
            expfile = TESTS / "expected" / f"{name}.out"
            progargs, infile, cwd, include = [], None, None, []
        else:
            modules = tc.native_imports(text)
            name = re.sub(r"^\d+_", "", f.stem)
            sidecar = f.with_suffix(".build").exists()
            defines_goose = []
            expfile = SAMPLES / "expected" / f"{name}.out"
            argfile = SAMPLES / "data" / f"{name}.args"
            progargs = argfile.read_text(encoding="utf-8").split() if argfile.exists() else []
            infile = SAMPLES / "data" / f"{name}.stdin"
            infile = infile if infile.exists() else None
            cwd = SAMPLES
            header = SAMPLES / f"{name}.h"
            include = ["--include", str(header)] if header.exists() else []
        package_driver = kind == "fixture" and f.parent.name == "packages"
        if (modules or sidecar) and not package_driver:
            return "skip", "links a native layer or C of its own"
        aborts = kind == "fixture" and (TESTS / "expected" / f"{name}.aborts").exists()
        if self.pipeline:
            why = self.supported(f, defines_goose + include)
            if why:
                return "skip", f"unsupported in pipeline {self.pipeline}"
        for label, flags, defines, opt in self.variants(kind, f, line):
            d = self.work / f"{kind}-{name}-{label}"
            shutil.rmtree(d, ignore_errors=True)
            d.mkdir(parents=True)
            what = f"{label} {f.name}"
            if package_driver:
                exe = d / ("prog" + tc.EXE_SUFFIX)
                argv = ([str(self.goose), "build", "--units"] + flags +
                        defines_goose + ["-D" + define for define in defines] +
                        ["--cc", self.cc.cc, "-o", str(exe), str(f)])
                env = dict(os.environ, GOOSE_HOME=str(d / "home"))
                built = subprocess.run(argv, capture_output=True, text=True, errors="replace", env=env)
                code, out, err = built.returncode, built.stdout, built.stderr
                if code != 0:
                    return "FAIL", f"build {what}: {(out + err)[-300:]}"
                code, out, err = tc.run_capture([str(exe)] + progargs, cwd=cwd, stdin_path=infile)
                bad = self.check(name, aborts, code, out, err, what)
                if bad:
                    return "FAIL", bad
                if expfile.exists():
                    want = tc.decode(expfile.read_bytes())
                    if run_tests.joined(out) != run_tests.joined(want):
                        return "FAIL", f"expected-output {what}"
                elif kind == "fixture":
                    return "FAIL", f"missing expected-output {what}"
                continue
            argv = [str(self.goose)] + defines_goose + flags + include + ["--emit-units", str(d / "units"), str(f)]
            code, out, err = tc.run_capture(argv)
            if code != 0:
                return "FAIL", f"emit {what}: {(out + err)[-300:]}"
            units = sorted((d / "units").glob("*.c"))
            exe = d / ("prog" + tc.EXE_SUFFIX)
            # A program with C of its own has its runtime in its native-support
            # unit and links no runtime object.
            native = (d / "units" / "native.c").exists()
            ok, log = self.cc.compile(units, exe, opt=opt, defines=defines, strict_decls=True,
                                      runtime=None if native else self.runtime,
                                      extra=[f"-I{d / 'units'}"],
                                      log=d / "cc.log")
            if not ok:
                return "FAIL", f"cc {what}: " + "\n".join(log.splitlines()[:6])
            code, out, err = tc.run_capture([str(exe)] + progargs, cwd=cwd, stdin_path=infile)
            bad = self.check(name, aborts, code, out, err, what)
            if bad:
                return "FAIL", bad
            if expfile.exists():
                want = tc.decode(expfile.read_bytes())
                if run_tests.joined(out) != run_tests.joined(want):
                    return "FAIL", f"expected-output {what}"
            elif kind == "fixture":
                return "FAIL", f"missing expected-output {what}"
        return "ok", ""


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--goose", required=True)
    ap.add_argument("--only", action="append", default=[], metavar="GLOB",
                    help="run only fixtures named category/stem or samples/name matching GLOB")
    ap.add_argument("-j", "--jobs", type=int, default=min(os.cpu_count() or 1, 16))
    ap.add_argument("--pipeline", choices=["gir"], help="emit the units through this compiler pipeline")
    ap.add_argument("--work", help="scratch directory (default: .work/units_corpus)")
    a = ap.parse_args()
    work = Path(a.work).resolve() if a.work else ROOT / ".work" / "units_corpus"
    shutil.rmtree(work, ignore_errors=True)
    work.mkdir(parents=True)
    os.environ["GOOSE_HOME"] = str(work / "home")
    goose = Path(a.goose).resolve()
    cc = tc.test_cc("native")
    builtin = tc.builtin_modules(goose)
    native = {m: m in builtin for m in tc.NATIVE_MODULES}
    corpus = Corpus(goose, work, cc, native, a.pipeline)
    items = []
    for kind, f in fixtures():
        label = f"{f.parent.name}/{f.stem}" if kind == "fixture" else f"samples/{f.stem}"
        if not a.only or any(fnmatch.fnmatchcase(label, g) for g in a.only):
            items.append((kind, f, label))
    if a.pipeline:
        for fx in corpus.harness.discover(ROOT / "test" / "semantics"):
            label = f"semantics/{fx.name}"
            if not a.only or any(fnmatch.fnmatchcase(label, g) for g in a.only):
                items.append(("pilot", fx, label))
    counts = {"ok": 0, "fail": 0, "expected_fail": 0, "skip": 0}
    skips = {}
    unexpected = []

    def run(item):
        kind, f, label = item
        try:
            return item, (corpus.pilot(f) if kind == "pilot" else corpus.one(kind, f))
        except Exception as e:  # a harness error is a failure of that program
            return item, ("FAIL", f"harness: {e!r}")

    with concurrent.futures.ThreadPoolExecutor(a.jobs) as pool:
        for (kind, f, label), (status, detail) in pool.map(run, items):
            if status == "ok":
                counts["ok"] += 1
            elif status == "skip":
                counts["skip"] += 1
                skips[detail] = skips.get(detail, 0) + 1
            elif kind != "pilot" and f.stem in (EXPECTED_GIR_FAILURES if a.pipeline else EXPECTED_FAILURES):
                counts["expected_fail"] += 1
                print(f"expected failure {label}: {detail[:100]}")
            else:
                counts["fail"] += 1
                unexpected.append(label)
                print(f"FAIL {label}: {detail}")
    print(json.dumps({"compiled": a.goose, "programs": len(items), **counts, "skips": skips}))
    return 1 if counts["fail"] else 0


if __name__ == "__main__":
    sys.exit(main())
