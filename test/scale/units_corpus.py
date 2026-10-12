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

Skipped, and counted apart: parse-only fixtures, and programs that link a
native layer or C of their own, which need the driver's link step, not
written yet. Prints one line per failure and a final JSON line with the
pass, fail and skip counts. The two failures that also fail in single-file
mode (native_stack_overflow, render_reference_cycle) are expected and
reported as such; any other failure exits 1.
"""

import argparse
import concurrent.futures
import fnmatch
import json
import os
import re
import shutil
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
sys.path.insert(0, str(ROOT / "test"))
sys.path.insert(0, str(ROOT / "scripts"))
import run_tests  # noqa: E402  (the runner's per-fixture rules)
import toolchain as tc  # noqa: E402

EXPECTED_FAILURES = {"native_stack_overflow", "render_reference_cycle"}
TESTS = ROOT / "test"
SAMPLES = ROOT / "samples"


def fixtures():
    tests = [f for f in sorted(TESTS.glob("*/*.goose"))
             if f.parent.name not in ("goose_in_goose", "lint", "errors", "errors_tc")
             and f.name != "lexer_tokens.goose"]
    return [("fixture", f) for f in tests] + [("sample", f) for f in sorted(SAMPLES.glob("*.goose"))]


class Corpus:
    def __init__(self, goose, work, cc, native):
        self.goose, self.work, self.cc, self.native = goose, work, cc, native
        self.runtime = tc.GooseRuntime(goose, work / "runtime")

    def variants(self, kind, f, line):
        """(label, goose flags, cc defines, optimization) builds of a program."""
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
        if modules or sidecar:
            return "skip", "links a native layer or C of its own"
        aborts = kind == "fixture" and (TESTS / "expected" / f"{name}.aborts").exists()
        for label, flags, defines, opt in self.variants(kind, f, line):
            d = self.work / f"{kind}-{name}-{label}"
            shutil.rmtree(d, ignore_errors=True)
            d.mkdir(parents=True)
            what = f"{label} {f.name}"
            argv = [str(self.goose)] + defines_goose + flags + include + ["--emit-units", str(d / "units"), str(f)]
            code, out, err = tc.run_capture(argv)
            if code != 0:
                return "FAIL", f"emit {what}: {(out + err)[-300:]}"
            units = sorted((d / "units").glob("*.c"))
            exe = d / ("prog" + tc.EXE_SUFFIX)
            ok, log = self.cc.compile(units, exe, opt=opt, defines=defines, strict_decls=True,
                                      runtime=self.runtime, extra=[f"-I{d / 'units'}"],
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
    ap.add_argument("--work", help="scratch directory (default: .work/units_corpus)")
    a = ap.parse_args()
    work = Path(a.work) if a.work else ROOT / ".work" / "units_corpus"
    shutil.rmtree(work, ignore_errors=True)
    work.mkdir(parents=True)
    os.environ["GOOSE_HOME"] = str(work / "home")
    goose = Path(a.goose).resolve()
    cc = tc.test_cc("native")
    builtin = tc.builtin_modules(goose)
    native = {m: m in builtin for m in tc.NATIVE_MODULES}
    corpus = Corpus(goose, work, cc, native)
    items = []
    for kind, f in fixtures():
        label = f"{f.parent.name}/{f.stem}" if kind == "fixture" else f"samples/{f.stem}"
        if not a.only or any(fnmatch.fnmatchcase(label, g) for g in a.only):
            items.append((kind, f, label))
    counts = {"ok": 0, "fail": 0, "expected_fail": 0, "skip": 0}
    skips = {}
    unexpected = []

    def run(item):
        kind, f, label = item
        try:
            return item, corpus.one(kind, f)
        except Exception as e:  # a harness error is a failure of that program
            return item, ("FAIL", f"harness: {e!r}")

    with concurrent.futures.ThreadPoolExecutor(a.jobs) as pool:
        for (kind, f, label), (status, detail) in pool.map(run, items):
            if status == "ok":
                counts["ok"] += 1
            elif status == "skip":
                counts["skip"] += 1
                skips[detail] = skips.get(detail, 0) + 1
            elif f.stem in EXPECTED_FAILURES:
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
