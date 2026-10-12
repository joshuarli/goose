#!/usr/bin/env python3
"""Source edits against the single-file build path.

  python test/scale/edit_matrix.py --goose GOOSE --workload synthetic
         [--case ID ...] [--work DIR]

For each case the synthetic family is generated twice, as it is and after the
edit; each is compiled to C at -O2, built with the native C compiler as the
main test runner does, and run. The run's output, or the compile failure the
edit is expected to cause, is checked against what the generator states. The
emitted C of the two programs is split into functions and compared by source
function, with specialization numbers and source line numbers masked, and
the set of source functions whose code changed is compared with the set the
edit is expected to change.

Prints one JSON object per case, then a summary object. Fields that need
code-generation units or a build store, which do not exist yet, are null so
that later work fills them in. Exits 1 if any case fails.

The Aincrad3 workload is not implemented here: `--workload aincrad3
--source DIR` exits 2.
"""

import argparse
import json
import os
import re
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(ROOT / "scripts"))
import cfuncs  # noqa: E402
import edits  # noqa: E402
import gen  # noqa: E402
import toolchain as tc  # noqa: E402

# The family every case is cut from: shareable, distinct and edit-target
# members, small enough that a case takes a few seconds.
FAMILY = dict(helpers=1, contexts=2, types=gen.INT_TYPES[:1], shareable=1, root_params=2, distinct=True,
              edit_targets=True)

# Fields of the per-case record that need features the compiler lacks. They
# are present so that a later change fills them in without a new layout.
NOT_YET = ("frontend_phases", "implementation_digests_changed", "units_changed",
           "units_per_native_invocation", "objects_reused", "objects_missed", "link_skipped",
           "native_compiler_peak_rss")


def measured(argv, log_dir, name):
    """(exit code, stdout, stderr, wall ms, CPU ms, peak RSS bytes) of one
    process; the last three are None where the platform cannot say."""
    if tc.IS_WINDOWS:
        start = time.perf_counter()
        code, out, err = tc.run_capture(argv)
        return code, out, err, (time.perf_counter() - start) * 1000, None, None
    outf, errf = log_dir / f"{name}.stdout", log_dir / f"{name}.stderr"
    with open(outf, "wb") as fo, open(errf, "wb") as fe:
        start = time.perf_counter()
        p = subprocess.Popen([str(a) for a in argv], stdout=fo, stderr=fe)
        _, status, usage = os.wait4(p.pid, 0)
        ms = (time.perf_counter() - start) * 1000
        p.returncode = os.waitstatus_to_exitcode(status)
    cpu = (usage.ru_utime + usage.ru_stime) * 1000
    peak = usage.ru_maxrss * (1 if tc.IS_MACOS else 1024)
    return (p.returncode, tc.decode(outf.read_bytes()), tc.decode(errf.read_bytes()), ms, cpu, peak)


class Build:
    """One program compiled to C, built and run."""

    def __init__(self, label, directory, goose, cc, runtime, edit):
        self.label, self.dir, self.edit = label, directory, edit
        self.write(edit)
        self.expected = json.loads((directory / "expected.json").read_text(encoding="utf-8"))
        out = directory / "main.out"
        self.want_output = out.read_text(encoding="utf-8") if out.exists() else None
        self.cfile = directory / "main.c"
        self.cfile.unlink(missing_ok=True)
        self.dir_text = str(directory)
        (self.exit, so, se, self.wall_ms, self.cpu_ms, self.peak) = measured(
            [goose, "-O2", "-o", self.cfile, directory / "main.goose"], directory, "goose")
        self.log = so + se
        self.contexts = None
        m = re.search(r"typechecked ok: (\d+) specialization", self.log)
        if m:
            self.contexts = int(m.group(1))
        self.warnings = self.log.count(": warning:")
        self.c_text = self.cfile.read_text(encoding="utf-8") if self.exit == 0 else None
        self.output = self.native_ms = None
        self.build_failure = None
        if self.c_text is not None:
            self.run_native(cc, runtime)

    def write(self, edit):
        source, output, expected, files = gen.build(**FAMILY, edit=edit)
        self.dir.mkdir(parents=True, exist_ok=True)
        (self.dir / "main.goose").write_text(source, encoding="utf-8", newline="\n")
        if output is not None:
            (self.dir / "main.out").write_text(output, encoding="utf-8", newline="\n")
        for name, text in files.items():
            (self.dir / name).write_text(text, encoding="utf-8", newline="\n")
        (self.dir / "expected.json").write_text(json.dumps(expected, indent=2) + "\n",
                                                encoding="utf-8")

    def run_native(self, cc, runtime):
        exe = self.dir / ("main" + tc.EXE_SUFFIX)
        exe.unlink(missing_ok=True)
        start = time.perf_counter()
        ok, log = cc.compile(self.cfile, exe, opt=2, runtime=runtime, log=self.dir / "cc.log")
        self.native_ms = (time.perf_counter() - start) * 1000
        if not ok:
            self.build_failure = log.strip()[:300]
            return
        code, out, err = tc.run_capture([exe])
        self.output = out
        self.run_exit = code


def function_changes(before, after):
    """(functions whose code changed, those that changed only in the source
    line numbers their runtime checks report), from two C texts. A function
    is a source function, or a compiler-written one by its C name."""
    plain_b, plain_a = cfuncs.by_source(before), cfuncs.by_source(after)
    lined_b, lined_a = cfuncs.by_source(before, lines=False), cfuncs.by_source(after, lines=False)
    changed = sorted(n for n in plain_b.keys() | plain_a.keys() if plain_b.get(n) != plain_a.get(n))
    with_lines = sorted(n for n in lined_b.keys() | lined_a.keys() if lined_b.get(n) != lined_a.get(n))
    return changed, sorted(set(with_lines) - set(changed))


def case_edit(case):
    """The edit id a case generates, or None for the original."""
    return None if case == "E00" else case


def run_case(case, goose, cc, runtime, work):
    record = {"case": case, "workload": "synthetic", "ok": True, "failures": []}

    def fail(why):
        record["ok"] = False
        record["failures"].append(why)

    original = Build("original", work / case / "original", goose, cc, runtime, None)
    record["contexts_checked_original"] = original.contexts
    if original.exit != 0 or original.output != original.want_output or original.warnings:
        fail("the original program does not build, run and print its expected output "
             f"without warnings (compile exit {original.exit}, warnings {original.warnings}, "
             f"{original.build_failure or ''})")
    if case == "E00":
        record["title"] = edits.NOT_SOURCE_EDITS["E00"]
        record.update(timing(original, None))
        return finish(record)

    e = edits.EDITS[case]
    record["title"] = e.title
    edited = Build("edited", work / case / "edited", goose, cc, runtime, case)
    record["contexts_checked"] = edited.contexts
    record["compiler_exit"] = edited.exit
    record["warnings_original"], record["warnings"] = original.warnings, edited.warnings

    if e.outcome == "error":
        if edited.exit == 0:
            fail("expected a compile failure; the edited program compiled")
        elif e.message not in edited.log:
            fail(f"the compile failure does not say {e.message!r}")
        elif edited.cfile.exists() and edited.exit != 0 and edited.c_text:
            fail("a C file was reported for a program that failed to compile")
    else:
        if edited.exit != 0:
            fail(f"the edited program does not compile (exit {edited.exit})")
        elif edited.build_failure:
            fail(f"the edited C does not build: {edited.build_failure}")
        elif edited.output != edited.want_output:
            fail("the edited program's output differs from the expected output")
        if e.outcome == "warning" and edited.warnings != original.warnings + 1:
            fail(f"expected one new warning, saw {edited.warnings - original.warnings}")
        if e.outcome == "warning" and e.message not in edited.log:
            fail(f"the warning does not say {e.message!r}")
        if e.outcome != "warning" and edited.warnings != original.warnings:
            fail("the edit changed the number of warnings")

    record["output_matches"] = (edited.output == edited.want_output
                                if edited.output is not None else None)
    record["functions_changed_expected"] = sorted(e.changed)
    if original.c_text and edited.c_text:
        changed, line_only = function_changes(original.c_text, edited.c_text)
        record["functions_changed"] = changed
        record["functions_changed_by_line_numbers_only"] = line_only
        # Static data and declarations outside any function, with each
        # program's own directory (which its C names) erased.
        record["data_changed"] = (cfuncs.outside_functions(original.c_text).replace(original.dir_text, "<dir>")
                                  != cfuncs.outside_functions(edited.c_text).replace(edited.dir_text, "<dir>"))
        if changed != sorted(e.changed):
            fail(f"changed functions {changed}, expected {sorted(e.changed)}")
    else:
        record["functions_changed"] = record["functions_changed_by_line_numbers_only"] = None

    if e.sequence and e.outcome != "error":
        revert = Build("revert", work / case / "revert", goose, cc, runtime, None)
        same = (revert.c_text.replace(revert.dir_text, "<dir>")
                == original.c_text.replace(original.dir_text, "<dir>"))
        record["revert_c_identical"] = same
        if not same:
            fail("the emitted C after the revert differs from the original's")
        if revert.output != original.output:
            fail("the program's output after the revert differs from the original's")
    record.update(timing(original, edited))
    return finish(record)


def timing(original, edited):
    shown = edited or original
    record = {
        "compiler_wall_ms": rounded(shown.wall_ms),
        "compiler_cpu_ms": rounded(shown.cpu_ms),
        "compiler_peak_rss": shown.peak,
        "native_compiler_invocations": 1 if shown.c_text else 0,
        "native_compiler_wall_ms": rounded(shown.native_ms),
    }
    record.update({field: None for field in NOT_YET})
    return record


def rounded(ms):
    return None if ms is None else round(ms, 1)


def finish(record):
    print(json.dumps(record, sort_keys=False))
    return record["ok"]


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--goose", required=True, help="the compiler")
    ap.add_argument("--workload", required=True, choices=("synthetic", "aincrad3"))
    ap.add_argument("--source", help="the Aincrad3 checkout (that workload only)")
    ap.add_argument("--case", action="append", help="a matrix row; repeatable. Default: all "
                    "rows that are source edits, and E00")
    ap.add_argument("--work", default=str(ROOT / ".work" / "edit_matrix"))
    a = ap.parse_args()
    if a.workload == "aincrad3":
        print("error: the aincrad3 workload is not implemented", file=sys.stderr)
        return 2
    known = ["E00", *edits.EDITS]
    cases = a.case or known
    for c in cases:
        if c not in known:
            why = edits.NOT_SOURCE_EDITS.get(c, "no such row")
            print(f"error: {c}: not a case this runner can generate ({why})", file=sys.stderr)
            return 2
    goose = Path(a.goose).resolve()
    work = Path(a.work).resolve()
    work.mkdir(parents=True, exist_ok=True)
    # The compiler's cache lives with the run, never the user's own.
    os.environ["GOOSE_HOME"] = str(work / "home")
    cc = tc.test_cc()
    if cc is None:
        print("error: no C compiler found", file=sys.stderr)
        return 2
    runtime = tc.GooseRuntime(goose, work / "runtime")
    results = [run_case(c, goose, cc, runtime, work) for c in cases]
    summary = {"summary": True, "cases": len(results), "passed": sum(results),
               "failed": len(results) - sum(results), "c_compiler": cc.desc}
    print(json.dumps(summary))
    return 0 if all(results) else 1


if __name__ == "__main__":
    sys.exit(main())
