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

Prints one JSON object per case, then a summary object. Synthetic records leave
the native-object reuse fields null because they use the single-file build
path. Exits 1 if any case fails.

The Aincrad3 mode builds the core entry through `goose build --units` in an
isolated copy of the supplied checkout. It records the cold build, a no-op,
a comment edit, and a body edit; it never writes to `--source`.
"""

import argparse
import json
import os
import re
import shutil
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
NOT_YET = ("frontend_phases", "implementation_digests_changed",
           "units_per_native_invocation", "objects_reused", "objects_missed", "link_skipped",
           "native_compiler_peak_rss")


def measured(argv, log_dir, name, cwd=None, env=None):
    """(exit code, stdout, stderr, wall ms, CPU ms, peak RSS bytes) of one
    process; the last three are None where the platform cannot say."""
    if tc.IS_WINDOWS:
        start = time.perf_counter()
        p = subprocess.run([str(a) for a in argv], capture_output=True, text=True,
                           errors="replace", cwd=cwd, env=env)
        code, out, err = p.returncode, p.stdout, p.stderr
        return code, out, err, (time.perf_counter() - start) * 1000, None, None
    outf, errf = log_dir / f"{name}.stdout", log_dir / f"{name}.stderr"
    with open(outf, "wb") as fo, open(errf, "wb") as fe:
        start = time.perf_counter()
        p = subprocess.Popen([str(a) for a in argv], stdout=fo, stderr=fe, cwd=cwd, env=env)
        _, status, usage = os.wait4(p.pid, 0)
        ms = (time.perf_counter() - start) * 1000
        p.returncode = os.waitstatus_to_exitcode(status)
    cpu = (usage.ru_utime + usage.ru_stime) * 1000
    peak = usage.ru_maxrss * (1 if tc.IS_MACOS else 1024)
    return (p.returncode, tc.decode(outf.read_bytes()), tc.decode(errf.read_bytes()), ms, cpu, peak)


AINCRAD3_CASES = ("E00", "E01", "E02", "E03")
AINCRAD3_ENTRY = Path("src/world-core-continue.goose")
AINCRAD3_INCLUDES = (Path("native/world_event_storage.h"), Path("native/m4_world_metrics.h"))


def aincrad3_edit(source, case):
    """Apply one reviewed, output-preserving change to the core entry."""
    text = source.read_text(encoding="utf-8")
    if case == "E02":
        before = "fn argument_u64("
        after = "// Added above the entry's argument parser.\n\n" + before
        if text.count(before) != 1:
            raise ValueError(f"expected one occurrence of {before!r} in {source}")
        text = text.replace(before, after, 1)
    elif case == "E03":
        start = text.index("fn argument_u64(")
        end = text.index("\nfn argument_u32(", start)
        body = text[start:end]
        before = "result = result * 10 + digit;"
        after = "result = digit + result * 10;"
        if body.count(before) != 1:
            raise ValueError(f"expected one occurrence of {before!r} in argument_u64 in {source}")
        text = text[:start] + body.replace(before, after, 1) + text[end:]
    else:
        raise ValueError(f"{case} is not a source edit for the Aincrad3 core entry")
    source.write_text(text, encoding="utf-8", newline="\n")


def aincrad3_unit_kinds(names):
    """Counts of changed code, locations, support and other units."""
    kinds = {"code": 0, "globals": 0, "locations": 0, "literals": 0,
             "program": 0, "native_support": 0, "other": 0}
    for name in names:
        if name == "native.c":
            kinds["native_support"] += 1
        elif name == "program.c":
            kinds["program"] += 1
        elif name.endswith(".globals.c"):
            kinds["globals"] += 1
        elif name.startswith("literals") and name.endswith(".c"):
            kinds["literals"] += 1
        elif name.endswith("_loc.c") or name.endswith(".loc.c"):
            kinds["locations"] += 1
        elif name.endswith(".c"):
            kinds["code"] += 1
        else:
            kinds["other"] += 1
    return kinds


class Aincrad3Build:
    """One core-entry build with its native-unit report."""

    def __init__(self, goose, source, work, env, verify, label):
        self.report_path = work / f"{label}.report.json"
        self.report_path.unlink(missing_ok=True)
        self.exe = work / ("world-core-continue" + tc.EXE_SUFFIX)
        command = [str(goose), "build", "--units"]
        if verify:
            command.append("--verify-reuse")
        command += ["-O0"]
        for header in AINCRAD3_INCLUDES:
            command += ["--include", str(source / header)]
        command += ["--build-report", str(self.report_path), "-o", str(self.exe),
                    str(source / AINCRAD3_ENTRY)]
        (self.exit, self.stdout, self.stderr, self.wall_ms, self.cpu_ms, self.peak_rss) = measured(
            command, work, label, cwd=source, env=env)
        try:
            self.report = json.loads(self.report_path.read_text(encoding="utf-8"))
        except (OSError, ValueError):
            self.report = {}
        self.native = (self.report.get("extensions") or {}).get("native_compile") or {}

    def record(self, case, requested):
        native = self.native
        invocations = native.get("native_compiler_invocations", [])
        verification = native.get("verification_invocations", [])
        changed = aincrad3_unit_kinds(native.get("units_text_changed", []))
        biggest = max(invocations, key=lambda x: x.get("peak_rss_bytes") or 0, default={})
        return {
            "case": case,
            "workload": "aincrad3",
            "requested": requested,
            "ok": self.exit == 0,
            "failures": [] if self.exit == 0 else [(self.stdout + self.stderr)[-300:]],
            "title": {
                "E00": "cold core-entry build",
                "E01": "unchanged no-op build",
                "E02": "comment and blank line above argument_u64",
                "E03": "commute digit addition in argument_u64",
            }[case],
            "compiler_exit": self.exit,
            "no_op": native.get("no_op"),
            "frontend_phases": native.get("frontend_phases"),
            "contexts_checked": (self.report.get("counts") or {}).get("checked_contexts"),
            "implementation_digests_changed": None,
            "units_text_changed": sum(changed.values()),
            "changed_unit_kinds": changed,
            "native_compiler_invocations": len(invocations),
            "units_per_native_invocation": [len(item.get("units", [])) for item in invocations],
            "verification_invocations": len(verification),
            "objects_reused": native.get("objects_reused"),
            "objects_missed": native.get("objects_missed"),
            "link_skipped": (native.get("link") or {}).get("ran") is False,
            "compiler_wall_ms": rounded(self.wall_ms),
            "compiler_cpu_ms": rounded(self.cpu_ms),
            "compiler_peak_rss": self.peak_rss,
            "native_compiler_peak_rss": biggest.get("peak_rss_bytes"),
            "native_compiler_wall_ms": rounded((biggest.get("wall_seconds") or 0) * 1000)
            if biggest else None,
        }


def run_aincrad3(cases, goose, source, work):
    """Run selected rows in one isolated source copy and one units store."""
    if source is None:
        print("error: --workload aincrad3 needs --source DIR", file=sys.stderr)
        return 2
    source = Path(source).resolve()
    if not (source / AINCRAD3_ENTRY).is_file():
        print(f"error: Aincrad3 core entry is missing: {source / AINCRAD3_ENTRY}", file=sys.stderr)
        return 2
    for header in AINCRAD3_INCLUDES:
        if not (source / header).is_file():
            print(f"error: Aincrad3 native header is missing: {source / header}", file=sys.stderr)
            return 2
    if not (source / "src/protocol/schema_generated.goose").is_file():
        print("error: Aincrad3 generated protocol source is missing from --source; "
              "stage the existing generated file before running the matrix", file=sys.stderr)
        return 2

    work.mkdir(parents=True, exist_ok=True)
    session = work / "aincrad3"
    shutil.rmtree(session, ignore_errors=True)
    staged = session / "source"
    session.mkdir(parents=True)
    shutil.copytree(source, staged, ignore=shutil.ignore_patterns(".git", ".work", "build", "target"))
    entry = staged / AINCRAD3_ENTRY
    if not entry.is_file():
        print(f"error: staged Aincrad3 core entry is missing: {entry}", file=sys.stderr)
        return 2
    home = session / "home"
    tmp = session / "tmp"
    home.mkdir()
    tmp.mkdir()
    env = dict(os.environ, GOOSE_HOME=str(home), TMPDIR=str(tmp))

    ordered = [case for case in AINCRAD3_CASES if case in cases]
    # A changed build needs a warm baseline, even when a focused invocation
    # asks for only one edit row.
    if "E00" not in ordered:
        ordered.insert(0, "E00")
    records = []
    bad = []
    for index, case in enumerate(ordered):
        requested = case in cases
        if case in ("E02", "E03"):
            try:
                aincrad3_edit(entry, case)
            except (OSError, ValueError) as error:
                print(f"error: {error}", file=sys.stderr)
                return 2
        # The no-op row needs the real short-circuit. Other rows check every
        # reused object against a fresh native compilation.
        build = Aincrad3Build(goose, staged, session, env,
                              verify=(case != "E01"), label=f"{index:02d}-{case}")
        record = build.record(case, requested)
        if case == "E00" and build.exit == 0:
            if not build.native.get("link", {}).get("ran") or not build.native.get("native_compiler_invocations"):
                record["ok"] = False
                record["failures"].append("cold build did not compile and link native units")
        elif case == "E01" and build.exit == 0:
            if (build.native.get("no_op") is not True or build.native.get("frontend_phases") or
                    build.native.get("native_compiler_invocations") or
                    (build.native.get("link") or {}).get("ran")):
                record["ok"] = False
                record["failures"].append("unchanged build did not short-circuit before frontend, compiler, and link")
        elif case == "E02" and build.exit == 0:
            changed = record["changed_unit_kinds"]
            if (build.native.get("no_op") or changed["locations"] != 1 or changed["code"] or changed["globals"] or
                    changed["literals"] or changed["program"] or changed["native_support"] or changed["other"]):
                record["ok"] = False
                record["failures"].append(f"comment edit did not change exactly one location unit: {changed}")
        elif case == "E03" and build.exit == 0:
            changed = record["changed_unit_kinds"]
            if (build.native.get("no_op") or changed["code"] != 1 or changed["locations"] or changed["globals"] or
                    changed["literals"] or changed["program"] or changed["native_support"] or changed["other"]):
                record["ok"] = False
                record["failures"].append(f"body edit did not change exactly one code unit: {changed}")
        print(json.dumps(record))
        records.append(record)
        if not record["ok"]:
            bad.append(case)
            break
    print(json.dumps({"summary": True, "workload": "aincrad3", "cases": len(records),
                      "passed": sum(record["ok"] for record in records), "failed": len(bad),
                      "source_entry": str(AINCRAD3_ENTRY), "optimization": "-O0"}))
    return 1 if bad else 0


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


def emitted_units(build, goose):
    """{file name: bytes} of the units the program is emitted as, written with
    the program's own directory as the working directory so that the paths a
    unit holds do not depend on where it lives; None if it does not compile."""
    if build.exit != 0:
        return None
    out = build.dir / "units"
    shutil.rmtree(out, ignore_errors=True)
    code, _, _ = tc.run_capture([str(Path(goose).resolve()), "-O2", "--emit-units", str(out.resolve()),
                                 "main.goose"], cwd=build.dir)
    return {p.name: p.read_bytes() for p in out.iterdir()} if code == 0 else None


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
        record["units_changed"] = None
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

    # The units that differ between the two programs' emitted units.
    before, after = emitted_units(original, goose), emitted_units(edited, goose)
    record["units_changed"] = (None if before is None or after is None else
                               sorted(n for n in before.keys() | after.keys()
                                      if before.get(n) != after.get(n)))

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
    ap.add_argument("--source", help="a read-only Aincrad3 source copy (that workload only)")
    ap.add_argument("--case", action="append", help="a matrix row; repeatable. Default: all "
                    "rows that are source edits, and E00")
    ap.add_argument("--work", default=str(ROOT / ".work" / "edit_matrix"))
    a = ap.parse_args()
    goose = Path(a.goose).resolve()
    work = Path(a.work).resolve()
    if a.workload == "aincrad3":
        cases = a.case or list(AINCRAD3_CASES)
        unknown = sorted(set(cases) - set(AINCRAD3_CASES))
        if unknown:
            print(f"error: unsupported Aincrad3 matrix row(s): {', '.join(unknown)}", file=sys.stderr)
            return 2
        return run_aincrad3(cases, goose, a.source, work)
    known = ["E00", *edits.EDITS]
    cases = a.case or known
    for c in cases:
        if c not in known:
            why = edits.NOT_SOURCE_EDITS.get(c, "no such row")
            print(f"error: {c}: not a case this runner can generate ({why})", file=sys.stderr)
            return 2
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
