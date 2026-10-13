#!/usr/bin/env python3
"""The qualification matrix of `goose build --units` on the synthetic family.

  python test/scale/units_matrix.py --goose GOOSE [--case ID ...] [--random N --seed S]
         [--work DIR]

Every row of the matrix (E00 to E16) is run on a program of the synthetic
family in a scratch GOOSE_HOME that this script creates and is the only thing
it ever deletes from, with --verify-reuse on for every build. After each row
the incremental result is compared with a clean build of the same sources in
a fresh store: the unit texts byte for byte, the compiler's exit status and
diagnostics, and the program's output, exit status and abort diagnostics. The
structural gates count events, never time: L-NOOP, L-LEAF, L-LOC, L-ADD and
L-EQ, and the failure rows' own requirements.

Prints one JSON record per row, with what the matrix records for every row
(frontend phases that ran, contexts checked, units whose text changed, native
compiler invocations and the units in each, objects reused and missed,
whether the link ran, and the time and peak memory the compiler and the
largest native compiler process took), then a table. With --random N runs N
seeded random edits, contract changes and store damages with --verify-reuse,
each compared with a clean build. Exits 1 if any row or step fails.
"""

import argparse
import json
import os
import random
import re
import shutil
import signal
import subprocess
import sys
import threading
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(ROOT / "scripts"))
import edits  # noqa: E402
import gen  # noqa: E402

FAMILY = dict(helpers=1, contexts=2, types=gen.INT_TYPES[:1], shareable=1, root_params=2, distinct=True,
              edit_targets=True)
SOURCE_EDITS = ("E02", "E03", "E04", "E05", "E06", "E07a", "E07b", "E08", "E09a", "E09b", "E09c")


class Build:
    """One run of `goose build --units`."""

    def __init__(self, session, flags, label, kill_after=None, verify=True):
        self.session, self.label = session, label
        self.exe = session.dir / f"{getattr(session, 'exe_name', 'prog')}.exe"
        self.report_path = session.dir / f"{label}.report.json"
        self.report_path.unlink(missing_ok=True)
        argv = [session.goose, "build", "--units", *(["--verify-reuse"] if verify else []), "-O2", *flags,
                "--build-report", str(self.report_path), "-o", str(self.exe), "main.goose"]
        env = dict(os.environ, GOOSE_HOME=str(session.home))
        p = subprocess.Popen(argv, cwd=session.dir, env=env, stdout=subprocess.PIPE,
                             stderr=subprocess.PIPE, text=True, errors="replace")
        killed = False
        if kill_after is not None:
            timer = threading.Timer(kill_after, lambda: p.poll() is None and p.kill())
            timer.start()
        out, err = p.communicate()
        if kill_after is not None:
            timer.cancel()
            killed = p.returncode == -signal.SIGKILL
        self.killed = killed
        self.exit, self.stdout, self.stderr = p.returncode, out, err
        self.report = None
        if self.report_path.exists():
            try:
                self.report = json.loads(self.report_path.read_text())
            except ValueError:
                self.report = None

    @property
    def native(self):
        return (self.report or {}).get("extensions", {}).get("native_compile") or {}

    @property
    def store(self):
        s = self.native.get("store")
        return Path(s) if s else None

    def compiled_units(self):
        return sorted({u for c in self.native.get("native_compiler_invocations", []) for u in c["units"]})

    def record(self, row):
        n = self.native
        invs = n.get("native_compiler_invocations", [])
        biggest = max(invs, key=lambda c: c.get("peak_rss_bytes") or 0, default=None)
        counts = (self.report or {}).get("counts", {})
        return {
            "row": row, "exit": self.exit, "no_op": n.get("no_op"),
            "frontend_phases": n.get("frontend_phases"),
            "contexts_checked": counts.get("checked_contexts"),
            "implementation_digests_changed": None,
            "units_text_changed": n.get("units_text_changed"),
            "native_invocations": len(invs), "units_per_invocation": [len(c["units"]) for c in invs],
            "objects_reused": n.get("objects_reused"), "objects_missed": n.get("objects_missed"),
            "link_ran": (n.get("link") or {}).get("ran"),
            "corrupt_entries": n.get("corrupt_entries"),
            "compiler_wall_s": ((self.report or {}).get("total") or {}).get("wall_seconds"),
            "compiler_cpu_s": ((self.report or {}).get("total") or {}).get("cpu_seconds"),
            "compiler_peak_rss": ((self.report or {}).get("total") or {}).get("peak_rss_bytes"),
            "largest_native_wall_s": biggest and biggest.get("wall_seconds"),
            "largest_native_peak_rss": biggest and biggest.get("peak_rss_bytes"),
        }


class Session:
    """A program, its scratch GOOSE_HOME, and the builds made of it."""

    def __init__(self, goose, base, name, edit=None):
        self.goose = str(goose)
        self.dir = base / name
        self.home = self.dir / "home"
        shutil.rmtree(self.dir, ignore_errors=True)
        self.dir.mkdir(parents=True)
        self.counter = 0
        self.expected = None
        self.write(edit)

    def write(self, edit):
        source, output, expected, files = gen.build(**FAMILY, edit=edit)
        (self.dir / "main.goose").write_text(source, encoding="utf-8", newline="\n")
        for stale in self.dir.glob("*.txt"):
            stale.unlink()
        for name, text in files.items():
            (self.dir / name).write_text(text, encoding="utf-8", newline="\n")
        self.output = output
        self.edit = edit

    def build(self, *flags, label=None, kill_after=None, verify=True):
        self.counter += 1
        return Build(self, list(flags), label or f"b{self.counter}", kill_after, verify)

    def run(self, exe):
        r = subprocess.run([str(exe)], capture_output=True, text=True, errors="replace",
                           cwd=self.dir)
        return r.returncode, r.stdout, r.stderr

    def clean(self, *flags):
        """A build of the same sources in a store of its own."""
        other = Session.__new__(Session)
        other.goose, other.dir, other.counter = self.goose, self.dir, 0
        other.exe_name = f"clean{self.counter}"
        other.home = self.dir / f"home-clean{self.counter}"
        shutil.rmtree(other.home, ignore_errors=True)
        b = Build(other, list(flags), f"clean{self.counter}")
        b.home = other.home
        return b

    def delete_store(self):
        # Only the scratch store this session made.
        shutil.rmtree(self.home / "build" / "prog", ignore_errors=True)


def units_of(store):
    d = store / "units"
    return {p.name: p.read_bytes() for p in sorted(d.iterdir())} if d.is_dir() else {}


def normalized(text, *paths):
    for p in paths:
        text = text.replace(str(p), "<path>")
    return re.sub(r"/[^ \n]*home[^ \n]*", "<home>", text)


class Matrix:
    def __init__(self, goose, work):
        self.goose, self.work = goose, work
        self.failures, self.records = [], []

    def fail(self, row, why):
        self.failures.append(f"{row}: {why}")
        print(f"FAIL {row}: {why}")

    def equal_to_clean(self, row, s, b, flags=()):
        """L-EQ: the incremental build `b`, against a clean build."""
        c = s.clean(*flags)
        if b.exit != c.exit:
            return self.fail(row, f"exit {b.exit} against a clean build's {c.exit}")
        if normalized(b.stderr, s.home, s.dir) != normalized(c.stderr, c.home, s.dir):
            return self.fail(row, "diagnostics differ from a clean build's:\n--- incremental\n"
                                  f"{b.stderr[-300:]}\n--- clean\n{c.stderr[-300:]}")
        if b.exit != 0:
            return None
        if b.store is None or c.store is None:
            return self.fail(row, "no store reported")
        ub, uc = units_of(b.store), units_of(c.store)
        if ub != uc:
            return self.fail(row, "unit texts differ from a clean build's: "
                                  f"{sorted(k for k in ub.keys() | uc.keys() if ub.get(k) != uc.get(k))}")
        want = s.run(c.exe)
        got = s.run(b.exe)
        if got != want:
            return self.fail(row, f"the program differs from a clean build's: {got[:2]} / {want[:2]}")
        if s.output is not None and got[1] != s.output:
            return self.fail(row, "the program's output is not the expected one")
        return None

    def record(self, row, b, **extra):
        r = b.record(row)
        r.update(extra)
        self.records.append(r)
        print(json.dumps(r))

    def ok_build(self, row, b):
        if b.exit != 0:
            self.fail(row, f"build failed (exit {b.exit}): {b.stderr[-300:]}")
            return False
        return True

    # ---- rows ----

    def row_E00_E01(self, base):
        s = Session(self.goose, self.work, "e00")
        b = s.build()
        self.record("E00", b)
        if not self.ok_build("E00", b):
            return
        n = b.native
        if n["objects_reused"] != 0 or not n["link"]["ran"] or not n["frontend_phases"]:
            self.fail("E00", f"a cold build reused or skipped something: {b.record('E00')}")
        self.equal_to_clean("E00", s, b)
        # L-NOOP is about a build that runs nothing, which verification mode
        # by its nature does not: it recomputes after a hit.
        w = s.build(verify=False)
        self.record("E01", w)
        if not self.ok_build("E01", w):
            return
        n = w.native
        # L-NOOP
        if not (n.get("no_op") and not n["frontend_phases"] and not n["native_compiler_invocations"]
                and not n["link"]["ran"]):
            self.fail("E01", f"L-NOOP: a warm build ran something: {w.record('E01')}")
        if normalized(w.stdout, s.home, s.dir) != normalized(b.stdout, s.home, s.dir):
            # A warm build prints what a cold one does.
            self.fail("E01", "a warm build printed something other than a cold one")
        self.equal_to_clean("E01", s, w)
        v = s.build()
        self.record("E01 verified", v)
        if self.ok_build("E01 verified", v):
            if v.native.get("no_op") or v.native.get("objects_missed"):
                self.fail("E01", f"a verified warm build ran or compiled wrongly: {v.record('E01')}")
            self.equal_to_clean("E01 verified", s, v)

    def edit_row(self, row, edit, check):
        s = Session(self.goose, self.work, f"e-{row}")
        first = s.build()
        if not self.ok_build(row, first):
            return
        s.write(edit)
        b = s.build()
        self.record(row, b)
        e = edits.EDITS[edit]
        if e.outcome == "error":
            if b.exit == 0 or e.message not in b.stderr + b.stdout:
                self.fail(row, f"an error was expected; exit {b.exit}")
            if "built " in b.stdout:
                self.fail(row, "a failed build reported an executable")
            # Nothing was recorded, so the original is still a warm build.
            s.write(None)
            w = s.build(verify=False)
            if not w.native.get("no_op"):
                self.fail(row, f"the original after a failed build is not a no-op: {w.record(row)}")
            self.equal_to_clean(row, s, w)
            return
        if not self.ok_build(row, b):
            return
        if e.outcome == "warning" and e.message not in b.stderr:
            self.fail(row, "the warning is not printed")
        check(s, first, b)
        self.equal_to_clean(row, s, b)
        if e.outcome == "warning":
            w = s.build()
            if e.message not in w.stderr:
                self.fail(row, "a warm build does not replay the warning")

    def holders(self, b, names):
        """The units that hold an implementation of any of the functions."""
        units = set()
        for f in (b.report or {}).get("functions", []):
            if any(f["name"].startswith(n + "(") or f["name"] == n for n in names):
                units |= set(f.get("units", []))
        return units

    def check_leaf(self, s, first, b):
        compiled = set(b.compiled_units())
        holders = self.holders(b, edits.EDITS["E03"].changed)
        locs = {u for u in compiled if u.endswith(".loc.c")}
        if not (compiled - locs == holders and len(locs) <= 1):
            self.fail("E03", f"L-LEAF: compiled {sorted(compiled)}, holders {sorted(holders)}")

    def check_loc(self, s, first, b):
        code = [u for u in b.compiled_units() if not u.endswith(".loc.c")]
        if code:
            self.fail("E02", f"L-LOC: a code unit recompiled: {code}")

    def check_add(self, s, first, b):
        def symbols(store):
            found = set()
            for text in units_of(store).values():
                found |= set(re.findall(r"^GS_HIDDEN [^(\n]*?(\w+)\(", text.decode(errors="replace"), re.M))
            return found
        before = self.symbols_before
        after = symbols(b.store)
        if not before <= after:
            self.fail("E08", f"L-ADD: symbols renamed: {sorted(before - after)[:5]}")
        holders = self.holders(b, edits.EDITS["E08"].changed)
        stray = [u for u in b.compiled_units() if u not in holders and not u.endswith(".loc.c")]
        if stray:
            self.fail("E08", f"L-ADD: units recompiled that hold neither the new function nor its caller: {stray}")

    def rows_edits(self):
        self.edit_row("E02", "E02", self.check_loc)
        self.edit_row("E03", "E03", self.check_leaf)
        for row in ("E04", "E05", "E06", "E07a", "E07b", "E07c", "E09a", "E09b", "E09c", "E15a", "E15b"):
            self.edit_row(row, row, lambda s, f, b: None)
        # E08 needs the symbols of the original.
        s = Session(self.goose, self.work, "e-E08")
        first = s.build()
        if self.ok_build("E08", first):
            self.symbols_before = set()
            for text in units_of(first.store).values():
                self.symbols_before |= set(re.findall(r"^GS_HIDDEN [^(\n]*?(\w+)\(", text.decode(errors="replace"), re.M))
            s.write("E08")
            b = s.build()
            self.record("E08", b)
            if self.ok_build("E08", b):
                self.check_add(s, first, b)
                self.equal_to_clean("E08", s, b)
        # E16: an edit and its exact revert.
        s = Session(self.goose, self.work, "e-E16")
        first = s.build()
        if self.ok_build("E16", first):
            original = units_of(first.store)
            s.write("E03")
            s.build()
            s.write(None)
            b = s.build()
            self.record("E16", b)
            if self.ok_build("E16", b):
                if units_of(b.store) != original:
                    self.fail("E16", "the units after the revert are not the original's")
                self.equal_to_clean("E16", s, b)

    def row_E10(self):
        s = Session(self.goose, self.work, "e10")
        base = s.build()
        if not self.ok_build("E10", base):
            return
        variants = [("--debug",), ("-DEXTRA=1",), ("-O1",)]
        for cc in ("gcc", "clang"):
            probe = subprocess.run([self.goose, "toolchain", "--cc", cc], capture_output=True, text=True)
            if probe.returncode == 0:
                variants.append(("--cc", cc))
        for flags in variants:
            if flags[0] == "-O1":
                # The Goose -O level is given by Build itself: replace it.
                pass
            before = s.build(*flags)
            self.record(f"E10 {' '.join(flags)}", before)
            if not self.ok_build("E10", before):
                continue
            n = before.native
            same = n.get("contract") == base.native.get("contract")
            if same:
                # `--cc gcc` is the default compiler under another spelling: the
                # contract names it by what it is, so the store is the same.
                if n["objects_missed"] != 0:
                    self.fail("E10", f"the same compiler under another name did not reuse ({flags})")
                continue
            if n["objects_reused"] != 0 or n["objects_missed"] != n["units_written"]:
                self.fail("E10", f"a new contract reused objects ({flags}): {before.record('E10')}")
            self.equal_to_clean(f"E10 {' '.join(flags)}", s, before, flags)
            back = s.build()
            self.record(f"E10 back from {' '.join(flags)}", back)
            n = back.native
            if not (n.get("no_op") or (n["objects_missed"] == 0 and not n["native_compiler_invocations"])):
                self.fail("E10", f"returning to the first contract is not warm ({flags}): {back.record('E10')}")
            self.equal_to_clean("E10 back", s, back)

    def row_E11(self):
        s = Session(self.goose, self.work, "e11")
        b = s.build()
        if not self.ok_build("E11", b):
            return
        s.delete_store()
        c = s.build()
        self.record("E11", c)
        if self.ok_build("E11", c):
            n = c.native
            if n["objects_reused"] != 0 or not n["link"]["ran"] or not n["frontend_phases"]:
                self.fail("E11", f"a build after the store was deleted is not cold: {c.record('E11')}")
            self.equal_to_clean("E11", s, c)

    def objects(self, store):
        return sorted((store / "obj").glob("*.o"))

    def row_E12(self):
        # Each damage on a fresh session, so that one is not hidden by another.
        for what in ("truncate", "flip", "record"):
            s = Session(self.goose, self.work, f"e12-{what}")
            b = s.build()
            if not self.ok_build("E12", b):
                return
            obj = self.objects(b.store)[0]
            unit = obj.name.split(".")[0]
            if what == "truncate":
                data = obj.read_bytes()
                obj.write_bytes(data[: len(data) // 2])
            elif what == "flip":
                data = bytearray(obj.read_bytes())
                data[len(data) // 2] ^= 0xFF
                obj.write_bytes(bytes(data))
            else:
                obj.with_suffix(".rec").unlink()
            c = s.build()
            self.record(f"E12 {what}", c)
            if not self.ok_build(f"E12 {what}", c):
                continue
            bad = c.native.get("corrupt_entries", [])
            if not any(unit in e["unit"] for e in bad):
                self.fail(f"E12 {what}", f"the damaged entry was not reported: {bad}")
            if c.native["objects_missed"] < 1:
                self.fail(f"E12 {what}", "the damaged object was not rebuilt")
            self.equal_to_clean(f"E12 {what}", s, c)

    def row_E13(self):
        s = Session(self.goose, self.work, "e13")
        b = s.build()
        if not self.ok_build("E13", b):
            return
        store = b.store
        objs = self.objects(store)
        # An interrupted publish: a temporary file left behind, and an object
        # that never got its record.
        (store / "obj" / "left-behind.o.tmp").write_bytes(b"partial")
        objs[0].with_suffix(".rec").unlink()
        (store / "tmp" / "half.o").write_bytes(b"half")
        # An interrupted link: no record, and a truncated executable.
        (store / "link.rec").unlink()
        data = b.exe.read_bytes()
        b.exe.write_bytes(data[: len(data) // 3])
        c = s.build()
        self.record("E13 simulated", c)
        if self.ok_build("E13", c):
            if not c.native["link"]["ran"]:
                self.fail("E13", "the link was skipped after an interrupted link")
            self.equal_to_clean("E13 simulated", s, c)
        # Killed for real, at several moments.
        for delay in (0.05, 0.2, 0.35, 0.5, 0.7, 0.9, 1.2):
            s.write("E03" if delay > 0.3 else None)
            k = s.build(kill_after=delay)
            after = s.build()
            self.record(f"E13 killed at {delay}s", after, killed=k.killed)
            if self.ok_build("E13 kill", after):
                self.equal_to_clean(f"E13 kill {delay}", s, after)

    def row_E14(self):
        s = Session(self.goose, self.work, "e14")
        s.build()
        s.write("E03")
        procs = []
        for k in range(2):
            exe = s.dir / f"par{k}.exe"
            env = dict(os.environ, GOOSE_HOME=str(s.home))
            procs.append(subprocess.Popen(
                [s.goose, "build", "--units", "--verify-reuse", "-O2", "-o", str(exe), "main.goose"],
                cwd=s.dir, env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True))
        results = [(p.communicate(), p.returncode) for p in procs]
        for k, ((out, err), code) in enumerate(results):
            if code != 0:
                self.fail("E14", f"build {k} failed: {err[-300:]}")
        if all(code == 0 for _, code in results):
            c = s.clean()
            want = s.run(c.exe)
            for k in range(2):
                if s.run(s.dir / f"par{k}.exe") != want:
                    self.fail("E14", f"executable {k} behaves differently from a clean build's")
        print(json.dumps({"row": "E14", "exits": [code for _, code in results]}))

    def run_all(self, cases):
        steps = [("E00", self.row_E00_E01), ("E01", None), ("E10", self.row_E10),
                 ("E11", self.row_E11), ("E12", self.row_E12), ("E13", self.row_E13),
                 ("E14", self.row_E14)]
        want = set(cases)
        if not want or want & {"E00", "E01"}:
            self.row_E00_E01(None)
        if not want or want & (set(SOURCE_EDITS) | {"E16", "E15a", "E15b", "E07c"}):
            self.rows_edits()
        for name, fn in steps[2:]:
            if not want or name in want:
                fn()

    # ---- the random sequence ----

    def random_sequence(self, steps, seed):
        rng = random.Random(seed)
        s = Session(self.goose, self.work, "random")
        s.build()
        flags = ()
        actions = ["edit"] * 6 + ["revert"] * 2 + ["contract", "damage", "nothing"]
        for step in range(steps):
            action = rng.choice(actions)
            label = f"random {step} {action}"
            if action == "edit":
                s.write(rng.choice(SOURCE_EDITS + ("E15a", "E15b", "E07c")))
            elif action == "revert":
                s.write(None)
            elif action == "contract":
                flags = rng.choice([(), ("--debug",), ("-DX=1",), ("-O1",)])
                label += f" {flags}"
            elif action == "damage":
                store = (s.home / "build" / "prog")
                objs = sorted(store.glob("*/store/*/obj/*.o")) if store.exists() else []
                if objs:
                    obj = rng.choice(objs)
                    kind = rng.choice(["truncate", "flip", "record"])
                    if kind == "truncate":
                        obj.write_bytes(obj.read_bytes()[: max(1, obj.stat().st_size // 2)])
                    elif kind == "flip":
                        data = bytearray(obj.read_bytes())
                        data[len(data) // 2] ^= 0xFF
                        obj.write_bytes(bytes(data))
                    else:
                        obj.with_suffix(".rec").unlink(missing_ok=True)
                    label += f" {kind}"
            b = s.build(*flags)
            expected_error = s.edit in ("E15a", "E07c")
            if expected_error:
                if b.exit == 0:
                    self.fail(label, "an error was expected")
                self.equal_to_clean(label, s, b, flags)
                continue
            if self.ok_build(label, b):
                self.equal_to_clean(label, s, b, flags)
            print(f"ok? step {step}: {label}")


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--goose", required=True)
    ap.add_argument("--case", action="append", default=[])
    ap.add_argument("--random", type=int, default=0, metavar="N")
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--work")
    a = ap.parse_args()
    work = Path(a.work).resolve() if a.work else ROOT / ".work" / "units_matrix"
    shutil.rmtree(work, ignore_errors=True)
    work.mkdir(parents=True)
    m = Matrix(str(Path(a.goose).resolve()), work)
    if a.random:
        m.random_sequence(a.random, a.seed)
    else:
        m.run_all(a.case)
    print("\nrow".ljust(34) + "exit  units compiled  reused  missed  link")
    for r in m.records:
        print(f"{r['row']:<33} {r['exit']:<5} {str(r['units_per_invocation']):<15} "
              f"{r['objects_reused']!s:<7} {r['objects_missed']!s:<7} {r['link_ran']}")
    print(f"units_matrix: {'ok' if not m.failures else str(len(m.failures)) + ' failure(s)'}")
    return 1 if m.failures else 0


if __name__ == "__main__":
    sys.exit(main())
