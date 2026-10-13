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
each compared with a clean build. Exits 1 if any row or step fails and 2 if
any qualification dimension is unavailable.
"""

import argparse
import json
import os
import random
import re
import shlex
import shutil
import subprocess
import sys
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
E10_UNAVAILABLE = {
    "independent_c_flags": "the build command exposes no raw C flag override; --debug changes numeric mode and C flags together (-D is tested separately)",
    "target": "the compiler has no target option; a cross compiler also changes C compiler identity",
    "runtime_text_only": "runtime text is embedded in the Goose binary, so changing it also changes compiler binary identity",
}


def make_compiler_variant(goose, destination):
    """Make a new executable identity without changing its runtime text."""
    source = Path(goose)
    data = source.read_bytes()
    base_version = subprocess.run([str(source), "version"], capture_output=True, text=True,
                                  errors="replace", check=False)
    if base_version.returncode != 0:
        raise ValueError(f"cannot run Goose compiler {source}: {base_version.stderr.strip()}")
    # ELF, Mach-O and PE loaders ignore bytes after the executable image.
    data += b"\0"
    destination = Path(destination)
    destination.write_bytes(data)
    shutil.copymode(source, destination)
    variant = subprocess.run([str(destination), "version"], capture_output=True, text=True,
                             errors="replace", check=False)
    if variant.returncode != 0:
        raise ValueError(f"compiler variant is not executable: {variant.stderr.strip()}")
    if variant.stdout != base_version.stdout:
        raise ValueError("a binary-only compiler variant changed runtime text")
    return destination


class Build:
    """One run of `goose build --units`."""

    def __init__(self, session, flags, label, goose=None, env_overrides=None,
                 kill_when=None, on_kill=None, kill_timeout=30, verify=True):
        self.session, self.label = session, label
        self.exe = session.dir / f"{getattr(session, 'exe_name', 'prog')}.exe"
        self.report_path = session.dir / f"{label}.report.json"
        self.report_path.unlink(missing_ok=True)
        goose = str(goose or session.goose)
        argv = [goose, "build", "--units", *(["--verify-reuse"] if verify else []), "-O2", *flags,
                "--build-report", str(self.report_path), "-o", str(self.exe), "main.goose"]
        env = dict(os.environ, GOOSE_HOME=str(session.home))
        if env_overrides:
            env.update(env_overrides)
        p = subprocess.Popen(argv, cwd=session.dir, env=env, stdout=subprocess.PIPE,
                             stderr=subprocess.PIPE, text=True, errors="replace")
        killed = False
        deadline = time.monotonic() + kill_timeout if kill_when is not None else None
        while p.poll() is None:
            if kill_when is not None and kill_when():
                p.kill()
                killed = True
                if on_kill is not None:
                    on_kill()
                break
            if deadline is not None and time.monotonic() >= deadline:
                p.kill()
                if on_kill is not None:
                    on_kill()
                break
            time.sleep(0.005)
        out, err = p.communicate()
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
            "runtime_version": (self.report or {}).get("runtime_version"),
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

    def build(self, *flags, label=None, goose=None, env_overrides=None,
              kill_when=None, on_kill=None, kill_timeout=30, verify=True):
        self.counter += 1
        return Build(self, list(flags), label or f"b{self.counter}", goose, env_overrides,
                     kill_when, on_kill, kill_timeout, verify)

    def run(self, exe):
        r = subprocess.run([str(exe)], capture_output=True, text=True, errors="replace",
                           cwd=self.dir)
        return r.returncode, r.stdout, r.stderr

    def clean(self, *flags, goose=None):
        """A build of the same sources in a store of its own."""
        other = Session.__new__(Session)
        other.goose, other.dir, other.counter = self.goose, self.dir, 0
        other.exe_name = f"clean{self.counter}"
        other.home = self.dir / f"home-clean{self.counter}"
        shutil.rmtree(other.home, ignore_errors=True)
        b = Build(other, list(flags), f"clean{self.counter}", goose=goose)
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
        self.unavailable = []

    def fail(self, row, why):
        self.failures.append(f"{row}: {why}")
        print(f"FAIL {row}: {why}")

    def record_unavailable(self, row, dimensions):
        record = {"row": row, "status": "unavailable", "dimensions": dimensions}
        self.unavailable.append(record)
        self.records.append(record)
        print(json.dumps(record))

    def completion(self):
        if self.failures:
            return "fail", 1
        if self.unavailable:
            return "incomplete", 2
        return "ok", 0

    def equal_to_clean(self, row, s, b, flags=(), goose=None):
        """L-EQ: the incremental build `b`, against a clean build."""
        c = s.clean(*flags, goose=goose)
        if b.exit != c.exit:
            return self.fail(row, f"exit {b.exit} against a clean build's {c.exit}")
        if normalized(b.stdout, b.exe, s.home, s.dir) != normalized(c.stdout, c.exe, c.home, s.dir):
            return self.fail(row, "stdout differs from a clean build's:\n--- incremental\n"
                                  f"{b.stdout[-300:]}\n--- clean\n{c.stdout[-300:]}")
        if normalized(b.stderr, b.exe, s.home, s.dir) != normalized(c.stderr, c.exe, c.home, s.dir):
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
        if e.outcome == "warning":
            if units_of(first.store) != units_of(b.store):
                self.fail(row, "the warning edit changed generated unit text")
            if b.native.get("native_compiler_invocations") or b.native.get("link", {}).get("ran"):
                self.fail(row, "the warning edit recompiled or relinked unchanged units")
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
        self.row_E16()

    def row_E16(self):
        s = Session(self.goose, self.work, "e-E16")
        first = s.build()
        if self.ok_build("E16", first):
            original = units_of(first.store)
            s.write("E03")
            edited = s.build()
            self.record("E16 edit", edited)
            if not self.ok_build("E16 edit", edited):
                return
            edited_units = units_of(edited.store)
            if edited_units == original:
                self.fail("E16", "the intermediate edit did not change any unit text")
            self.equal_to_clean("E16 edit", s, edited)
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

        variants = [("numeric profile --debug", ("--debug",), None),
                    ("-D define", ("-DEXTRA=1",), None),
                    ("numeric profile -O1", ("-O1",), None)]
        for cc in ("gcc", "clang"):
            probe = subprocess.run([self.goose, "toolchain", "--cc", cc], capture_output=True,
                                   text=True, env=dict(os.environ, GOOSE_HOME=str(s.home)))
            if probe.returncode == 0:
                variants.append((f"C compiler {cc}", ("--cc", cc), None))

        try:
            binary_variant = make_compiler_variant(
                self.goose, self.work / f"goose-binary-variant{Path(self.goose).suffix}")
            variants.append(("compiler binary", (), binary_variant))
        except (OSError, ValueError) as error:
            self.fail("E10", f"could not construct compiler contract variants: {error}")

        for label, flags, goose in variants:
            before = s.build(*flags, goose=goose)
            self.record(f"E10 {label}", before)
            if not self.ok_build("E10", before):
                continue
            n = before.native
            same = n.get("contract") == base.native.get("contract")
            if same:
                # `--cc gcc` is the default compiler under another spelling: the
                # contract names it by what it is, so the store is the same.
                if n["objects_missed"] != 0:
                    self.fail("E10", f"the same compiler under another name did not reuse ({label})")
                self.equal_to_clean(f"E10 {label}", s, before, flags, goose)
                continue
            if n["objects_reused"] != 0 or n["objects_missed"] != n["units_written"]:
                self.fail("E10", f"a new contract reused objects ({label}): {before.record('E10')}")
            if label == "compiler binary" and n.get("runtime_version") != base.record("base").get("runtime_version"):
                self.fail("E10", "a binary-only compiler variant changed runtime text")
            self.equal_to_clean(f"E10 {label}", s, before, flags, goose)
            back = s.build()
            self.record(f"E10 back from {label}", back)
            n = back.native
            if not self.is_warm(n):
                self.fail("E10", f"returning to the first contract is not warm ({label}): {back.record('E10')}")
            self.equal_to_clean("E10 back", s, back)
            again = s.build(*flags, goose=goose)
            self.record(f"E10 back to {label}", again)
            if not self.is_warm(again.native):
                self.fail("E10", f"the {label} store was not left warm: {again.record('E10')}")
            self.equal_to_clean(f"E10 back to {label}", s, again, flags, goose)

        self.record_unavailable("E10 unavailable dimensions", E10_UNAVAILABLE)

    @staticmethod
    def is_warm(native):
        return bool(not native.get("native_compiler_invocations")
                    and not (native.get("link") or {}).get("ran")
                    and (native.get("no_op") or native.get("objects_missed") == 0))

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
        objects = self.objects(store)
        if not objects:
            self.fail("E13", "the cold build published no object to interrupt")
            return

        # Hold record publication open after the object rename. The kill must
        # leave an object without its completion record, not an invented state.
        obj = objects[0]
        rec = obj.with_suffix(".rec")
        temp = Path(str(rec) + ".tmp")
        obj.unlink()
        rec.unlink(missing_ok=True)
        try:
            os.mkfifo(temp)
        except (AttributeError, OSError) as error:
            self.fail("E13 publish", f"cannot create a blocking publication point: {error}")
            return
        killed = s.build(kill_when=lambda: obj.exists() and not rec.exists(), kill_timeout=30)
        if not killed.killed:
            self.fail("E13 publish", "the build did not reach and interrupt record publication")
        if not obj.exists() or rec.exists() or not temp.exists():
            self.fail("E13 publish", "the interruption did not leave the object-without-record state")
        temp.unlink(missing_ok=True)
        recovered = s.build()
        self.record("E13 publish recovery", recovered, interrupted=killed.killed)
        if self.ok_build("E13 publish recovery", recovered):
            if recovered.native.get("objects_missed", 0) < 1:
                self.fail("E13 publish", "recovery did not rebuild the interrupted object")
            self.equal_to_clean("E13 publish recovery", s, recovered)

        # Force a link and block its compiler wrapper after invocation begins.
        real_cc = shutil.which("cc")
        if not real_cc or os.name == "nt":
            self.fail("E13 link", "this host has no POSIX C compiler wrapper support")
            return
        wrapper = self.work / "e13-cc-wrapper"
        wrapper.write_text(
            "#!/bin/sh\n"
            "for arg in \"$@\"; do\n"
            f"  case \"$arg\" in -c|--version|-dumpversion|-dumpfullversion|-dumpmachine) "
            f"exec {shlex.quote(real_cc)} \"$@\" ;; esac\n"
            "done\n"
            "if [ -n \"${GOOSE_LINK_MARKER:-}\" ] && [ -n \"${GOOSE_LINK_RELEASE:-}\" ]; then\n"
            "  : > \"$GOOSE_LINK_MARKER\"\n"
            "  while [ ! -e \"$GOOSE_LINK_RELEASE\" ]; do sleep 0.01; done\n"
            "  exit 99\n"
            "fi\n"
            f"exec {shlex.quote(real_cc)} \"$@\"\n", encoding="utf-8")
        wrapper.chmod(0o755)
        cc_flags = ("--cc", str(wrapper))
        plain_env = {}
        wrapper_prime = s.build(*cc_flags, env_overrides=plain_env)
        self.record("E13 link wrapper prime", wrapper_prime)
        if not self.ok_build("E13 link wrapper prime", wrapper_prime):
            return
        warm_wrapper = s.build(*cc_flags, env_overrides=plain_env)
        self.record("E13 link wrapper warm", warm_wrapper)
        if not self.ok_build("E13 link wrapper warm", warm_wrapper):
            return
        if warm_wrapper.native.get("objects_missed", 0) != 0:
            self.fail("E13 link", "the wrapper contract did not leave its objects warm")
        link_record = warm_wrapper.store / "link.rec"
        link_record.unlink(missing_ok=True)
        warm_wrapper.exe.write_bytes(warm_wrapper.exe.read_bytes()[:0])
        marker = self.work / "e13-link-started"
        release = self.work / "e13-link-release"
        marker.unlink(missing_ok=True)
        release.unlink(missing_ok=True)
        blocked_env = {**plain_env, "GOOSE_LINK_MARKER": str(marker),
                       "GOOSE_LINK_RELEASE": str(release)}
        interrupted = s.build(*cc_flags, env_overrides=blocked_env,
                              kill_when=marker.exists, on_kill=lambda: release.touch(),
                              kill_timeout=30)
        release.touch()
        if not interrupted.killed:
            self.fail("E13 link", "the build did not reach and interrupt the link command")
        if link_record.exists():
            self.fail("E13 link", "the interrupted link retained its completion record")
        recovered = s.build(*cc_flags, env_overrides=plain_env)
        self.record("E13 link recovery", recovered, interrupted=interrupted.killed)
        if self.ok_build("E13 link recovery", recovered):
            if not recovered.native.get("link", {}).get("ran"):
                self.fail("E13 link", "recovery skipped the incomplete link")
            self.equal_to_clean("E13 link recovery", s, recovered, cc_flags)

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
        initial = s.build()
        if not self.ok_build("random initial build", initial):
            return
        self.equal_to_clean("random initial build", s, initial)
        flags = ()
        actions = ["edit"] * 6 + ["revert"] * 2 + ["contract", "damage", "nothing"]
        last_successful = initial
        last_successful_flags = flags
        last_successful_edit = s.edit
        for step in range(steps):
            damage_ready = last_successful_flags == flags and last_successful_edit == s.edit
            available = actions if damage_ready else [a for a in actions if a != "damage"]
            action = rng.choice(available)
            label = f"random {step} {action}"
            damaged = False
            if action == "edit":
                s.write(rng.choice(SOURCE_EDITS + ("E15a", "E15b", "E07c")))
            elif action == "revert":
                s.write(None)
            elif action == "contract":
                flags = rng.choice([(), ("--debug",), ("-DX=1",), ("-O1",)])
                label += f" {flags}"
            elif action == "damage":
                objs = (sorted(last_successful.store.glob("obj/*.o")) +
                        sorted(last_successful.store.glob("obj/*.obj")))
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
                    damaged = True
                    label += f" {kind}"
                if not damaged:
                    self.fail(label, "the damage action found no cached object to damage")
            b = s.build(*flags)
            self.record(label, b, action=action, damage_applied=damaged)
            expected_error = s.edit in ("E15a", "E07c")
            if expected_error:
                if b.exit == 0:
                    self.fail(label, "an error was expected")
                edit = edits.EDITS[s.edit]
                if edit.message not in b.stderr + b.stdout:
                    self.fail(label, "the expected diagnostic was not printed")
                if "built " in b.stdout:
                    self.fail(label, "a failed build reported an executable")
                self.equal_to_clean(label, s, b, flags)
                continue
            if s.edit == "E15b" and edits.EDITS["E15b"].message not in b.stderr:
                self.fail(label, "the warning was not printed")
            if b.exit != 0:
                self.fail(label, f"unexpected build failure (exit {b.exit}): {b.stderr[-300:]}")
                continue
            if action == "damage" and damaged:
                if b.native.get("objects_missed", 0) < 1:
                    self.fail(label, "the damaged object was not rebuilt")
                if not b.native.get("corrupt_entries"):
                    self.fail(label, "the damaged cache entry was not reported")
            self.equal_to_clean(label, s, b, flags)
            last_successful = b
            last_successful_flags = flags
            last_successful_edit = s.edit


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
        if "exit" not in r:
            print(f"{r['row']:<33} {r['status']}")
            continue
        print(f"{r['row']:<33} {r['exit']:<5} {str(r['units_per_invocation']):<15} "
              f"{r['objects_reused']!s:<7} {r['objects_missed']!s:<7} {r['link_ran']}")
    status, exit_code = m.completion()
    if status == "incomplete":
        dimensions = sum(len(record["dimensions"]) for record in m.unavailable)
        detail = f"incomplete ({dimensions} unavailable dimension(s))"
    elif status == "fail":
        detail = f"{len(m.failures)} failure(s)"
    else:
        detail = "ok"
    print(f"units_matrix: {detail}")
    return exit_code


if __name__ == "__main__":
    sys.exit(main())
