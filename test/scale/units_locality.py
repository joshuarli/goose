#!/usr/bin/env python3
"""What an edit changes among the units `--emit-units` writes.

  python test/scale/units_locality.py --goose GOOSE [--pipeline gir] [--work DIR]

Writes small multi-module programs and the synthetic family's edits, emits
units before and after each edit, and compares the two directories file by
file. Each case states the units that must change and the units that may;
anything else changing is a failure, and so is a required unit that did not.
One line per case says which units changed against which were expected. Also
checks that two runs write identical directories, and that no function symbol
of the original program is renamed or lost by an edit that only adds.

With `--pipeline gir` the units are the IR pipeline's. The synthetic family's
programs are outside what it supports, so only the two-module cases run, and a
case that the pipeline refuses is skipped and said so.

Prints one line per case and exits 1 if any fails.
"""

import argparse
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent

A = """var ga: i64[>..] = [1];
fn a_leaf(x: i64) -> i64 { return x * 3 + 1; }
fn a_use_global() -> i64 { return ga[0] + a_leaf(2); }
fn a_hook() -> i64 { return a_use_global() + 1; }
fn a_name() { print("hello from a"); }
"""
B = """var gb: i64[>..] = [2];
fn b_leaf(x: i64) -> i64 { return x * 5 + 2; }
fn b_use_global() -> i64 { return gb[0] + b_leaf(3); }
fn b_hook() -> i64 { return b_use_global() + 1; }
fn b_name() { print("hello from b"); }
"""
MAIN = """import a;
import b;
fn main() {
    print(a_hook());
    print(b_hook());
    a_name();
    b_name();
}
"""


PIPELINE = []


def emit(goose, source, out, *flags):
    shutil.rmtree(out, ignore_errors=True)
    # Run in the program's directory with a relative path: the paths a unit
    # holds are as the compiler was given them.
    r = subprocess.run([str(Path(goose).resolve()), "-O0", *PIPELINE, *flags, "--emit-units", str(out.resolve()),
                        source.name], capture_output=True, text=True, cwd=source.parent)
    if r.returncode:
        raise RuntimeError(f"{source}: {(r.stdout + r.stderr)[-400:]}")
    return {p.name: p.read_bytes() for p in sorted(out.iterdir())}


def diff(before, after):
    return {n for n in before.keys() | after.keys() if before.get(n) != after.get(n)}


def kinds(names):
    """File names as the module's unit and its kind: a.code, a.globals,
    a.loc, literals, program."""
    out = set()
    for n in names:
        m = re.fullmatch(r"main_(\w+?)_goose_[0-9a-f]{8}(_[0-9a-f]+)?(\.globals|\.loc)?\.c", n)
        if m:
            out.add(f"{m.group(1)}.{(m.group(3) or '.code')[1:]}")
        elif n.startswith("literals"):
            out.add("literals")
        elif n == "program.c":
            out.add("program")
        else:
            out.add(n)
    return out


def symbols(units):
    found = set()
    for n, text in units.items():
        if n.endswith(".c"):
            found |= set(re.findall(r"^GS_HIDDEN [^(\n]*?(\w+)\(", text.decode(), re.M))
    return found


def program(tmp, name, a=A, b=B, main=MAIN, extra=None):
    d = tmp / name
    d.mkdir(parents=True, exist_ok=True)
    for f, text in (("a.goose", a), ("b.goose", b), ("main.goose", main)):
        (d / f).write_text(text)
    for f, text in (extra or {}).items():
        (d / f).write_text(text)
    return d / "main.goose"


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--goose", required=True)
    ap.add_argument("--pipeline", choices=["gir"], help="emit the units through this compiler pipeline")
    ap.add_argument("--work")
    a = ap.parse_args()
    if a.pipeline:
        PIPELINE[:] = ["--pipeline", a.pipeline]
    scratch = ROOT / ".work" / "tmp"
    scratch.mkdir(parents=True, exist_ok=True)
    bad = []
    with tempfile.TemporaryDirectory(dir=a.work or scratch) as t:
        tmp = Path(t)
        results = []

        def case(name, before, after, required, allowed, add_only=False):
            changed = kinds(diff(before, after))
            problems = []
            if not required <= changed:
                problems.append(f"missing {sorted(required - changed)}")
            if not changed <= (required | allowed):
                problems.append(f"unexpected {sorted(changed - required - allowed)}")
            if add_only and not symbols(before) <= symbols(after):
                problems.append(f"renamed {sorted(symbols(before) - symbols(after))}")
            status = "PASS" if not problems else "FAIL " + "; ".join(problems)
            print(f"{status:5} {name}: changed {sorted(changed)}; expected {sorted(required)} "
                  f"allowed {sorted(allowed)}")
            if problems:
                bad.append(name)

        goose = a.goose
        base_src = program(tmp, "base")
        base = emit(goose, base_src, tmp / "base_units")
        again = emit(goose, base_src, tmp / "again_units")
        print(f"{'PASS' if base == again else 'FAIL'} determinism: two runs write "
              f"{'identical' if base == again else 'different'} directories ({len(base)} files)")
        if base != again:
            bad.append("determinism")
        print(f"      units: {sorted(kinds(base.keys()))}")

        def edited(name, **kw):
            return emit(goose, program(tmp, name, **kw), tmp / (name + "_units"))

        case("leaf body edit", base,
             edited("leaf", a=A.replace("x * 3 + 1", "x * 3 + 2")),
             {"a.code"}, set())
        case("comment above a function", base,
             edited("comment", a=A.replace("fn a_leaf", "// a comment\nfn a_leaf")),
             {"a.loc"}, set())
        case("function added to one module", base,
             edited("added", a=A.replace("return a_use_global() + 1;", "return a_use_global() + a_extra(1);")
                    + "fn a_extra(x: i64) -> i64 { return x + 9; }\n"),
             {"a.code"}, {"a.loc"}, add_only=True)
        case("global added to one module", base,
             edited("global", a=A + "var ga2: i64[>..] = [5];\n"),
             {"a.globals"}, {"a.code", "a.loc", "program"})
        case("string literal edited", base,
             edited("literal", a=A.replace("hello from a", "hello from A")),
             {"a.code", "literals"}, set())
        case("module added", base,
             edited("module", main=MAIN.replace("import b;", "import b;\nimport c;")
                    .replace("b_name();", "b_name();\n    print(c_one());"),
                    extra={"c.goose": "fn c_one() -> i64 { return 1; }\n"}),
             # The IR pipeline gives a function a location table only if it has a
             # check or a call to name one for.
             {"main.code", "c.code", "units.txt"} | ({"c.loc"} if not PIPELINE else set()),
             {"main.loc", "program"} | ({"c.loc"} if PIPELINE else set()), add_only=True)

        # The synthetic family's edits, each against the original program.
        def family(edit=None):
            d = tmp / f"fam{edit or ''}"
            cmd = [sys.executable, str(HERE / "gen.py"), "--shareable", "2", "--distinct",
                   "--edit-targets", "--out", str(d)]
            if edit:
                cmd += ["--edit", edit]
            subprocess.run(cmd, check=True, capture_output=True)
            return emit(goose, d / "main.goose", tmp / f"fam{edit or ''}_units")

        orig = None
        try:
            orig = family()
        except RuntimeError as error:
            if not PIPELINE:
                raise
            print(f"SKIP  family and sharded cases: {str(error).strip().splitlines()[-1][:100]}")
        if orig is None:
            print("units_locality: " + ("ok" if not bad else f"{len(bad)} failed: {', '.join(bad)}"))
            return 1 if bad else 0
        case("family E02 comment above a function", orig, family("E02"), {"main.loc"}, set())
        case("family E03 leaf body", orig, family("E03"), {"main.code"}, {"main.loc"})
        case("family E08 specialization request", orig, family("E08"), {"main.code"},
             {"main.loc"}, add_only=True)

        # A module big enough to be sharded: an edit changes the shards that
        # hold the function, not the others.
        def big(edit=None):
            d = tmp / f"big{edit or ''}"
            cmd = [sys.executable, str(HERE / "gen.py"), "--shareable", "60", "--distinct",
                   "--edit-targets", "--out", str(d)]
            if edit:
                cmd += ["--edit", edit]
            subprocess.run(cmd, check=True, capture_output=True)
            return emit(goose, d / "main.goose", tmp / f"big{edit or ''}_units")

        bo, be = big(), big("E03")
        shards = [n for n in bo if re.fullmatch(r"main_main_goose_[0-9a-f]{8}_[0-9a-f]+\.c", n)]
        changed_code = [n for n in diff(bo, be) if n in shards]
        ok = len(shards) > 1 and len(changed_code) <= 1
        print(f"{'PASS' if ok else 'FAIL'} sharded module: {len(shards)} code shards, an edit to "
              f"one leaf changes {len(changed_code)} of them")
        if not ok:
            bad.append("sharded module")
    print("units_locality: " + ("ok" if not bad else f"{len(bad)} failed: {', '.join(bad)}"))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
