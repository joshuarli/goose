#!/usr/bin/env python3
"""What varies the specializations of one source function, as small programs.

  python test/scale/findings.py --goose GOOSE [--markdown]

Each finding is one variation of the calling context, a program that makes
it, and what the compiler does with it: how many specializations the
checker creates for the function, how many of their printed bodies (`--specs`
at -O0) differ, and how many distinct implementations the emitted C holds
(callees compared by class, numbering and source lines masked). The expected
values were read from the compiler; the run fails if it no longer agrees.
The optional Markdown table contains these rows.
"""

import argparse
import re
import subprocess
import sys
import tempfile
from collections import namedtuple
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import cfuncs  # noqa: E402
import gen  # noqa: E402

Finding = namedtuple("Finding", "id variation function specs bodies implementations program")

HEAD_LEN = "fn f(a: i64[:]) -> i64 { return a.len; }\n"
HEAD_LEN2 = "fn f(a: i64[:], b: i64[:]) -> i64 { return a.len + b.len; }\n"

FINDINGS = [
    Finding("F01", "slice argument rooted in a global, and in a local", "f", 2, 1, 1,
            HEAD_LEN + "var g: i64[>..] = [1];\n"
            "fn main() { var l: i64[>..] = [2]; print(f(g)); print(f(l)); }\n"),
    Finding("F02", "the same, for a body that indexes the slice", "f", 2, 1, 2,
            "fn f(a: i64[:]) -> i64 { return a[0]; }\nvar g: i64[>..] = [1];\n"
            "fn main() { var l: i64[>..] = [2]; print(f(g)); print(f(l)); }\n"),
    Finding("F03", "several different globals, and several locals at different depths", "f", 2, 1, 1,
            HEAD_LEN + "var g: i64[>..] = [1];\nvar h: i64[>..] = [1];\n"
            "fn main() { var a: i64[>..] = [1]; { var b: i64[>..] = [1]; "
            "print(f(g)); print(f(h)); print(f(a)); print(f(b)); } }\n"),
    Finding("F04", "two slice parameters: the same array twice, and two arrays", "f", 2, 1, 1,
            HEAD_LEN2 + "fn main() { var x: i64[>..] = [1]; var y: i64[>..] = [2]; "
            "print(f(x, y)); print(f(x, x)); }\n"),
    Finding("F05", "two slice parameters: global or local per parameter", "f", 4, 1, 1,
            HEAD_LEN2 + "var g: i64[>..] = [1];\nvar h: i64[>..] = [2];\n"
            "fn main() { var x: i64[>..] = [3]; var y: i64[>..] = [4]; "
            "print(f(g, h)); print(f(g, y)); print(f(x, h)); print(f(x, y)); }\n"),
    Finding("F06", "two locals: first outer, first inner, or at one depth", "f", 3, 1, 1,
            HEAD_LEN2 + "fn main() { var x: i64[>..] = [1]; var z: i64[>..] = [1]; "
            "{ var y: i64[>..] = [2]; print(f(x, y)); print(f(y, x)); print(f(x, z)); } }\n"),
    Finding("F07", "a writable array and a const one", "f", 2, 1, 1,
            HEAD_LEN + "fn main() { var x: i64[>..] = [1]; let c: const i64[>..] = [2]; "
            "print(f(x)); print(f(c)); }\n"),
    Finding("F08", "whole array and slice views of it", "f", 1, 1, 1,
            HEAD_LEN + "var g: i64[>..] = [1, 2, 3];\n"
            "fn main() { print(f(g)); print(f(g[1..])); print(f(g[..2])); }\n"),
    Finding("F09", "scalar reference to a global, and to a local", "f", 2, 1, 1,
            "fn f(a: i64&) -> i64 { return a + 1; }\nvar g: i64 = 1;\n"
            "fn main() { var l: i64 = 2; print(f(g)); print(f(l)); }\n"),
    Finding("F10", "an enclosing function given a global root, and a local one", "outer", 2, 1, 1,
            "fn outer(a: i64[:]) -> i64 {\n    fn inner() -> i64 { return a.len; }\n"
            "    return inner();\n}\nvar g: i64[>..] = [1];\n"
            "fn main() { var l: i64[>..] = [2]; print(outer(g)); print(outer(l)); }\n"),
    Finding("F11", "the nested function of F10", "inner", 2, 1, 1,
            "fn outer(a: i64[:]) -> i64 {\n    fn inner() -> i64 { return a.len; }\n"
            "    return inner();\n}\nvar g: i64[>..] = [1];\n"
            "fn main() { var l: i64[>..] = [2]; print(outer(g)); print(outer(l)); }\n"),
    Finding("F12", "a nested function capturing a reference rebound between two calls", "rd", 2, 1, 1,
            "fn main() {\n    var a: i64[>..] = [1];\n    var b: i64[>..] = [2, 3];\n"
            "    var r: i64[>..]& .= a;\n    fn rd() -> i64 { return r.len; }\n"
            "    print(rd());\n    r .= b;\n    print(rd());\n}\n"),
    Finding("F13", "two nested functions capturing two different locals", "fa", 1, 1, 1,
            "fn main() {\n    var a: i64[>..] = [1];\n    var b: i64[>..] = [2];\n"
            "    fn fa() -> i64 { return a.len; }\n    fn fb() -> i64 { return b.len; }\n"
            "    print(fa());\n    print(fb());\n}\n"),
    Finding("F14", "a nested function called with an optional narrowed, and not", "show", 2, 1, 1,
            "fn main() {\n    var v: i64 = 5;\n    var o: i64? = &v;\n"
            "    fn show() -> i64 { if o { return o; } return 0; }\n"
            "    print(show());\n    if o { print(show()); }\n}\n"),
    Finding("F15", "an optional parameter given a plain variable, and an optional one", "f", 2, 1, 1,
            "fn f(a: i64?) -> i64 { if a { return a; } return 0; }\n"
            "fn main() { var l: i64 = 2; var n: i64? = null; print(f(l)); print(f(n)); }\n"),
    Finding("F16", "untyped parameters given a literal or a variable, each", "f", 4, 1, 1,
            "fn f(a, b) { return a + b; }\nfn main() { var x: i64 = 1; "
            "print(f(1, 2)); print(f(x, 2)); print(f(1, x)); print(f(x, x)); }\n"),
    Finding("F17", "the same literal parameters given different literal values", "f", 1, 1, 1,
            "fn f(a, b) { return a + b; }\nfn main() { print(f(1, 2)); print(f(3, 4)); }\n"),
    Finding("F18", "two resizable references: two arrays, and one array twice, with a shrink",
            "f", 2, 1, 2,
            "fn f(a: i64[>..<]&, b: i64[>..<]&) -> i64 { let k = a.len; b.pop(); return a[k - 2]; }\n"
            "fn main() { var x: i64[>..<] = [1, 2, 3]; var y: i64[>..<] = [4, 5, 6]; "
            "print(f(x, y)); print(f(x, x)); }\n"),
    Finding("F19", "a `reusable` pool, and a plain array, as a resizable reference", "f", 2, 1, 2,
            "fn f(p: i64[>..]&) -> i64 { p.push(1); return p.len; }\n"
            "reusable var pool: i64[>..] = [];\n"
            "fn main() { var a: i64[>..] = [1]; print(f(a)); print(f(pool)); }\n"),
    Finding("F20", "two bound function values", "apply", 2, 1, 2,
            "fn dbl(x: i64) -> i64 { return x * 2; }\nfn tpl(x: i64) -> i64 { return x * 3; }\n"
            "fn apply<F>(x: i64) -> i64 { return F(x); }\n"
            "fn main() { print(apply(1, dbl)); print(apply(1, tpl)); }\n"),
    Finding("F21", "two element types", "f", 2, 2, 2,
            "fn f<T>(xs: T[:]) -> i64 { return xs[0]; }\n"
            "fn main() { var a: i64[>..] = [1]; var b: i32[>..] = [2]; print(f(a)); print(f(b)); }\n"),
    Finding("F22", "a result consumed as a value and as an element run", "mk", 1, 1, 2,
            "fn mk() -> i64[] { return [1, 2, 3]; }\n"
            "fn main() { var a: i64[>..] = []; a.append(mk()); "
            "var rows: i64[][>..] = []; rows.push(mk()); print(a.len + rows.len); }\n"),
    Finding("F23", "a return propagated to two targets", "relay", 2, 1, 2,
            "fn finish() { return 7 from choose; }\nfn relay() { finish(); }\n"
            "fn choose<T>(x: T) -> T { relay(); return x; }\n"
            "fn main() { var w: i64 = 1; var s: u8 = 2; print(choose(w)); print(choose(s)); }\n"),
    Finding("F24", "a mutually recursive pair under a global and a local root", "ping", 2, 1, 1,
            "recursive fn ping(a: i64[:], n: i64) -> i64 { if n == 0 { return a.len; } "
            "return pong(a, n - 1); }\n"
            "recursive fn pong(a: i64[:], n: i64) -> i64 { if n == 0 { return a.len + 1; } "
            "return ping(a, n - 1); }\nvar g: i64[>..] = [1];\n"
            "fn main() { var l: i64[>..] = [2]; print(ping(g, 3)); print(ping(l, 3)); }\n"),
]


def observe(goose, finding, work):
    """(specializations, distinct printed bodies, implementations) of the
    finding's function, or an error text."""
    src = work / f"{finding.id}.goose"
    src.write_text(finding.program, encoding="utf-8")
    r = subprocess.run([goose, "-O0", "--specs", "--check", src], capture_output=True, text=True)
    if r.returncode:
        return r.stdout + r.stderr
    specs, _ = gen.spec_counts(r.stdout + r.stderr)
    cfile = work / f"{finding.id}.c"
    r = subprocess.run([goose, "-O0", "-o", cfile, src], capture_output=True, text=True)
    if r.returncode:
        return r.stdout + r.stderr
    impl = cfuncs.implementations(cfile.read_text(encoding="utf-8"))
    n, bodies = specs.get(finding.function, (0, 0))
    return n, bodies, impl.get(finding.function, 0)


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--goose", required=True)
    ap.add_argument("--markdown", action="store_true", help="print the README table")
    a = ap.parse_args()
    bad = 0
    rows = []
    scratch = Path(__file__).resolve().parents[2] / ".work"
    scratch.mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(dir=scratch) as d:
        for f in FINDINGS:
            got = observe(a.goose, f, Path(d))
            want = (f.specs, f.bodies, f.implementations)
            if got != want:
                bad += 1
                print(f"{f.id} {f.variation}: observed {got}, expected {want}", file=sys.stderr)
            rows.append((f, got))
    if a.markdown:
        print("| Id | Variation of the call | specializations | printed bodies identical | "
              "emitted C identical |\n|---|---|---|---|---|")
        for f, _ in rows:
            c = "n/a" if f.specs == 1 and f.implementations == 1 else (
                "yes" if f.implementations == 1 else "no")
            print(f"| {f.id} | {f.variation} (`{f.function}`) | {f.specs} | "
                  f"{'yes' if f.bodies == 1 else 'no'} | {c} |")
    print(f"{len(FINDINGS) - bad} of {len(FINDINGS)} findings agree with the compiler")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
