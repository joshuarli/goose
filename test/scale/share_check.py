#!/usr/bin/env python3
"""--share against the synthetic family's expected implementation counts.

  python test/scale/share_check.py --goose GOOSE [--cc cc] [--work DIR]

Generates families with gen.py and, for each, at -O0 and -O2, emits the C
with `--share` and checks that

  * each source function has as many emitted definitions as `expected.json`
    says it has implementations (exactly, or at least, where the expected
    count is a lower bound; a function the optimizer inlines at -O2 is
    skipped), so every must-stay-distinct case stays distinct and every
    shareable one is one;
  * the program built from that C prints the program's expected output.

Prints one line per violation and exits 1 if there is any.
"""

import argparse
import json
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
sys.path.insert(0, str(HERE))
import cfuncs  # noqa: E402

FAMILIES = [
    ["--shareable", "2", "--distinct"],
    ["--shareable", "1", "--root-params", "3", "--distinct"],
    ["--shareable", "3", "--root-params", "2", "--distinct", "--edit-targets"],
]


def run(cmd, **kw):
    return subprocess.run([str(c) for c in cmd], capture_output=True, text=True, **kw)


def check(goose, cc, tmp, flags):
    bad = []
    d = tmp / "_".join(flags).replace("-", "")
    r = run([sys.executable, HERE / "gen.py", *flags, "--out", d])
    if r.returncode:
        return [f"gen.py {flags}: {r.stderr.strip()}"]
    expected = json.loads((d / "expected.json").read_text())
    functions = {n: f for m in expected["members"].values() for n, f in m["functions"].items()}
    want_out = (d / "main.out").read_text()
    for level in (0, 2):
        c = d / f"share-O{level}.c"
        r = run([goose, f"-O{level}", "--share", "--standalone", "-o", c, d / "main.goose"])
        if r.returncode:
            bad.append(f"{flags} -O{level}: --share failed: {(r.stdout + r.stderr)[-300:]}")
            continue
        defs = {}
        for name in cfuncs.functions(c.read_text()):
            src = cfuncs.source_name(name)
            if src:
                defs[src] = defs.get(src, 0) + 1
        for name, f in functions.items():
            if level == 2 and f["inlined_at_o2"]:
                continue
            got, want = defs.get(name, 0), f["implementations"]
            if got != want if f["implementations_exact"] else got < want:
                bad.append(f"{flags} -O{level} {name}: {got} emitted, expected "
                           f"{'' if f['implementations_exact'] else 'at least '}{want}")
        exe = d / f"share-O{level}"
        r = run([cc, "-w", "-O1", c, "-o", exe, "-lm", "-pthread"])
        if r.returncode:
            bad.append(f"{flags} -O{level}: the C does not compile: {r.stderr[-300:]}")
            continue
        r = run([exe])
        if r.stdout != want_out:
            bad.append(f"{flags} -O{level}: output differs (exit {r.returncode})")
    return bad


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--goose", required=True)
    ap.add_argument("--cc", default="cc")
    ap.add_argument("--work")
    a = ap.parse_args()
    scratch = ROOT / ".work" / "tmp"
    scratch.mkdir(parents=True, exist_ok=True)
    bad = []
    with tempfile.TemporaryDirectory(dir=a.work or scratch) as tmp:
        for flags in FAMILIES:
            bad += check(a.goose, a.cc, Path(tmp), flags)
    for line in bad:
        print(f"share_check: {line}")
    if not bad:
        print(f"share_check: ok ({len(FAMILIES)} families, -O0 and -O2)")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
