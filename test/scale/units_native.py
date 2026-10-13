#!/usr/bin/env python3
"""Programs with C of their own, built in units.

  python test/scale/units_native.py --goose GOOSE [--work DIR]

The stand-in under test/scale/native/ has a header like the one of a large
program with a lot of C: it refuses the separate-runtime forms with `#error`,
reads a static table of the runtime's implementation, defines `static`
functions that the program calls as `extern fn`, and spells a slice of the
program's struct by its single-file name. Checks, each by comparing with the
single-file build of the same program:

  * output: the single-file standalone build, `--emit-units` linked by hand,
    and `goose build --units` (given only `--include`) print the same;
  * names: every generated type name a header can see in single-file output
    that is reachable from an extern signature, or derived from such a type,
    is declared in the native-support unit with the same spelling, and the
    unit invents no other spelling of a type;
  * reuse: editing the header recompiles the native-support unit and nothing
    else; editing a Goose function body recompiles that function's code
    unit, and never the native-support unit.

Prints one line per check and exits 1 if any fails.
"""

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
sys.path.insert(0, str(ROOT / "scripts"))
import toolchain as tc  # noqa: E402

STANDIN = HERE / "native"


def run(argv, **kw):
    return subprocess.run([str(a) for a in argv], capture_output=True, text=True, errors="replace", **kw)


def type_names(types_text):
    """The names a section of C declares as types."""
    names = set()
    for m in re.finditer(r"^typedef\s+struct\s+(\w+)\s+\w+;", types_text, re.M):
        names.add(m.group(1))
    for m in re.finditer(r"}\s*(\w+);", types_text):
        names.add(m.group(1))
    for m in re.finditer(r"^typedef\s+[^{;]*?\s(\w+);", types_text, re.M):
        names.add(m.group(1))
    return names


def single_file_view(c_text):
    """(the type names a header can see in single-file output, the extern
    prototype text): the types are declared before the headers are included."""
    types = c_text[c_text.index("/* ---- types ---- */"):c_text.index("/* ---- data ---- */")]
    protos_at = c_text.find("/* ---- extern prototypes ---- */")
    protos = c_text[protos_at:c_text.index("/* ---- prototypes ---- */")] if protos_at >= 0 else ""
    return type_names(types), types, protos


def reachable(names, types_text, protos):
    """The type names reachable from the extern prototypes: those they spell,
    the types their bodies spell, and the types built over any of them."""
    bodies = {}
    for m in re.finditer(r"(?s)(?:typedef\s+struct\s*\{.*?\}\s*(\w+);|struct\s+(\w+)\s*\{.*?\n\};)", types_text):
        bodies[m.group(1) or m.group(2)] = m.group(0)
    found = {n for n in names if re.search(rf"\b{n}\b", protos)}
    changed = True
    while changed:
        changed = False
        for n in list(names):
            body = bodies.get(n, "")
            body = re.sub(rf"\b{n}\b", "", body, count=1)
            below = {m for m in names if m in found and re.search(rf"\b{m}\b", body)}
            if n in found:
                add = {m for m in names if m != n and re.search(rf"\b{m}\b", body)}
            else:
                add = {n} if below else set()
            if not add <= found:
                found |= add
                changed = True
    return found


class Checks:
    def __init__(self):
        self.bad = []

    def say(self, ok, what):
        print(f"{'PASS' if ok else 'FAIL'} {what}")
        if not ok:
            self.bad.append(what)


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--goose", required=True)
    ap.add_argument("--work")
    a = ap.parse_args()
    goose = Path(a.goose).resolve()
    work = Path(a.work).resolve() if a.work else ROOT / ".work" / "units_native"
    shutil.rmtree(work, ignore_errors=True)
    prog = work / "prog"
    shutil.copytree(STANDIN, prog)
    home = work / "home"
    env = dict(os.environ, GOOSE_HOME=str(home))
    cc = tc.test_cc("native")
    checks = Checks()

    # Single file.
    c = work / "single.c"
    r = run([goose, "--standalone", "--include", "standin.h", "-o", c, "standin.goose"], cwd=prog)
    checks.say(r.returncode == 0, "single-file standalone output is written")
    shutil.copy(prog / "standin.h", work / "standin.h")
    ok, log = cc.compile(c, work / "single", opt=1, extra=[f"-I{prog}"])
    want = run([work / "single"]).stdout
    checks.say(ok and want == "46\n33\n16\n", f"single-file output runs: {want!r}")
    names, types, protos = single_file_view(c.read_text())

    # --emit-units, linked by hand with no runtime object.
    units = work / "emitted"
    r = run([goose, "-O1", "--include", "standin.h", "--emit-units", units, "standin.goose"], cwd=prog)
    checks.say(r.returncode == 0 and (units / "native.c").exists(), "--emit-units writes a native-support unit")
    sources = sorted(units.glob("*.c"))
    ok, log = cc.compile(sources, work / "emitted.exe", opt=1, strict_decls=True, extra=[f"-I{units}"])
    checks.say(ok, f"the emitted units compile and link without a runtime object: {log[-200:]}")
    checks.say(ok and run([work / "emitted.exe"]).stdout == want, "the emitted units print what single-file output prints")

    # Names.
    native_text = (units / "native.c").read_text()
    # The generated types: the packed block holding the core types.
    core = native_text.index("typedef struct { uint8_t *base; int64_t len; } gs_rhdr;")
    a_ = native_text.rindex("#pragma pack(push, 1)", 0, core)
    native_types = native_text[a_:native_text.index("#pragma pack(pop)", a_)]
    visible = type_names(native_types)
    need = reachable(names, types, protos)
    checks.say(bool(need) and "sl_Point_g" in need, f"types reachable from extern signatures in single-file output: {sorted(need)}")
    missing = need - visible
    checks.say(not missing, f"the native-support unit declares each of them with the same spelling (missing {sorted(missing)})")
    invented = visible - names
    checks.say(not invented, f"it invents no other spelling of a type (extra {sorted(invented)})")

    # The driver, and reuse.
    def build(label):
        report = work / f"{label}.json"
        r = run([goose, "build", "--units", "--verify-reuse", "--include", "standin.h",
                 "--build-report", report, "-o", work / "driven.exe", "standin.goose"], cwd=prog, env=env)
        data = json.loads(report.read_text()) if report.exists() else {}
        return r, data.get("extensions", {}).get("native_compile", {})

    r, n = build("cold")
    checks.say(r.returncode == 0 and run([work / "driven.exe"]).stdout == want,
               f"goose build --units with only --include builds and prints the same: {r.stderr[-200:]}")
    compiled = lambda n: sorted({u for c in n.get("native_compiler_invocations", []) for u in c["units"]})
    checks.say("native.c" in compiled(n), "a cold build compiles the native-support unit")
    r, n = build("warm")
    checks.say(r.returncode == 0 and n.get("no_op") is False and not compiled(n), "a second build compiles nothing")

    header = prog / "standin.h"
    header.write_text(header.read_text() + "\n/* an edit to the header */\n")
    r, n = build("header")
    checks.say(r.returncode == 0 and compiled(n) == ["native.c"],
               f"editing the header recompiles the native-support unit and nothing else: {compiled(n)}")
    checks.say(run([work / "driven.exe"]).stdout == want, "and the program still prints the same")

    source = prog / "standin.goose"
    source.write_text(source.read_text().replace("return standin_sum(points);", "return standin_sum(points) + 0;"))
    r, n = build("body")
    code = [u for u in compiled(n) if not u.endswith(".loc.c")]
    checks.say(r.returncode == 0 and code and "native.c" not in code and len(code) == 1,
               f"editing a Goose body recompiles that function's unit only: {compiled(n)}")
    checks.say(run([work / "driven.exe"]).stdout == want, "and the program still prints the same")
    print("units_native: " + ("ok" if not checks.bad else f"{len(checks.bad)} failed"))
    return 1 if checks.bad else 0


if __name__ == "__main__":
    sys.exit(main())
