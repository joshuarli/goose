#!/usr/bin/env python3
"""Deterministic generator of a public synthetic Goose workload.

The family grows from a two-context program: a helper taking a slice is
called with a global growable array and with a local one, and the checker
specializes the helper once per root context. Parameters scale the family:

  --helpers M   distinct helper bodies per element type
  --contexts K  root contexts each helper is called under (distinct globals
                and locals at different block depths)
  --types T     element types, taken in order from INT_TYPES

Output directory contents:
  main.goose     the program
  main.out       the stdout the program must print
  expected.json  the counts the generator predicts

The same parameters always produce byte-identical files. Further kinds of
member are Member subclasses (model.py) contributing declarations, calls,
output and expectations; the assembly in build() does not change. Without
the flags below the output is exactly the two-context program above.

  --shareable N      N copies of each member whose calling contexts multiply
                     specializations of a function with one printed body
  --root-params P    slice parameters of the root-pattern member (2..4)
  --distinct         one instance of each case that must stay distinct
  --edit-targets     the functions the source edits are about
  --edit ID          the program after that edit (implies --edit-targets);
                     --list-edits names them
  --verify GOOSE     check the written program and expected.json against
                     that compiler: specializations from --specs, distinct
                     implementations from the emitted C, and the output of
                     --jit
"""

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import cfuncs  # noqa: E402
import edits  # noqa: E402
import family  # noqa: E402
from model import FnExpect, Member, indent  # noqa: E402

# Integer types that widen implicitly to i64, so every result can be summed
# into one i64 accumulator without a cast.
INT_TYPES = ("i64", "i32", "i16", "i8", "u32", "u16", "u8")

# Element values stay small and the helper constants are capped so that
# value + constant fits the narrowest type (i8).
MAX_HELPERS = 100
BLOCK_DEPTHS = 4


class Counts:
    """What the generator predicts about the program it writes."""

    def __init__(self):
        self.source_functions = 0
        self.helper_functions = 0
        self.checked_contexts_per_helper = 0
        self.checked_contexts_total = 0
        self.implementations_after_sharing = 0
        # What the baseline compiler's `typechecked ok: N specialization(s)`
        # line counts, not the generator's own notion of a context: the
        # checker keys a helper's specialization on whether its slice
        # argument is rooted in a global or in a local, so contexts of one
        # kind share a specialization.
        self.baseline_specializations = 0

    def as_dict(self):
        return dict(vars(self))


class SliceHelpers(Member):
    """M helpers per type, each with a distinct body, each called under K
    root contexts. Helper h of any type returns `values[0] + (h + 1)`.

    Context k of a type is a global array when k is even and otherwise a
    local array declared `depth` blocks deep in main. Every context holds
    the single value value(k)."""

    kind = "shareable"
    name = "slice_helpers"

    def __init__(self, helpers, contexts, types):
        self.m, self.k, self.types = helpers, contexts, types

    @staticmethod
    def value(k):
        return k % 7 + 1

    @staticmethod
    def depth(k):
        return k // 2 % BLOCK_DEPTHS + 1

    @staticmethod
    def helper(h, t):
        return f"first_{t}_{h}"

    def global_name(self, t, k):
        return f"g_{t}_{k}"

    def globals(self):
        lines = []
        for t in self.types:
            for h in range(self.m):
                name = self.helper(h, t)
                lines.append(f"fn {name}(values: {t}[:]) -> {t} {{ return values[0] + {h + 1}; }}")
            for k in range(0, self.k, 2):
                lines.append(f"var {self.global_name(t, k)}: {t}[>..] = [{self.value(k)}];")
        return lines

    def calls(self, t, array):
        return [f"acc += {self.helper(h, t)}({array});" for h in range(self.m)]

    def body(self):
        lines = []
        for t in self.types:
            for k in range(self.k):
                if k % 2 == 0:
                    lines += self.calls(t, self.global_name(t, k))
                else:
                    d = self.depth(k)
                    lines += ["{"] * d
                    lines.append(f"var l_{t}_{k}: {t}[>..] = [{self.value(k)}];")
                    lines += self.calls(t, f"l_{t}_{k}")
                    lines += ["}"] * d
                lines.append("print(acc);")
        return lines

    def output(self):
        lines = []
        # The accumulator runs across types, as main's does.
        acc = 0
        for t in self.types:
            for k in range(self.k):
                acc += sum(self.value(k) + h + 1 for h in range(self.m))
                lines.append(str(acc))
        return lines

    def count(self, c):
        c.helper_functions += self.m * len(self.types)
        c.source_functions += self.m * len(self.types)
        c.checked_contexts_per_helper = self.k
        c.checked_contexts_total += self.m * len(self.types) * self.k
        # Contexts differ only in the argument's root, never in the body.
        # Context 0 is a global and context 1 a local, so with two or more
        # contexts each helper has exactly two specializations.
        c.baseline_specializations += self.m * len(self.types) * min(self.k, 2)
        c.implementations_after_sharing += self.m * len(self.types)


    def functions(self):
        # A local root removes a bounds check that a global root keeps, so
        # the two bodies differ in the C until a later pass; one body is
        # the most a merge can reach. Each helper is inlined away at -O2.
        return [FnExpect(self.helper(h, t), min(self.k, 2), 1, 1, exact=False, inlined_at_o2=True,
                         note="bounds-check elimination differs between a global and a local root")
                for t in self.types for h in range(self.m)]


class MainFunction(Member):
    def count(self, c):
        c.source_functions += 1
        c.implementations_after_sharing += 1
        c.baseline_specializations += 1


def build(helpers, contexts, types, shareable=0, root_params=2, distinct=False, edit_targets=False,
          edit=None):
    """(main.goose text, main.out text or None, expected, extra files).
    `shareable` is the number of copies of each shareable member; the other
    arguments after `types` select further members."""
    members = [SliceHelpers(helpers, contexts, types)]
    full = shareable or distinct or edit_targets or edit
    if shareable:
        members += [family.RootPatterns(root_params, shareable), family.ConstRefs(shareable),
                    family.LiteralParams(shareable), family.NestedFunctions(shareable)]
    if distinct:
        members.append(family.Distinct())
    if edit_targets or edit:
        members.append(edits.EditTargets(edit))
    members.append(MainFunction())
    counts = Counts()
    for m in members:
        m.count(counts)
    src = [line for m in members for line in m.imports()]
    for m in members:
        src += m.globals()
    src += ["", "fn main() {", "    var acc: i64 = 0;"]
    for m in members:
        src += indent(m.body())
    src.append("}")
    out = [line for m in members for line in m.output()]
    params = {"helpers": helpers, "contexts": contexts, "types": list(types)}
    expected = {"parameters": params, **counts.as_dict()}
    if full:
        expected["family"] = {"shareable": shareable, "root_params": root_params,
                              "distinct": distinct, "edit_targets": bool(edit_targets or edit)}
        # The counts above add every member's functions: the totals are
        # exact for specializations, and implementations are a lower bound
        # wherever a member's function is not marked exact.
        expected["implementations_provisional"] = any(
            not f.exact for m in members for f in m.functions())
        expected["members"] = {
            m.name: {"kind": m.kind,
                     "functions": {f.name: f.as_dict() for f in m.functions()},
                     "pairs": m.pairs()}
            for m in members if m.functions()}
    runs = True
    if edit:
        e = edits.EDITS[edit]
        expected["edit"] = {"id": e.id, "title": e.title, "changed_functions": list(e.changed),
                            "outcome": e.outcome, "message": e.message,
                            "sequence": list(e.sequence), "why": e.why}
        runs = e.outcome != "error"
    files = {}
    for m in members:
        files.update(m.files())
    text = "\n".join(src) + "\n"
    return text, ("\n".join(out) + "\n") if runs else None, expected, files


def run(argv):
    r = subprocess.run([str(a) for a in argv], capture_output=True, text=True, errors="replace")
    return r.returncode, r.stdout, r.stderr


def spec_counts(text):
    """{function: (specializations, distinct printed bodies)} and the total
    the compiler reports, from `--specs` output."""
    by = {}
    for block in re.split(r"^// spec \d+:[^\n]*\n", text, flags=re.M)[1:]:
        block = re.split(r"\n(?:typechecked ok|parsed ok|bce:)", block)[0].rstrip()
        by.setdefault(re.match(r"fn (\w+)", block).group(1), []).append(block)
    total = re.search(r"typechecked ok: (\d+) specialization", text)
    return {k: (len(v), len(set(v))) for k, v in by.items()}, int(total.group(1)) if total else None


def verify(goose, out_dir):
    """Problems found comparing the program in out_dir with its
    expected.json, by running the compiler. A list of text lines."""
    out_dir = Path(out_dir).resolve()
    expected = json.loads((out_dir / "expected.json").read_text(encoding="utf-8"))
    source = out_dir / "main.goose"
    problems = []
    edit = expected.get("edit")
    if edit and edit["outcome"] == "error":
        code, so, se = run([goose, "-O0", "--check", source])
        if code == 0 or edit["message"] not in so + se:
            problems.append(f"expected a compile error naming {edit['message']!r}; exit {code}")
        return problems
    code, so, se = run([goose, "-O0", "--specs", "--check", source])
    if code:
        return [f"does not compile: {(so + se).strip()[:300]}"]
    specs, total = spec_counts(so + se)
    if edit and edit["outcome"] == "warning" and edit["message"] not in so + se:
        problems.append(f"expected a warning naming {edit['message']!r}")
    if not edit or edit["outcome"] != "warning":
        if "warning:" in so + se:
            problems.append("unexpected warning")
    if total != expected["baseline_specializations"]:
        problems.append(f"typechecked {total} specializations, expected "
                        f"{expected['baseline_specializations']}")
    functions = {n: f for m in expected.get("members", {}).values() for n, f in m["functions"].items()}
    for name, f in functions.items():
        got = specs.get(name, (0, 0))
        if got != (f["specializations"], f["distinct_spec_bodies"]):
            problems.append(f"{name}: (specializations, distinct bodies) {got}, expected "
                            f"({f['specializations']}, {f['distinct_spec_bodies']})")
    for level in (0, 2):
        cfile = out_dir / f"verify-O{level}.c"
        code, so, se = run([goose, f"-O{level}", "-o", cfile, source])
        if code:
            problems.append(f"-O{level} emission failed: {(so + se).strip()[:300]}")
            continue
        impl = cfuncs.implementations(cfile.read_text(encoding="utf-8"))
        for name, f in functions.items():
            if level == 2 and f["inlined_at_o2"]:
                continue
            got = impl.get(name, 0)
            want = f["implementations"]
            if got != want if f["implementations_exact"] else got < want:
                problems.append(f"-O{level} {name}: {got} implementations, expected "
                                f"{'' if f['implementations_exact'] else 'at least '}{want}")
    if (out_dir / "main.out").exists():
        code, so, se = run([goose, "--jit", source])
        if code or so != (out_dir / "main.out").read_text(encoding="utf-8"):
            problems.append(f"--jit output differs from main.out (exit {code})")
    return problems


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--helpers", type=int, default=1)
    ap.add_argument("--contexts", type=int, default=2)
    ap.add_argument("--types", type=int, default=1)
    ap.add_argument("--shareable", type=int, default=0)
    ap.add_argument("--root-params", type=int, default=2)
    ap.add_argument("--distinct", action="store_true")
    ap.add_argument("--edit-targets", action="store_true")
    ap.add_argument("--edit", choices=sorted(edits.EDITS))
    ap.add_argument("--list-edits", action="store_true")
    ap.add_argument("--verify", metavar="GOOSE")
    ap.add_argument("--out", help="directory to write into")
    a = ap.parse_args()
    if a.list_edits:
        for e in edits.EDITS.values():
            print(f"{e.id}\t{e.title}")
        for k, why in edits.NOT_SOURCE_EDITS.items():
            print(f"{k}\tnot a source edit: {why}")
        return 0
    if not a.out:
        ap.error("--out is required")
    if not 1 <= a.helpers <= MAX_HELPERS:
        ap.error(f"--helpers must be 1..{MAX_HELPERS}")
    if a.contexts < 1:
        ap.error("--contexts must be at least 1")
    if not 1 <= a.types <= len(INT_TYPES):
        ap.error(f"--types must be 1..{len(INT_TYPES)}")
    if not 2 <= a.root_params <= 4:
        ap.error("--root-params must be 2..4")
    if a.shareable < 0:
        ap.error("--shareable must not be negative")
    source, output, expected, files = build(a.helpers, a.contexts, INT_TYPES[:a.types],
                                            a.shareable, a.root_params, a.distinct,
                                            a.edit_targets, a.edit)
    out = Path(a.out)
    out.mkdir(parents=True, exist_ok=True)
    (out / "main.goose").write_text(source, encoding="utf-8", newline="\n")
    if output is not None:
        (out / "main.out").write_text(output, encoding="utf-8", newline="\n")
    for name, text in files.items():
        (out / name).write_text(text, encoding="utf-8", newline="\n")
    (out / "expected.json").write_text(json.dumps(expected, indent=2) + "\n", encoding="utf-8")
    if a.verify:
        problems = verify(a.verify, out)
        for p in problems:
            print(f"verify: {p}", file=sys.stderr)
        return 1 if problems else 0
    return 0


if __name__ == "__main__":
    sys.exit(main())
