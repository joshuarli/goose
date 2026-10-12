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

The same parameters always produce byte-identical files. New kinds of
member (cases that must stay distinct, source edits) are added as further
Member subclasses contributing declarations, calls, output and counts; the
assembly in build() does not change.
"""

import argparse
import json
import sys
from pathlib import Path

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


class Member:
    """One part of the family. A member contributes global declarations,
    statements inside main, the lines main prints, and its share of the
    expected counts."""

    def globals(self):
        return []

    def body(self):
        return []

    def output(self):
        return []

    def count(self, counts):
        pass


class SliceHelpers(Member):
    """M helpers per type, each with a distinct body, each called under K
    root contexts. Helper h of any type returns `values[0] + (h + 1)`.

    Context k of a type is a global array when k is even and otherwise a
    local array declared `depth` blocks deep in main. Every context holds
    the single value value(k)."""

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


class MainFunction(Member):
    def count(self, c):
        c.source_functions += 1
        c.implementations_after_sharing += 1
        c.baseline_specializations += 1


def indent(lines):
    out, depth = [], 1
    for line in lines:
        if line == "}":
            depth -= 1
        out.append("    " * depth + line)
        if line == "{":
            depth += 1
    return out


def build(helpers, contexts, types):
    members = [SliceHelpers(helpers, contexts, types), MainFunction()]
    counts = Counts()
    for m in members:
        m.count(counts)
    src = []
    for m in members:
        src += m.globals()
    src += ["", "fn main() {", "    var acc: i64 = 0;"]
    for m in members:
        src += indent(m.body())
    src.append("}")
    out = [line for m in members for line in m.output()]
    params = {"helpers": helpers, "contexts": contexts, "types": list(types)}
    expected = {"parameters": params, **counts.as_dict()}
    return "\n".join(src) + "\n", "\n".join(out) + "\n", expected


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--helpers", type=int, default=1)
    ap.add_argument("--contexts", type=int, default=2)
    ap.add_argument("--types", type=int, default=1)
    ap.add_argument("--out", required=True, help="directory to write into")
    a = ap.parse_args()
    if not 1 <= a.helpers <= MAX_HELPERS:
        ap.error(f"--helpers must be 1..{MAX_HELPERS}")
    if a.contexts < 1:
        ap.error("--contexts must be at least 1")
    if not 1 <= a.types <= len(INT_TYPES):
        ap.error(f"--types must be 1..{len(INT_TYPES)}")
    source, output, expected = build(a.helpers, a.contexts, INT_TYPES[:a.types])
    out = Path(a.out)
    out.mkdir(parents=True, exist_ok=True)
    (out / "main.goose").write_text(source, encoding="utf-8", newline="\n")
    (out / "main.out").write_text(output, encoding="utf-8", newline="\n")
    (out / "expected.json").write_text(json.dumps(expected, indent=2) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    sys.exit(main())
