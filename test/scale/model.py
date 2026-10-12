"""The parts every family member is built from.

A member contributes global declarations, statements inside main, the lines
main prints, and what the generator predicts about the functions it adds:
how many specializations the checker creates for each (`--specs` at -O0
lists every one), how many of those differ in their printed body, and how
many distinct implementations the emitted C holds once identical bodies are
counted once.
"""

from dataclasses import dataclass


@dataclass(frozen=True)
class FnExpect:
    """What the compiler is expected to do with one source function.

    `specs` is the number of specializations the checker creates and
    `spec_bodies` the number of distinct printed bodies among them.
    `implementations` is the number of distinct emitted bodies once each
    callee is replaced by its class (`cfuncs.classes`); `exact` is false
    where that is only a lower bound, because context-dependent
    optimization may split bodies a later merge would keep apart or
    together. `inlined_at_o2` marks a function the optimizer removes from
    the C at -O2, where no implementation count applies."""

    name: str
    specs: int
    spec_bodies: int
    implementations: int
    exact: bool = True
    inlined_at_o2: bool = False
    note: str = ""

    def as_dict(self):
        d = {"specializations": self.specs, "distinct_spec_bodies": self.spec_bodies,
             "implementations": self.implementations,
             "implementations_exact": self.exact,
             "inlined_at_o2": self.inlined_at_o2}
        if self.note:
            d["note"] = self.note
        return d


class Member:
    """One part of the family."""

    # How the member is reported in expected.json.
    kind = "shareable"
    name = "member"

    def globals(self):
        return []

    def body(self):
        return []

    def output(self):
        return []

    def imports(self):
        return []

    def files(self):
        """{file name: text} of the files beside main.goose."""
        return {}

    def functions(self):
        """The FnExpect of every source function this member declares."""
        return []

    def pairs(self):
        """Specializations that must stay separate implementations, or share
        only together: [{"functions": [...], "outcome": ..., "reason": ...}]."""
        return []

    def count(self, counts):
        fns = self.functions()
        counts.source_functions += len(fns)
        counts.baseline_specializations += sum(f.specs for f in fns)
        counts.implementations_after_sharing += sum(f.implementations for f in fns)


def indent(lines):
    out, depth = [], 1
    for line in lines:
        if line == "}":
            depth -= 1
        out.append("    " * depth + line)
        if line == "{":
            depth += 1
    return out
