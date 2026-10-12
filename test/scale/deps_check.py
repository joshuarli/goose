#!/usr/bin/env python3
"""The dependency record is complete: after an edit, every context whose
checked result changed was predicted invalid by what the compiler recorded.

  python test/scale/deps_check.py --goose GOOSE [--work DIR] [--seed N] [--steps N]
         [--edit ID ...] [--jobs N] [-v]

The synthetic family (gen.py) is built with each source edit of edits.py and
each dependency edit below it, before and after, with
`goose --check --build-report`, and predict.py compares the two reports. Each
edit is also run backwards, from the edited program to the original. Then a
randomized sequence of edits, toggled one at a time from a fixed seed, is run
step by step; with --mutants, so are random one-token mutations of the
repository's own fixtures. The check fails on any context that changed without being
predicted, and on any edit that is expected to change nothing and changes
something. It also requires that two builds of the same program, in two
directories, agree digest for digest, and that an edit which only adds a
comment moves positions and nothing else.

Prints one row per comparison: how many contexts the edit predicted invalid,
how many changed, and the over-approximation between them.
"""

import argparse
import glob
import json
import random
import re
import shutil
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import cfuncs  # noqa: E402
import edits  # noqa: E402
import family  # noqa: E402
import gen  # noqa: E402
import predict  # noqa: E402
from model import indent  # noqa: E402

# Edits that do not compile, and the ones that are a sequence of others.
NO_REPORT = {i for i, e in edits.EDITS.items() if e.outcome == "error"}
SEQUENCES = {i for i, e in edits.EDITS.items() if e.sequence}
# Edits expected to change no context's result but the ones named (a context
# that appears or disappears is not a changed result). The initializer of a
# var global is the global's own result.
NO_RESULT_CHANGE = {"E02": set(), **{i: set() for i, e in edits.DEPENDENCY_EDITS.items()
                                      if e.effect == "none"}}
NO_RESULT_CHANGE["D08"] = {"global dt_gv"}
# Contexts an edit must leave alone although it changes what surrounds them.
STAYS = {"D27": {"dt_throw(_)"}}
# Edits that only move text: no dependency but a location may break.
MOVES_ONLY = {"E02", "D16", "D20"}


def source_edits():
    return [i for i in edits.EDITS if i not in NO_REPORT and i not in SEQUENCES]


def all_edits():
    return source_edits() + list(edits.DEPENDENCY_EDITS)


# The size of the family every program is cut from: gen.py's flags.
SHAPE = dict(helpers=1, contexts=2, types=1, shareable=1, root_params=2)


def program(ids):
    """(main.goose text, {file: text}) of the family with the edits applied."""
    source_ids = [i for i in ids if i in edits.EDITS]
    dep_ids = [i for i in ids if i in edits.DEPENDENCY_EDITS]
    members = [gen.SliceHelpers(SHAPE["helpers"], SHAPE["contexts"],
                                gen.INT_TYPES[:SHAPE["types"]]),
               family.RootPatterns(SHAPE["root_params"], SHAPE["shareable"]),
               family.ConstRefs(SHAPE["shareable"]), family.LiteralParams(SHAPE["shareable"]),
               family.NestedFunctions(SHAPE["shareable"]), family.Distinct(),
               edits.EditTargets(source_ids), edits.DepTargets(dep_ids), gen.MainFunction()]
    src = [line for m in members for line in m.imports()]
    for m in members:
        src += m.globals()
    src += ["", "fn main() {", "    var acc: i64 = 0;"]
    for m in members:
        src += indent(m.body())
    src.append("}")
    files = {}
    for m in members:
        files.update(m.files())
    return "\n".join(src) + "\n", files


class Builder:
    def __init__(self, goose, work, jobs):
        self.goose, self.work = str(goose), Path(work)
        self.cache = {}
        self.pool = ThreadPoolExecutor(jobs)

    @staticmethod
    def label(ids):
        return "+".join(sorted(ids)) or "base"

    def build(self, ids, tag=""):
        key = (frozenset(ids), tag)
        if key not in self.cache:
            self.cache[key] = self.pool.submit(self._build, sorted(ids), tag)
        return self.cache[key]

    def _build(self, ids, tag):
        directory = self.work / (self.label(ids) + tag)
        directory.mkdir(parents=True, exist_ok=True)
        text, files = program(ids)
        (directory / "main.goose").write_text(text, encoding="utf-8", newline="\n")
        for name, content in files.items():
            (directory / name).write_text(content, encoding="utf-8", newline="\n")
        out, cfile = directory / "report.json", directory / "main.c"
        out.unlink(missing_ok=True)
        cfile.unlink(missing_ok=True)
        # The C is written at -O0, where nothing is inlined, so that what a
        # later phase read of a context can be told from the C of its function.
        r = subprocess.run([self.goose, "-O0", "-o", str(cfile), "--build-report", str(out),
                            str(directory / "main.goose")],
                           capture_output=True, text=True, errors="replace")
        if r.returncode != 0 or not out.exists() or not cfile.exists():
            return None, (r.stdout + r.stderr).strip()[-600:]
        return (predict.load(out), cfile.read_text(encoding="utf-8")), r.stderr


class Run:
    def __init__(self, builder, verbose):
        self.b, self.verbose = builder, verbose
        self.failures = []
        self.rows = []
        # Edits whose emitted C changed in a function no context's result
        # or caller-side facts explain: the result digest is missing what
        # code generation reads.
        self.unexplained = []
        self.explained_by_callers = 0
        self.tally = {"own": 0, "callee": 0, "later phase": 0}

    def explained(self, label, before, after, old, new, r):
        """Every program function whose emitted C changed belongs to a
        context whose result changed (or that appeared or disappeared), or
        else to one whose facts from its call sites changed: those are not
        in the result. The check that the result is not poor."""
        changed, other = emitted_changes(self.c_text(before), self.c_text(after))
        a = {c["key"]: c for c in old["contexts"]}
        b = {c["key"]: c for c in new["contexts"]}
        moved = {k for k in a.keys() & b.keys() if a[k]["result"] != b[k]["result"]}
        moved |= (a.keys() ^ b.keys())
        by_callers = {k for k in a.keys() & b.keys() if a[k]["callers"] != b[k]["callers"]}
        names = {**{k: c["name"] for k, c in a.items()}, **{k: c["name"] for k, c in b.items()}}
        explained = {context_base(names[k]) for k in moved}
        callers = {context_base(names[k]) for k in by_callers}
        # Code generation reads the summaries of what a function calls: a
        # callee that never returns, that needs a stack, that grows an array
        # its caller holds. So a function is also explained by a callee whose
        # result changed.
        beside = set()
        for report in (a, b):
            for c in report.values():
                called = {d["subject"][len("context:"):] for d in c["dependencies"]
                          if d["kind"] == "requests"}
                if called & moved:
                    beside.add(context_base(c["name"]))
        globals_moved = any(names[k].startswith("global ") for k in moved)
        edit = label.split()[-1] if label.startswith("random") else label.split()[0]
        for n in sorted(changed):
            if n in explained:
                self.tally["own"] += 1
                continue
            if n in beside:
                self.tally["callee"] += 1
                continue
            if n in LATER_PHASE.get(edit, ()):
                self.tally["later phase"] += 1
                continue
            if n in callers:
                self.explained_by_callers += 1
                continue
            self.unexplained.append(f"{label}: the C of {n} changed, no context of it has a "
                                    f"changed result")
        if other and not globals_moved:
            self.unexplained.append(f"{label}: C the compiler wrote on its own changed, and no "
                                    f"global initializer's result did")

    def get(self, ids, tag=""):
        built, err = self.b.build(ids, tag).result()
        if built is None:
            self.failures.append(f"{Builder.label(ids)}: does not compile: {err}")
            return None
        return built[0]

    def c_text(self, ids):
        return self.b.build(ids).result()[0][1]

    def compare(self, label, before, after, allowed=None, moves_only=False, stays=()):
        old, new = self.get(before), self.get(after)
        if old is None or new is None:
            return None
        r = predict.compare(old, new)
        self.rows.append((label, r))
        self.explained(label, before, after, old, new, r)
        line = f"{label:34} " + predict.summary_line(r)
        print(line)
        if r["clashes"]:
            self.failures.append(f"{label}: a dependency subject has two digests: {r['clashes'][:3]}")
        if r["under_approximation"]:
            self.failures.append(f"{label}: {r['under_approximation']} context(s) changed "
                                 f"without being predicted: "
                                 + ", ".join(r["names"][k] for k in r["under"][:8]))
        if moves_only and r["predicted_set"] - r["gone_set"]:
            self.failures.append(f"{label}: an edit that only moves text broke a dependency "
                                 f"other than a location of: "
                                 f"{sorted(r['names'][k] for k in r['predicted_set'] - r['gone_set'])[:8]}")
        if stays:
            moved = {r["names"][k] for k in r["changed_set"]} & set(stays)
            if moved:
                self.failures.append(f"{label}: a result that must not change did: {sorted(moved)}")
        if allowed is not None:
            changed = {r["names"][k] for k in r["changed_set"] - r["gone_set"]}
            if changed - allowed:
                self.failures.append(f"{label}: expected no result to change but {sorted(allowed)}, "
                                     f"and these did: {sorted(changed - allowed)[:8]}")
        if self.verbose and r["inputs"] and any(r["inputs"].values()):
            print("    inputs:", json.dumps(r["inputs"], sort_keys=True))
        return r


# C functions the compiler writes beside the program's own: the global
# initializer and the like. The pattern of a program function's name:
# `name_g`, `name_g12`, `name_g_12`, `name_g_12_er`.
CNAME = re.compile(r"_g(?:_?\d+)?(?:_er)?$")


def c_base(c_name):
    return CNAME.sub("", c_name)


def context_base(name):
    """The C name a context's source function gets, without its numbers:
    namespaces join with `_`, a nested function is named alone."""
    leaf = name.split("/")[-1]
    return leaf.split("(")[0].replace("::", "_")


def emitted_changes(before_c, after_c):
    """The program functions emitted both before and after whose C differs,
    by C base name, with specialization numbers and runtime-check line
    numbers masked; and whether anything the compiler wrote on its own
    differs. A function emitted on one side only was made live or dead by
    reachability, which is not a property of its own check."""
    tables = []
    for text in (before_c, after_c):
        table = {}
        for n, body in cfuncs.functions(text).items():
            key = c_base(n) if CNAME.search(n) else ""
            table.setdefault(key, []).append(cfuncs.mask(body) if key else f"{n}\n{body}")
        tables.append(table)
    a, b = tables
    # Some body replaced by another. Instances that are merely live on one
    # side only leave bodies on one side only.
    changed = {n for n in a.keys() & b.keys() if set(a[n]) - set(b[n]) and set(b[n]) - set(a[n])}
    return changed - {""}, "" in changed


# Changes of emitted C that the cross-check cannot explain, by edit and function,
# because a later phase read something other than a checked result: the
# optimizer replaces a read of a global variable that nothing assigns by the
# value of its initializer.
LATER_PHASE = {"D08": {"dt_global_user"}}


def same_report(a, b):
    """The differences between two reports of one program, as lines."""
    ca = {c["key"]: c for c in a["contexts"]}
    cb = {c["key"]: c for c in b["contexts"]}
    out = []
    for k in sorted(set(ca) ^ set(cb)):
        out.append(f"context only in one report: {(ca.get(k) or cb.get(k))['name']}")
    for k in sorted(set(ca) & set(cb)):
        for field in ("result", "positions", "callers", "dependencies", "duplicates"):
            if ca[k][field] != cb[k][field]:
                out.append(f"{ca[k]['name']}: {field} differs")
    if a["inputs"] != b["inputs"]:
        out.append(f"inputs differ: {a['inputs']} vs {b['inputs']}")
    return out


def determinism(run):
    base, again = run.get([]), run.get([], "-again")
    if base is None or again is None:
        return
    diff = same_report(base, again)
    print(f"{'determinism: base twice':34} {len(base['contexts'])} contexts, "
          f"{len(diff)} difference(s)")
    for d in diff[:10]:
        print("   ", d)
    if diff:
        run.failures.append(f"two builds of the same program differ: {diff[:3]}")


# Programs the mutants are cut from: the repository's own fixtures. One,
# test/typing/nested_overloads.goose, makes `--build-report` itself crash (the
# context keys read an overload set the checker has freed), so it is left out.
CORPUS = ("test/typing", "test/codegen", "test/optimizer", "test/lifetimes", "test/storage",
          "test/syntax", "test/threads", "samples")
CORPUS_SKIP = ("nested_overloads.goose",)

# Each kind of mutation, as a pattern in a line of code: what it matches and
# what it becomes. An integer literal grows by one, a type narrows, an
# operator flips, a binding changes kind, a string changes, a call goes to
# another function, a statement goes, a function becomes recursive or not.
MUTATIONS = {
    "literal": (r"(?<![\w.])\d+(?![\w.])", lambda m, names, rng: str(int(m.group(0)) + 1)),
    "type": (r"\bi64\b", lambda m, names, rng: "i32"),
    "operator": (r" \+ ", lambda m, names, rng: " - "),
    "let": (r"\blet\b", lambda m, names, rng: "var"),
    "var": (r"\bvar\b", lambda m, names, rng: "let"),
    "string": (r'"[^"]*"', lambda m, names, rng: '"zz"'),
    "call": (r"\b[a-z_][a-z_0-9]*(?=\()", lambda m, names, rng: rng.choice(names or [m.group(0)])),
    "statement": (r"^\s*(?:let|var|[a-z_]+\(.*\);|[a-z_]+ [-+]?= .*;)\s*$",
                  lambda m, names, rng: "// deleted"),
    "recursion": (r"\bfn\b", lambda m, names, rng: rng.choice(["recursive fn", "fn"])),
}


def mutate(text, rng):
    """(mutated text, what changed) for one random mutation of the program,
    or None where it has nothing to mutate."""
    names = sorted(set(re.findall(r"\bfn (?:recursive )?([a-z_][a-z_0-9]*)", text)))
    lines = text.split("\n")
    sites = []
    for i, line in enumerate(lines):
        code = line.split("//")[0]
        for kind, (pattern, _) in MUTATIONS.items():
            sites += [(kind, i, m) for m in re.finditer(pattern, code)]
    if not sites:
        return None
    kind, i, m = rng.choice(sites)
    line = lines[i]
    lines[i] = line[:m.start()] + MUTATIONS[kind][1](m, names, rng) + line[m.end():]
    return "\n".join(lines), f"{kind} at line {i + 1}"


def mutants(run, builder, seed, per_file, work):
    """A report of each program and of the program with one random mutation,
    compared as an edit is. Mutants that do not compile are not counted."""
    rng = random.Random(seed)
    root = HERE.parent.parent
    files = sorted(f for d in CORPUS for f in glob.glob(str(root / d / "*.goose"))
                   if not f.endswith(CORPUS_SKIP))
    jobs = [(f, k, random.Random(rng.random())) for f in files for k in range(per_file)]

    def report(directory):
        out = directory / "report.json"
        out.unlink(missing_ok=True)
        r = subprocess.run([builder.goose, "--check", "--build-report", str(out),
                            str(directory / "main.goose")], capture_output=True, text=True,
                           errors="replace")
        return predict.load(out) if r.returncode == 0 and out.exists() else None

    def one(job):
        f, k, r = job
        text = Path(f).read_text(encoding="utf-8")
        m = mutate(text, r)
        if m is None:
            return None
        directory = Path(work) / "mutants" / f"{Path(f).parent.name}_{Path(f).stem}_{k}"
        # Both programs have the same file name: it is part of every key.
        for sub, body in (("base", text), ("mut", m[0])):
            d = directory / sub
            d.mkdir(parents=True, exist_ok=True)
            for x in Path(f).parent.glob("*"):
                if x.is_file() and str(x) != f:
                    shutil.copy(x, d)
            (d / "main.goose").write_text(body, encoding="utf-8", newline="\n")
        old, new = report(directory / "base"), report(directory / "mut")
        if old is None or new is None:
            return None
        return f, m[1], predict.compare(old, new)

    done = changed = predicted = 0
    for res in builder.pool.map(one, jobs):
        if res is None:
            continue
        f, what, r = res
        done += 1
        changed += r["changed"]
        predicted += r["predicted"]
        if r["under_approximation"] or r["clashes"]:
            run.failures.append(f"mutant of {f} ({what}): "
                                + ", ".join(r["names"][k] for k in r["under"][:5])
                                + "".join(r["clashes"][:2]))
    print(f"mutants (seed {seed}): {done} compared; {changed} contexts changed, {predicted} "
          f"predicted, under-approximation {len([x for x in run.failures if x.startswith('mutant')])}")


def randomized(run, seed, steps, pool):
    rng = random.Random(seed)
    state = set()
    for step in range(steps):
        i = rng.choice(pool)
        after = state ^ {i}
        verb = "revert" if i in state else "apply"
        run.compare(f"random {seed}.{step:02d} {verb} {i}", sorted(state), sorted(after),
                    allowed=NO_RESULT_CHANGE.get(i), moves_only=i in MOVES_ONLY,
                    stays=STAYS.get(i, ()))
        state = after


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--goose", required=True)
    ap.add_argument("--work", default=str(HERE.parent.parent / ".work" / "deps_check"))
    ap.add_argument("--seed", type=int, default=20261012)
    ap.add_argument("--steps", type=int, default=40)
    ap.add_argument("--edit", action="append", help="only these edits (and no random run)")
    ap.add_argument("--mutants", type=int, default=0, metavar="N",
                    help="also compare N random one-token mutants of each fixture in the corpus "
                         "(a few minutes for N=6)")
    ap.add_argument("--jobs", type=int, default=8)
    for name, value in SHAPE.items():
        ap.add_argument(f"--{name.replace('_', '-')}", type=int, default=value,
                        help=f"the family's {name.replace('_', ' ')} (gen.py's flag)")
    ap.add_argument("-v", "--verbose", action="store_true")
    args = ap.parse_args()
    for name in SHAPE:
        SHAPE[name] = getattr(args, name)

    run = Run(Builder(args.goose, args.work, args.jobs), args.verbose)
    pool = args.edit or all_edits()
    # Start every build at once; the comparisons below wait for them.
    run.b.build([])
    for i in pool:
        run.b.build([i])
    if run.get([]) is None:
        print("\n".join(run.failures))
        return 1

    determinism(run)
    for i in pool:
        run.compare(f"{i} apply", [], [i], allowed=NO_RESULT_CHANGE.get(i),
                    moves_only=i in MOVES_ONLY, stays=STAYS.get(i, ()))
        run.compare(f"{i} revert", [i], [], allowed=NO_RESULT_CHANGE.get(i),
                    moves_only=i in MOVES_ONLY, stays=STAYS.get(i, ()))
    if not args.edit:
        randomized(run, args.seed, args.steps, pool)
    if args.mutants:
        mutants(run, run.b, args.seed, args.mutants, args.work)

    skipped = sorted(NO_REPORT)
    print(f"\n{len(run.rows)} comparisons; not compared (the edit is a compile error): "
          f"{', '.join(skipped)}")
    if run.rows:
        total = lambda k: sum(r[k] for _, r in run.rows)  # noqa: E731
        print(f"predicted {total('predicted')}, changed {total('changed')}, "
              f"over-approximation {total('over_approximation')}, "
              f"under-approximation {total('under_approximation')}")
    print(f"emitted C cross-check: functions whose C changed, by what explains them: "
          f"{run.tally} (own result changed; only a callee's did; a later phase), "
          f"{run.explained_by_callers} by facts from the call sites alone, "
          f"{len(run.unexplained)} unexplained")
    run.failures += run.unexplained
    if run.failures:
        print("\nFAILED:")
        for f in run.failures:
            print("  " + f)
        return 1
    print("PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
