#!/usr/bin/env python3
"""Which checked contexts an edit could have changed, and which it did.

  python test/scale/predict.py OLD.json NEW.json [--list N] [--json]

OLD and NEW are `goose --build-report` files of a program before and after an
edit (extensions.dependencies). A context is named by its key. From the two:

  predicted  the contexts present in both with a dependency of the old report
             that the new program does not bear out, and the contexts that
             appear or disappear. A dependency is (kind, subject, digest);
             it is borne out when the new report says the same digest of the
             subject, in whatever context. A subject nothing in the new
             program depends on counts as not borne out. What the new context
             depends on is not consulted: a reused result would not know it;
  changed    the contexts whose result digest differs, and the contexts that
             appear or disappear.

Positions are kept apart. A dependency of kind `location` says where a
declaration's nodes are; the result digest leaves positions out and a second
digest, `positions`, holds them. So two checks are made:

  * every context whose result changed is predicted by a dependency that is
    not a location, and
  * every context whose result or positions changed is predicted by some
    dependency.

An observation (a subject starting `observed:`) is what one context's check
found of a global's provenance, which depends on what was checked before it:
only the same context's entry in the new report can bear it out.

A context that changed without being predicted is an under-approximation: a
dependency the compiler did not record. It is listed and the exit status is 1.
The over-approximation is the predicted contexts that did not change; a
recorder that predicts everything never fails the check and says nothing, so
its size is printed beside the rest.
"""

import argparse
import json
import sys

FORMAT = "goose-dependencies/1"


def load(path):
    with open(path, encoding="utf-8") as f:
        report = json.load(f)
    deps = (report.get("extensions") or {}).get("dependencies")
    if not deps or deps.get("format") != FORMAT:
        raise SystemExit(f"{path}: no {FORMAT} section")
    return deps


OBSERVED = "observed:"


def evaluate(report):
    """What the program the report describes says of each dependency
    subject: {(kind, subject): digest}. A subject's digest is a property of
    the program, whichever context asks, so two contexts must agree on it.
    Also the disagreements found. An observation (a subject starting
    `observed:`) is what one context's check saw when it ran, which depends on
    what was checked before it; it is not a fact about the program and is
    left out."""
    value, clashes = {}, []
    for c in report["contexts"]:
        for d in c["dependencies"]:
            if d["subject"].startswith(OBSERVED):
                continue
            k = (d["kind"], d["subject"])
            if value.setdefault(k, d["digest"]) != d["digest"]:
                clashes.append(f"{k[0]} {k[1]}: {c['name']} reads another digest")
    return value, clashes


def broken(old, new, value, location):
    """The dependencies of the old context, as the old report recorded them,
    that the new program does not bear out: its digest differs, or no context
    of the new program depends on the subject at all, so it cannot be told.
    An observation is borne out only by the new context's own: nothing but
    checking it again says what it would see."""
    mine = {(d["kind"], d["subject"]): d["digest"] for d in new["dependencies"]}
    out = set()
    for d in old["dependencies"]:
        if (d["kind"] == "location") != location:
            continue
        k = (d["kind"], d["subject"])
        now = mine.get(k) if d["subject"].startswith(OBSERVED) else value.get(k)
        if now != d["digest"]:
            out.add(k)
    return out


def compare(old, new):
    """The sets of context keys, and the details of every context in both."""
    a = {c["key"]: c for c in old["contexts"]}
    b = {c["key"]: c for c in new["contexts"]}
    appeared, disappeared = set(b) - set(a), set(a) - set(b)
    common = set(a) & set(b)
    # A recorded dependency still holds when the new program says the same of
    # its subject. What the new context itself depends on is not consulted:
    # reuse would not know it without checking again.
    value, clashes = evaluate(new)
    semantic = {k for k in common if broken(a[k], b[k], value, False)}
    located = {k for k in common if broken(a[k], b[k], value, True)}
    result = {k for k in common if a[k]["result"] != b[k]["result"]}
    moved = {k for k in common if a[k]["positions"] != b[k]["positions"]}
    # Contexts the key does not tell apart are reported as one. One more or
    # one fewer of them is a context that appeared or disappeared.
    gone = appeared | disappeared | {k for k in common if a[k]["duplicates"] != b[k]["duplicates"]}
    names = {**{k: c["name"] for k, c in a.items()}, **{k: c["name"] for k, c in b.items()}}
    # Facts that flow back from the call sites, left out of results.
    callers = {k for k in common if a[k]["callers"] != b[k]["callers"]}
    predicted_semantic = semantic | gone
    predicted_any = predicted_semantic | located
    changed_semantic = result | gone
    changed_located = changed_semantic | moved
    under_semantic = changed_semantic - predicted_semantic
    under_located = changed_located - predicted_any
    return {
        "old_contexts": len(a), "new_contexts": len(b), "common": len(common),
        "appeared": len(appeared), "disappeared": len(disappeared),
        "predicted": len(predicted_semantic), "predicted_with_locations": len(predicted_any),
        "changed": len(changed_semantic), "changed_with_positions": len(changed_located),
        "over_approximation": len(predicted_semantic - changed_semantic),
        "location_only": len(predicted_any - predicted_semantic),
        "caller_facts_changed": len(callers),
        "under_approximation": len(under_semantic | under_located),
        "under": sorted(under_semantic | under_located),
        "names": names,
        "predicted_set": predicted_semantic, "changed_set": changed_semantic, "gone_set": gone,
        "inputs": inputs_changed(old, new), "clashes": clashes + evaluate(old)[1],
    }


def inputs_changed(old, new):
    files_a = {f["path"]: f["digest"] for f in old["inputs"]["files_read"]}
    files_b = {f["path"]: f["digest"] for f in new["inputs"]["files_read"]}
    return {
        "files_changed": sorted(p for p in files_a.keys() & files_b.keys() if files_a[p] != files_b[p]),
        "files_added": sorted(files_b.keys() - files_a.keys()),
        "files_removed": sorted(files_a.keys() - files_b.keys()),
        "paths_absent_changed": sorted(set(old["inputs"]["paths_absent"])
                                       ^ set(new["inputs"]["paths_absent"])),
    }


def summary_line(r):
    return (f"contexts {r['old_contexts']} -> {r['new_contexts']} "
            f"(+{r['appeared']} -{r['disappeared']}); predicted {r['predicted']} "
            f"(+{r['location_only']} by location only); changed {r['changed']} "
            f"(+{r['changed_with_positions'] - r['changed']} by position only); "
            f"over-approximation {r['over_approximation']}; "
            f"under-approximation {r['under_approximation']}")


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("old")
    ap.add_argument("new")
    ap.add_argument("--list", type=int, default=20, metavar="N",
                    help="list at most N contexts per set (0: none)")
    ap.add_argument("--json", action="store_true", help="print the sizes as one JSON object")
    args = ap.parse_args()
    r = compare(load(args.old), load(args.new))
    if args.json:
        print(json.dumps({k: v for k, v in r.items()
                          if not isinstance(v, (set, dict)) or k == "inputs"}, sort_keys=True))
    else:
        print(summary_line(r))
        if any(r["inputs"].values()):
            print("inputs:", json.dumps(r["inputs"], sort_keys=True))
        if args.list:
            for label, keys in (("predicted but unchanged", r["predicted_set"] - r["changed_set"]),):
                shown = sorted(r["names"][k] for k in keys)[:args.list]
                for n in shown:
                    print(f"  {label}: {n}")
    for k in r["under"][:max(args.list, 20)]:
        print(f"UNDER-APPROXIMATION: {r['names'][k]} [{k}] changed with no dependency predicting it",
              file=sys.stderr)
    for line in r["clashes"][:10]:
        print(f"INCONSISTENT: {line}", file=sys.stderr)
    return 1 if r["under_approximation"] or r["clashes"] else 0


if __name__ == "__main__":
    sys.exit(main())
