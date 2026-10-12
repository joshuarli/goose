#!/usr/bin/env python3
"""Internal consistency of a goose-build-report/1 file.

  python test/scale/report_check.py REPORT [--c-file FILE]

Checks the rules a report must satisfy before anything is read from it:

  * the per-function emitted bytes, the helper, type, literal, data, runtime
    and glue bytes, and the stated unattributed remainder sum to the size of
    the C file (and to FILE's size on disk when --c-file is given);
  * the unattributed remainder is small: it is only the file's header
    comment, build defines and section banners;
  * checked contexts >= entry-reachable contexts >= live instances, and the
    per-function counts add up to the program's;
  * the itemized phase times and the stated unattributed remainder sum to
    the total, and no time is negative.

Prints one line per violation and exits 1 if there is any.
"""

import argparse
import json
import sys
from pathlib import Path

FORMAT = "goose-build-report/1"
# Header comment, build defines and the section banners; far less than this
# unless some real content has gone unattributed.
MAX_UNATTRIBUTED_BYTES = 16 * 1024
# Times are written with six decimals.
TIME_SLACK = 1e-4


def check(report, c_file):
    bad = []

    def need(cond, message):
        if not cond:
            bad.append(message)

    need(report.get("format") == FORMAT, f"format is {report.get('format')!r}, not {FORMAT!r}")
    counts = report.get("counts", {})
    functions = report.get("functions", [])
    mode = report.get("input", {}).get("mode")

    contexts = counts.get("checked_contexts")
    reachable = counts.get("entry_reachable_contexts")
    live = counts.get("live_instances")
    need(isinstance(contexts, int) and isinstance(reachable, int), "contexts missing")
    if isinstance(contexts, int) and isinstance(reachable, int):
        need(contexts >= reachable, f"checked contexts {contexts} < entry-reachable {reachable}")
    if live is not None:
        need(reachable >= live, f"entry-reachable contexts {reachable} < live instances {live}")
    need(counts.get("source_functions") == len(functions),
         f"source_functions {counts.get('source_functions')} != {len(functions)} listed")
    need(sum(f["contexts"] for f in functions) == contexts,
         "per-function contexts do not sum to checked_contexts")
    dup = counts.get("duplicate_contexts", {})
    need(sum(f["duplicate_contexts"] for f in functions) == dup.get("count"),
         "per-function duplicate contexts do not sum to the program's")
    need(dup.get("count") == sum(v for k, v in dup.items() if k != "count"),
         "duplicate contexts are not all classified")
    keys = [f["decl_key"] for f in functions]
    need(len(set(keys)) == len(keys), "two functions share a decl_key")
    if live is not None:
        need(sum(f["live_instances"] for f in functions) == live,
             "per-function live instances do not sum to live_instances")
        for f in functions:
            need(f["live_instances"] <= f["contexts"], f"{f['name']}: live instances > contexts")

    for f in functions:
        n = f["contexts"] - f["duplicate_contexts"]
        need(0 <= f["duplicate_contexts"] < max(f["contexts"], 1) or f["contexts"] == 0,
             f"{f['name']}: duplicate contexts out of range")
        for d in f["dimensions"]:
            need(1 <= d["distinct_values"] <= n,
                 f"{f['name']}: {d['dimension']} distinct values out of range")
            need(0 <= d["contexts_merged_if_ignored"] <= n - 1,
                 f"{f['name']}: {d['dimension']} merged contexts out of range")
        need(f["self_check_seconds"] >= 0, f"{f['name']}: negative check time")
    for d in report.get("dimensions", []):
        need(d["distinct_values"] >= 0 and d["contexts_merged_if_ignored"] >= 0,
             f"dimension {d['dimension']} negative")

    # Bytes.
    out = report.get("output")
    if mode == "check":
        need(out is None and live is None and
             all("emitted_bytes" not in f for f in functions),
             "a --check report carries backend facts")
    if out is not None:
        a = out["attributed"]
        total = sum(a.values()) + out["unattributed_bytes"]
        need(total == out["c_bytes"],
             f"attributed {sum(a.values())} + unattributed {out['unattributed_bytes']} "
             f"!= c_bytes {out['c_bytes']}")
        need(0 <= out["unattributed_bytes"] <= MAX_UNATTRIBUTED_BYTES,
             f"unattributed_bytes {out['unattributed_bytes']} out of range")
        need(all(v >= 0 for v in a.values()), "a negative byte count")
        need(sum(f["emitted_bytes"] for f in functions) == a["function_bodies"],
             "per-function emitted bytes do not sum to function_bodies")
        helpers = counts["generated_helpers"]
        need(sum(h["bytes"] for h in helpers.values()) == a["generated_helpers"],
             "helper bytes do not sum to generated_helpers")
        need(counts["type_declarations"]["bytes"] == a["type_declarations"], "type bytes differ")
        need(counts["literal_data"]["bytes"] == a["literal_data"], "literal bytes differ")
        need(counts["runtime_text"]["bytes"] == a["runtime_text"], "runtime bytes differ")
        emitted = counts["emitted_instances"]
        need(emitted["bodies"] == live, "emitted bodies != live instances")
        need(emitted["total"] == emitted["bodies"] + emitted["element_run_twins"] +
             emitted["thread_entries"], "emitted instance total does not add up")
        need(sum(f["emitted_instances"] for f in functions) ==
             emitted["bodies"] + emitted["element_run_twins"],
             "per-function emitted instances do not sum to bodies plus twins")
        if c_file is not None:
            size = Path(c_file).stat().st_size
            need(size == out["c_bytes"], f"{c_file} is {size} bytes, report says {out['c_bytes']}")
    elif c_file is not None:
        need(False, "--c-file given but the report wrote no output")

    # Time.
    phases = report.get("phases", {})
    total = report.get("total", {})
    rest = report.get("unattributed_seconds", {})
    for kind in ("wall", "cpu"):
        parts = sum(p[f"{kind}_seconds"] for p in phases.values())
        need(all(p[f"{kind}_seconds"] >= 0 for p in phases.values()), f"negative {kind} time")
        need(rest.get(kind, -1) >= -TIME_SLACK, f"negative unattributed {kind} time")
        need(abs(parts + rest.get(kind, 0) - total[f"{kind}_seconds"]) <= TIME_SLACK,
             f"phase {kind} times {parts:.6f} + unattributed {rest.get(kind)} "
             f"!= total {total[f'{kind}_seconds']:.6f}")
    for name in ("parse_and_resolve", "check_and_specialize"):
        need(name in phases, f"phase {name} missing")
    if mode == "emit":
        for name in ("optimize", "bounds_check_elimination", "code_generation"):
            need(name in phases, f"phase {name} missing")
    ext = report.get("extensions")
    need(isinstance(ext, dict) and {"sharing", "units", "native_compile"} <= ext.keys(),
         "extensions section missing")
    return bad


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("report")
    ap.add_argument("--c-file", help="the C file the report describes")
    a = ap.parse_args()
    try:
        report = json.loads(Path(a.report).read_text())
    except (OSError, ValueError) as e:
        print(f"report_check: cannot read {a.report}: {e}")
        return 1
    bad = check(report, a.c_file)
    for line in bad:
        print(f"report_check: {line}")
    if not bad:
        print(f"report_check: ok ({len(report['functions'])} functions)")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
