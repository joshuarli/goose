#!/usr/bin/env python3
"""Internal consistency of a goose-build-report/1 file.

  python test/scale/report_check.py REPORT [--c-file FILE]
      [--require-o2-sharing-threshold]

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
The optional O2 gate requires the report to show that inlined-call and
bounds-check blockers account for at least 10% of emitted C bytes.
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
SHARING_BLOCKER_CAUSES = {"bounds_check_sites", "inlined_calls", "callee", "other"}
O2_SHARING_CAUSES = ("inlined_calls", "bounds_check_sites")


def check_sharing_blockers(sharing, need):
    # Reports written before byte attribution have no byte section. Continue
    # checking their existing sharing fields without treating them as invalid.
    if "not_merged_same_declaration_bytes" not in sharing:
        return
    counts = sharing.get("not_merged_same_declaration")
    byte_counts = sharing["not_merged_same_declaration_bytes"]
    if not isinstance(counts, dict):
        need(False, "sharing blocker bytes are present without blocker counts")
        return
    if not isinstance(byte_counts, dict):
        need(False, "sharing not_merged_same_declaration_bytes is not an object")
        return
    if set(counts) != set(byte_counts):
        need(False, "sharing blocker count and byte causes differ")
    if set(counts) != SHARING_BLOCKER_CAUSES:
        need(False, "sharing blocker causes differ from the reported cause set")

    valid_counts = all(type(value) is int and value >= 0 for value in counts.values())
    valid_bytes = all(type(value) is int and value >= 0 for value in byte_counts.values())
    need(valid_counts, "sharing blocker counts must be non-negative integers")
    need(valid_bytes, "sharing blocker bytes must be non-negative integers")
    if valid_counts:
        need(sum(counts.values()) <= sharing["functions_after"],
             "sharing blocker counts exceed functions_after")
    if valid_bytes:
        need(sum(byte_counts.values()) <= sharing["function_bytes_after"],
             "sharing blocker bytes exceed function_bytes_after")


def check_o2_sharing_threshold(report, need):
    input_info = report.get("input")
    level = input_info.get("optimization_level") if isinstance(input_info, dict) else None
    need(type(level) is int and level == 2,
         f"O2 sharing threshold requires input.optimization_level == 2 (got {level!r})")

    extensions = report.get("extensions")
    sharing = extensions.get("sharing") if isinstance(extensions, dict) else None
    if not isinstance(sharing, dict):
        need(False, "O2 sharing threshold requires extensions.sharing")
        return
    counts = sharing.get("not_merged_same_declaration")
    byte_counts = sharing.get("not_merged_same_declaration_bytes")
    if not isinstance(byte_counts, dict):
        need(False,
             "O2 sharing threshold requires extensions.sharing.not_merged_same_declaration_bytes")
        return
    if not isinstance(counts, dict):
        need(False, "O2 sharing threshold requires extensions.sharing.not_merged_same_declaration")
        return
    if set(counts) != SHARING_BLOCKER_CAUSES or set(byte_counts) != SHARING_BLOCKER_CAUSES:
        need(False, "O2 sharing threshold requires the complete sharing blocker cause set")
        return
    if set(counts) != set(byte_counts):
        need(False, "O2 sharing threshold found inconsistent blocker causes")
        return
    if not all(type(value) is int and value >= 0 for value in counts.values()):
        need(False, "O2 sharing threshold requires non-negative integer blocker counts")
        return
    if not all(type(value) is int and value >= 0 for value in byte_counts.values()):
        need(False, "O2 sharing threshold requires non-negative integer blocker bytes")
        return

    function_bytes = sharing.get("function_bytes_after")
    if type(function_bytes) is not int or function_bytes < 0:
        need(False, "O2 sharing threshold requires non-negative integer function_bytes_after")
        return
    if sum(byte_counts.values()) > function_bytes:
        need(False, "O2 sharing threshold found blocker bytes exceeding function_bytes_after")
        return

    output = report.get("output")
    c_bytes = output.get("c_bytes") if isinstance(output, dict) else None
    if type(c_bytes) is not int or c_bytes <= 0:
        need(False, "O2 sharing threshold requires positive integer output.c_bytes")
        return
    attributed = output.get("attributed")
    function_bodies = attributed.get("function_bodies") if isinstance(attributed, dict) else None
    if type(function_bodies) is not int or function_bodies != function_bytes:
        need(False,
             "O2 sharing threshold requires function_bytes_after to equal output function_bodies")
        return

    blocked_bytes = sum(byte_counts[cause] for cause in O2_SHARING_CAUSES)
    if blocked_bytes * 10 < c_bytes:
        need(False,
             f"O2 context-dependent blocker bytes {blocked_bytes} / emitted C bytes {c_bytes} "
             "are below the 10% threshold")


def check(report, c_file, require_o2_sharing_threshold=False):
    bad = []

    def need(cond, message):
        if not cond:
            bad.append(message)

    if require_o2_sharing_threshold:
        check_o2_sharing_threshold(report, need)

    # A build that ran nothing: the report says so and carries nothing else.
    if report.get("input", {}).get("mode") == "no-op":
        need(report.get("format") == FORMAT, "format differs")
        nc = report.get("extensions", {}).get("native_compile") or {}
        need(nc.get("no_op") is True, "a no-op report does not say no_op")
        need(not nc.get("frontend_phases") and not nc.get("native_compiler_invocations")
             and not nc.get("link", {}).get("ran"), "a no-op report says something ran")
        return bad

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
    sharing = report.get("extensions", {}).get("sharing")
    if sharing is not None:
        need(sharing["functions_after"] <= sharing["functions_before"], "sharing grew the functions")
        need(sharing["function_bytes_after"] <= sharing["function_bytes_before"],
             "sharing grew the function bytes")
        need(sum(f["implementations"] for f in functions) == sharing["functions_after"],
             "per-function implementations do not sum to the functions after sharing")
        if out is not None:
            need(sharing["function_bytes_after"] == out["attributed"]["function_bodies"],
                 "bytes after sharing differ from function_bodies")
        need(sharing["functions_before"] == (emitted["bodies"] + emitted["element_run_twins"]
                                             if out is not None else sharing["functions_before"]),
             "functions before sharing differ from the emitted bodies and twins")
        check_sharing_blockers(sharing, need)
    units = report.get("extensions", {}).get("units")
    if units is not None:
        listed = units["units"]
        need(units["count"] == len(listed), "units count differs from the units listed")
        sizes = sorted(u["bytes"] for u in listed)
        need(units["bytes"] == {"min": sizes[0], "median": sizes[len(sizes) // 2], "max": sizes[-1]},
             "unit byte statistics differ from the units listed")
        files = {u["file"] for u in listed}
        need(len(files) == len(listed), "two units share a file name")
        for f in functions:
            for u in f.get("units", []):
                need(u in files, f"{f['name']} is placed in {u}, which is not a unit")
    ext = report.get("extensions")
    need(isinstance(ext, dict) and {"sharing", "units", "native_compile"} <= ext.keys(),
         "extensions section missing")
    return bad


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("report")
    ap.add_argument("--c-file", help="the C file the report describes")
    ap.add_argument("--require-o2-sharing-threshold", action="store_true",
                    help="require O2 sharing blockers to account for at least 10%% of emitted C")
    a = ap.parse_args()
    try:
        report = json.loads(Path(a.report).read_text())
    except (OSError, ValueError) as e:
        print(f"report_check: cannot read {a.report}: {e}")
        return 1
    bad = check(report, a.c_file, a.require_o2_sharing_threshold)
    for line in bad:
        print(f"report_check: {line}")
    if not bad:
        print(f"report_check: ok ({len(report.get('functions', []))} functions)")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
