#!/usr/bin/env python3
"""Byte-for-byte parity of the C two compilers emit.

For every positive fixture under test/ that the main runner generates C for,
and every program in samples/, emits C at -O0 and -O2 with a candidate and a
baseline compiler and compares the files. A program both reject with the same
exit code and diagnostics counts as equal; one accepted by only one compiler,
or rejected differently, is a difference.

  python test/scale/parity.py --goose CANDIDATE --baseline BASE
         [--candidate-arg ARG ...] [--only GLOB] [-j N] [--work DIR]

Prints one line per difference, then a JSON summary line. Exits 1 on any
difference.
"""

import argparse
import concurrent.futures
import fnmatch
import json
import os
import re
import shutil
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
sys.path.insert(0, str(ROOT / "test"))
sys.path.insert(0, str(ROOT / "scripts"))
import run_tests  # noqa: E402  (the runner's discovery and per-fixture flags)
import toolchain as tc  # noqa: E402

LEVELS = (0, 2)


def fixtures():
    """(label, source, extra flags, skip reason or None) for each program,
    discovered as run_tests.main does."""
    tests = [f for f in sorted((ROOT / "test").glob("*/*.goose"))
             if f.parent.name not in ("errors", "errors_tc", "goose_in_goose", "lint")
             and f.name != "lexer_tokens.goose"]
    found = []
    for f in tests:
        label = f"test/{f.parent.name}/{f.name}"
        if f.parent.name in tc.NATIVE_MODULES and run_tests.error_markers(f):
            found.append((label, f, [], "native-module rejection fixture"))
        elif "parse-only" in run_tests.first_line(f):
            found.append((label, f, [], "parse-only fixture (no C)"))
        else:
            found.append((label, f, [], None))
    for f in sorted((ROOT / "samples").glob("*.goose")):
        header = f.parent / (sample_name(f) + ".h")
        found.append((f"samples/{f.name}", f, ["--include", str(header)] if header.exists() else [], None))
    return found


def sample_name(f):
    """A sample's bare name, without its ordering prefix (as run_samples)."""
    return re.sub(r"^\d+_", "", f.stem)


def emit(exe, extra, flags, source, level, cfile):
    """(exit code, diagnostics, C bytes or None) of one compile."""
    cfile.parent.mkdir(parents=True, exist_ok=True)
    cfile.unlink(missing_ok=True)
    # Both compilers read one stdlib directory: a compiler otherwise embeds the
    # path of the stdlib beside its own binary in runtime diagnostics, which
    # would differ between two build directories of identical source.
    argv = [exe, "--stdlib", ROOT / "stdlib", *extra,
            *["-D" + d for d in run_tests.runtime_defines(source)], *flags,
            f"-O{level}", "-o", cfile, source]
    code, out, err = tc.run_capture(argv)
    return code, out + err, cfile.read_bytes() if code == 0 and cfile.is_file() else None


def compare(job, args, work):
    label, source, flags, level = job
    slug = label.replace("/", "__")
    base = emit(args.baseline, [], flags, source, level, work / "base" / f"O{level}" / f"{slug}.c")
    cand = emit(args.goose, args.candidate_arg, flags, source, level,
                work / "cand" / f"O{level}" / f"{slug}.c")
    if base[0] != cand[0]:
        return label, level, f"exit code {base[0]} (baseline) vs {cand[0]} (candidate)"
    if base[0] != 0:
        # Both rejected: the same rejection.
        return label, level, None if base[1] == cand[1] else "different diagnostics"
    if base[2] != cand[2]:
        return label, level, f"C differs ({len(base[2])} vs {len(cand[2])} bytes)"
    return label, level, None


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--goose", required=True, help="the candidate compiler")
    ap.add_argument("--baseline", required=True, help="the baseline compiler")
    ap.add_argument("--candidate-arg", action="append", default=[],
                    help="an extra argument for the candidate only (repeatable)")
    ap.add_argument("--only", help="compare only programs whose label (test/<dir>/<file> "
                                   "or samples/<file>) matches this glob")
    ap.add_argument("-j", "--jobs", type=int, default=os.cpu_count() or 1)
    ap.add_argument("--work", default=str(ROOT / ".work" / "parity"))
    # argparse refuses a value that looks like an option; the argument is
    # meant to be one, so glue it to its flag.
    argv, i = [], 1
    while i < len(sys.argv):
        if sys.argv[i] == "--candidate-arg" and i + 1 < len(sys.argv):
            argv.append("--candidate-arg=" + sys.argv[i + 1])
            i += 1
        else:
            argv.append(sys.argv[i])
        i += 1
    args = ap.parse_args(argv)
    args.goose, args.baseline = str(Path(args.goose).resolve()), str(Path(args.baseline).resolve())
    work = Path(args.work).resolve()
    shutil.rmtree(work, ignore_errors=True)
    # The compilers' cache lives with the run, never the user's own.
    os.environ["GOOSE_HOME"] = str(work / "home")

    skipped, jobs = {}, []
    for label, source, flags, skip in fixtures():
        if args.only and not fnmatch.fnmatch(label, args.only):
            continue
        if skip:
            skipped[skip] = skipped.get(skip, 0) + 1
            continue
        jobs += [(label, source, flags, level) for level in LEVELS]

    different = 0
    with concurrent.futures.ThreadPoolExecutor(max(1, args.jobs)) as pool:
        results = list(pool.map(lambda j: compare(j, args, work), jobs))
    for label, level, why in results:
        if why:
            different += 1
            print(f"DIFF {label} -O{level}: {why}")
    summary = {"compared": len(results), "equal": len(results) - different,
               "different": different, "skipped": skipped}
    print(json.dumps(summary))
    return 1 if different else 0


if __name__ == "__main__":
    sys.exit(main())
