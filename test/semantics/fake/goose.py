#!/usr/bin/env python3
"""Stand-in for the Goose compiler, used only by `run_tests.py --self-test`.

Its answers come from the JSON script named by $FAKE_SCRIPT:
  export[NAME]            "ok" (default) | "nofile" | {"unsupported": ID} | {"fail": TEXT}
  gir                     "reject" makes `--pipeline` an unknown option
  gir_runs[NAME][MODE]    {"stdout": S, "stderr": S, "exit": N} of the pipeline's program
                          (written as C by --standalone, played directly by --jit)
"""

import json
import os
from pathlib import Path
import sys

script = json.loads(Path(os.environ["FAKE_SCRIPT"]).read_text())
args = sys.argv[1:]

if args[:2] == ["toolchain", "--json"]:
    print(json.dumps({"builtin": script.get("builtin", [])}))
    sys.exit(0)

if "--emit-core" in args:
    target = Path(args[args.index("--emit-core") + 1])
    source = Path(args[args.index("--check") + 1])
    name = source.stem
    entry = script.get("export", {}).get(name, "ok")
    if isinstance(entry, dict) and "unsupported" in entry:
        print(f"{source}:3: unsupported in core-pilot: {entry['unsupported']}", file=sys.stderr)
        sys.exit(1)
    if isinstance(entry, dict) and "fail" in entry:
        print(entry["fail"], file=sys.stderr)
        sys.exit(1)
    if entry != "nofile":
        target.write_text(json.dumps({"case": name}))
    print("parsed ok")
    sys.exit(0)

if "--pipeline" in args:
    if script.get("gir") == "reject":
        print("unknown option: --pipeline", file=sys.stderr)
        sys.exit(1)
    source = Path(args[-1])
    mode = "debug" if "-DGS_DEBUG=1" in args else "release"
    run = script["gir_runs"][source.stem][mode]
    if "--jit" in args:
        # An in-process run: the program's streams and status are the compiler's.
        sys.stdout.write(run.get("stdout", ""))
        sys.stderr.write(run.get("stderr", ""))
        sys.exit(run.get("exit", 0))
    target = Path(args[args.index("-o") + 1])
    target.write_text(
        "#include <stdio.h>\n"
        f"int main(void) {{ fputs({json.dumps(run.get('stdout', ''))}, stdout);"
        f" fputs({json.dumps(run.get('stderr', ''))}, stderr); return {run.get('exit', 0)}; }}\n")
    sys.exit(0)

print("fake goose: unsupported arguments", file=sys.stderr)
sys.exit(99)
