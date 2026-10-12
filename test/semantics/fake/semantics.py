#!/usr/bin/env python3
"""Stand-in for the reference tool, used only by `run_tests.py --self-test`.

`run FILE --numeric MODE` answers with run[NAME][MODE] from the JSON script
named by $FAKE_SCRIPT, where NAME is the case recorded in FILE:
  {"answer": JSON, "exit": N}   print the answer as one line and exit N
  {"raw": TEXT, "exit": N}      print TEXT verbatim and exit N
  {"sleep": SECONDS}            hang, then print nothing
"""

import json
import os
from pathlib import Path
import sys
import time

script = json.loads(Path(os.environ["FAKE_SCRIPT"]).read_text())
args = sys.argv[1:]
if args[:1] != ["run"] or "--numeric" not in args:
    print("fake semantics: unsupported arguments", file=sys.stderr)
    sys.exit(99)
name = json.loads(Path(args[1]).read_text())["case"]
mode = args[args.index("--numeric") + 1]
entry = script["run"].get(name, {}).get(mode)
if entry is None:
    print(f"fake semantics: no script for {name} {mode}", file=sys.stderr)
    sys.exit(99)
if "sleep" in entry:
    time.sleep(entry["sleep"])
    sys.exit(0)
if "raw" in entry:
    sys.stdout.write(entry["raw"])
else:
    print(json.dumps(entry["answer"]))
sys.exit(entry.get("exit", 0))
