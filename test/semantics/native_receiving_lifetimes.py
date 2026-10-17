#!/usr/bin/env python3
"""Check receiving ownership against the C emitter's actual runtime."""

import argparse
import os
from pathlib import Path
import subprocess


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--emitter", type=Path, required=True)
    parser.add_argument("--cc", default="clang")
    parser.add_argument("--sanitize", action="store_true")
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[2]
    work = root / ".work" / "tmp" / "native-receiving-lifetimes"
    work.mkdir(parents=True, exist_ok=True)
    environment = os.environ | {"TMPDIR": str(root / ".work" / "tmp")}
    source = work / "runtime.c"
    runtime = subprocess.run([str(args.emitter.resolve()), "runtime"], check=True,
                             stdout=subprocess.PIPE, env=environment).stdout
    source.write_bytes(runtime + Path(__file__).with_suffix(".c").read_bytes())
    for debug in (0, 1):
        for optimization in ("O0", "O2"):
            executable = work / f"receiving-{debug}-{optimization}"
            command = [args.cc, f"-{optimization}", f"-DGS_DEBUG={debug}"]
            if args.sanitize:
                command.append("-fsanitize=address,undefined")
            command.extend([str(source), "-o", str(executable), "-lm", "-pthread"])
            subprocess.run(command, check=True, env=environment)
            result = subprocess.run([str(executable)], stdout=subprocess.PIPE,
                                    stderr=subprocess.PIPE, env=environment)
            if result.returncode or result.stdout or result.stderr:
                raise RuntimeError(f"receiving failure {result.returncode}: {result.stdout!r} {result.stderr!r}")
            for rejected in range(1, 28):
                result = subprocess.run([str(executable), str(rejected)], stdout=subprocess.PIPE,
                                        stderr=subprocess.PIPE, env=environment)
                if (result.returncode != 1 or result.stdout or
                        result.stderr != b"goose runtime error: invalid construction receiver protocol\n"):
                    raise RuntimeError(f"receiving guard {rejected}: {result.returncode} "
                                       f"{result.stdout!r} {result.stderr!r}")
            print(f"receiving lifetime invariants: GS_DEBUG={debug} {optimization} pass")


if __name__ == "__main__":
    main()
