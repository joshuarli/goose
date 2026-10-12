#!/usr/bin/env python3
"""DeclKey and ContextKey stability across edits that must not move them.

  python test/scale/key_stability.py --goose GOOSE [--work DIR]

Generates a synthetic program with gen.py and four variants of it: an
unrelated function added, the declarations reordered, comments inserted
(which shifts every line number), and the body of one helper edited. For each
variant the program is checked with `--build-report` and the reports are
compared with the original's:

  * every function of the original keeps its DeclKey, including the helper
    whose body was edited;
  * every function keeps the digest of its set of context keys, so none of
    the variants moves a context;
  * the added function's DeclKey is new.

With `--stable-names` the same variants, and one in which a new helper with
two new specializations is added, are also emitted as C, and every function,
literal and file name of the original program must appear unchanged in each.

Prints one line per violation and exits 1 if there is any.
"""

import argparse
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
EDITED = "first_i64_0"
sys.path.insert(0, str(HERE))
import cfuncs  # noqa: E402

# A helper called under a global and a local root: two specializations the
# original program does not have.
EXTRA = '''var g_extra: i64[>..] = [5];
fn extra_helper(values: i64[:]) -> i64 { return values[0] + 9; }
fn extra_requests() -> i64 {
    var l_extra: i64[>..] = [6];
    return extra_helper(g_extra) + extra_helper(l_extra);
}
'''


def variants(source):
    lines = source.splitlines()
    helpers = [l for l in lines if l.startswith("fn first_")]
    rest = [l for l in lines if not l.startswith("fn first_")]
    assert helpers and any(l.startswith(f"fn {EDITED}(") for l in helpers)
    unrelated = "fn unrelated_added(x: i64) -> i64 { return x * 3 + 1; }"
    return {
        "unrelated function added": "\n".join([unrelated] + lines) + "\n",
        "declarations reordered": "\n".join(rest + helpers[::-1]) + "\n",
        "comments inserted": "\n".join(
            ["// a leading comment", "// and a second one"] +
            [l for i, ll in enumerate(lines) for l in ([ll, "// between"] if i % 3 == 0 else [ll])]
        ) + "\n",
        "specializations added": source.replace("fn main() {", EXTRA + "fn main() {\n    var extra: i64 = extra_requests();", 1),
        "helper body edited": source.replace(
            f"fn {EDITED}(values: i64[:]) -> i64 {{ return values[0] + 1; }}",
            f"fn {EDITED}(values: i64[:]) -> i64 {{ return values[0] + 100; }}"),
    }


def report_of(goose, path, out):
    r = subprocess.run([goose, "--check", "--build-report", str(out), str(path)],
                       capture_output=True, text=True)
    if r.returncode != 0:
        print(f"key_stability: {goose} rejected {path}:\n{r.stdout}{r.stderr}")
        sys.exit(1)
    functions = json.loads(Path(out).read_text())["functions"]
    return {f["name"]: f for f in functions}


def emitted_names(goose, path, out):
    """The names a program is emitted with under --stable-names: its
    functions, its literals and its file references."""
    r = subprocess.run([goose, "-O0", "--stable-names", "-o", str(out), str(path)],
                       capture_output=True, text=True)
    if r.returncode != 0:
        print(f"key_stability: --stable-names rejected {path}:\n{r.stdout}{r.stderr}")
        sys.exit(1)
    text = Path(out).read_text()
    return set(cfuncs.functions(text)) | set(re.findall(r"\bgs_(?:str|strv|blob|file)_[0-9a-f]{16}\b", text))


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--goose", required=True)
    ap.add_argument("--work", help="scratch directory (default: under .work/tmp)")
    a = ap.parse_args()
    scratch = ROOT / ".work" / "tmp"
    scratch.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(dir=a.work or scratch) as tmp:
        tmp = Path(tmp)
        subprocess.run([sys.executable, str(HERE / "gen.py"), "--helpers", "4",
                        "--contexts", "8", "--types", "2", "--out", str(tmp / "base")],
                       check=True, capture_output=True)
        source = (tmp / "base" / "main.goose").read_text()
        base = report_of(a.goose, tmp / "base" / "main.goose", tmp / "base.json")
        base_names = emitted_names(a.goose, tmp / "base" / "main.goose", tmp / "base.c")
        bad = []
        for label, text in variants(source).items():
            d = tmp / label.replace(" ", "_")
            d.mkdir()
            assert text != source, label
            (d / "main.goose").write_text(text)
            got = report_of(a.goose, d / "main.goose", d / "report.json")
            for name, f in base.items():
                g = got.get(name)
                if g is None:
                    bad.append(f"{label}: {name} is gone")
                    continue
                if g["decl_key"] != f["decl_key"]:
                    bad.append(f"{label}: DeclKey of {name} moved")
                if g["contexts_key"] != f["contexts_key"]:
                    bad.append(f"{label}: contexts of {name} moved")
            names = emitted_names(a.goose, d / "main.goose", d / "out.c")
            for name in sorted(base_names - names):
                bad.append(f"{label}: emitted name {name} is gone under --stable-names")
            added = set(got) - set(base)
            if label == "specializations added":
                added -= {n for n in added if n.startswith(("extra_helper", "extra_requests"))}
            if label == "unrelated function added":
                keys = {f["decl_key"] for f in base.values()}
                if len(added) != 1 or any(got[n]["decl_key"] in keys for n in added):
                    bad.append(f"{label}: the new function does not have a new DeclKey")
            elif added:
                bad.append(f"{label}: unexpected new functions {sorted(added)}")
    for line in bad:
        print(f"key_stability: {line}")
    if not bad:
        print(f"key_stability: ok ({len(base)} functions, {len(variants(source))} variants)")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
