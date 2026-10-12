#!/usr/bin/env python3
"""Byte-for-byte parity of the linter between two compilers.

Runs `goose lint`, the private facts stream and ordinary `--check` warnings
through a candidate and a baseline compiler and reports every difference, one
line each, then one JSON summary line. Exit status is 1 on any difference.

What is compared
  diagnostics  stdout, stderr and exit status of `goose lint` for every lint
               fixture, the linter's own source and every fixture that declares
               `// warning:` markers, under each option set below, plus the
               suite's baseline, configuration, suppression and failure cases.
  facts        the file the compiler hands `goose-lint --facts`, captured by a
               stand-in companion that copies it aside and runs the real one.
  warnings     the full `--check` output of every fixture with warning markers.
  fanout       a synthetic program with many contexts per helper: identical
               lint output, and the candidate's cost report showing fewer
               emitted implementations than the checked contexts the linter
               counts.
  backend      `--check --build-report` reports only frontend phases.

Only the absolute directory of each compiler is normalized, in stdout, stderr
and the facts: the two builds live in different directories and `goose lint`
never prints that directory unless an error does. The counts of replacements
are in the summary.
"""

import argparse
from concurrent.futures import ThreadPoolExecutor
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parents[2]
STDLIB = ROOT / "stdlib"
GROUPS = ["existing", "correctness", "suspicious", "review", "performance", "project"]
RULES = [
    "redundant_cast", "redundant_reference_marker", "avoidable_reference_copy", "discarded_failure",
    "unchecked_poll_result", "unused_pure_value", "stale_suppression", "post_overflow_guard",
    "stale_slice_length", "specialization_fanout", "view_before_append_argument",
    "foreign_container_index",
]
FRONTEND_PHASES = {"parse_and_resolve", "check_and_specialize", "report_collection"}

# A function that is not generic, so its cast is judged and its `&` warns.
CAST_AND_MARKER = """\
fn g(v: i64&) -> i64 { v }
fn both() -> i64 {
    var a = 2;
    let n: i32 = 7;
    let m: i32 = n as i32;
    print(m);
    g(&a)
}
fn main() {
    print(both());
}
"""

CRLF_SOURCE = ('fn main() {\r\n\tlet parsed = parse_int("42");\r\n'
               '\tprint(parsed);\r\n\tlet text = """goose-lint: allow[not_a_rule] -- raw text""";\r\n}\r\n')


class Compiler:
    """One compiler under test, with its own normalization and install layouts."""

    def __init__(self, name, goose):
        self.name = name
        self.goose = Path(goose).resolve()
        self.companion = self.goose.with_name("goose-lint")
        self.directory = str(self.goose.parent)
        self.normalized = 0

    def normalize(self, data):
        count = data.count(self.directory.encode())
        self.normalized += count
        return data.replace(self.directory.encode(), b"<COMPILER_DIR>")


def run(command, cwd=ROOT, env=None):
    return subprocess.run([str(c) for c in command], cwd=cwd, env=env, capture_output=True)


def lint(compiler, source, *options, goose=None, env=None, cwd=ROOT, stdlib=True):
    command = [goose or compiler.goose, "lint", source]
    if stdlib:
        command += ["--stdlib", STDLIB]
    result = run(command + list(options), cwd=cwd, env=env)
    return (result.returncode, compiler.normalize(result.stdout), compiler.normalize(result.stderr))


def check_run(compiler, source, *options):
    result = run([compiler.goose, *options, "--stdlib", STDLIB, source])
    return (result.returncode, compiler.normalize(result.stdout), compiler.normalize(result.stderr))


def describe(a, b):
    if a[0] != b[0]:
        return f"exit status {a[0]} != {b[0]}"
    for index, stream in ((1, "stdout"), (2, "stderr")):
        if a[index] != b[index]:
            left, right = a[index].splitlines(), b[index].splitlines()
            for number, (x, y) in enumerate(zip(left, right), 1):
                if x != y:
                    return f"{stream} line {number}: {x[:160]!r} != {y[:160]!r}"
            return f"{stream} length {len(left)} lines != {len(right)} lines"
    return None


def marker_fixtures():
    found = []
    for path in sorted((ROOT / "test").rglob("*.goose")):
        if re.search(r"^// warning: ", path.read_text(encoding="utf-8"), re.M):
            found.append(path)
    return found


class Parity:
    def __init__(self, candidate, baseline, scratch, jobs):
        self.candidate, self.baseline = candidate, baseline
        self.scratch = scratch
        self.jobs = jobs
        self.differences = []
        self.counts = {}

    def difference(self, section, label, text):
        self.differences.append(f"DIFF {section} {label}: {text}")

    def tally(self, section):
        self.counts[section] = self.counts.get(section, 0) + 1

    def compare_pairs(self, section, jobs):
        """`jobs` is (label, function(compiler) -> result); both compilers run
        each, in parallel across jobs."""
        def both(job):
            label, function = job
            return label, function(self.candidate), function(self.baseline)
        with ThreadPoolExecutor(self.jobs) as pool:
            for label, a, b in pool.map(both, jobs):
                self.tally(section)
                if a == b:
                    continue
                reason = describe(a, b) if isinstance(a, tuple) else "results differ"
                self.difference(section, label, reason or "results differ")

    # --- diagnostics ---------------------------------------------------------

    def config_files(self):
        contracts = self.scratch / "lint-contracts.json"
        contracts.write_text(json.dumps({"schema_version": 1, "apis": [
            {"callee": "contracts::append_and_return", "role": "append_to", "owner_arg": 0},
            {"callee": "contracts::after_append", "role": "view_after_append", "view_arg": 0, "append_arg": 1},
            {"callee": "contracts::find_for", "role": "index_of", "owner_arg": 0},
            {"callee": "contracts::use_index", "role": "consumes_index", "owner_arg": 0, "index_arg": 1},
        ]}))
        every_group = self.scratch / "all-groups.json"
        every_group.write_text(json.dumps({"schema_version": 1, "default_groups": GROUPS,
                                           "contracts": str(contracts)}))
        without_project = self.scratch / "all-but-project.json"
        without_project.write_text(json.dumps({"schema_version": 1, "default_groups": GROUPS[:-1]}))
        return every_group, without_project

    def diagnostics(self):
        every_group, without_project = self.config_files()
        core = [ROOT / "test/lint" / name for name in
                ("rules.goose", "review.goose", "contracts.goose", "suppressions.goose",
                 "fanout_root_depth.goose")]
        core += [ROOT / "test/typing/redundant_casts.goose", ROOT / "test/typing/warnings_once.goose",
                 ROOT / "tools/lint/main.goose"]
        crlf = self.scratch / "crlf.goose"
        crlf.write_bytes(CRLF_SOURCE.encode())
        cast = self.scratch / "cast_and_marker.goose"
        cast.write_text(CAST_AND_MARKER)
        core += [crlf, cast]
        markers = marker_fixtures()
        self.marker_count = len(markers)

        option_sets = [[], ["--format", "jsonl"], ["--require-complete"],
                       ["--format", "jsonl", "--require-complete"],
                       ["--format", "jsonl", "-O0"], ["--format", "jsonl", "-O2"],
                       ["--config", every_group], ["--format", "jsonl", "--config", every_group],
                       ["--format", "jsonl", "--config", every_group, "--require-complete"],
                       ["--format", "jsonl", "--config", without_project],
                       ["--format", "jsonl", *[x for r in RULES for x in ("--deny", r)]]]
        option_sets += [["--format", "jsonl", "--group", g] for g in GROUPS]
        option_sets += [["--group", g] for g in GROUPS]
        jobs = []
        for source in core:
            for options in option_sets:
                label = f"{source.relative_to(ROOT) if source.is_relative_to(ROOT) else source.name} {' '.join(map(str, options)) or '(default)'}"
                jobs.append((label, lambda c, s=source, o=options: lint(c, s, *o)))
        for source in markers:
            if source in core:
                continue
            for options in ([], ["--format", "jsonl"], ["--format", "jsonl", "--require-complete"]):
                label = f"{source.relative_to(ROOT)} {' '.join(options) or '(default)'}"
                jobs.append((label, lambda c, s=source, o=options: lint(c, s, *o)))
        self.option_set_count = len(option_sets)
        self.core_count = len(core)
        self.compare_pairs("diagnostics", jobs)
        self.suite_cases()

    def suite_cases(self):
        """The failure, configuration, baseline and install cases of the suite,
        in scratch files at one path for both compilers."""
        fixture = ROOT / "test/lint/rules.goose"
        scratch = self.scratch / "cases"
        scratch.mkdir()
        files = {}

        def write(name, text):
            path = scratch / name
            path.write_text(text)
            files[name] = path
            return path

        bad_source = write("bad.goose", "fn main( {\n")
        missing_import = write("missing-import.goose",
                               'import dep from "https://example.invalid/org/dep.git@main";\nfn main() {}\n')
        malformed = write("malformed-baseline.json", "{not json")
        severity = write("severity.json", json.dumps({
            "schema_version": 1, "default_groups": ["correctness"],
            "severity": {"discarded_failure": "error", "unchecked_poll_result": "note"}}))
        bad_severity = write("bad-severity.json",
                             json.dumps({"schema_version": 1, "severity": {"discarded_failure": "fatal"}}))
        unknown_key = write("unknown-key.json", '{"schema_version":1,"surprise":true}')
        jsonl = ["--format", "jsonl"]
        cases = [
            ("syntax error", bad_source, jsonl), ("syntax error text", bad_source, []),
            ("missing import", missing_import, jsonl), ("missing import text", missing_import, []),
            ("malformed baseline", fixture, [*jsonl, "--baseline", malformed]),
            ("severity overrides", fixture, [*jsonl, "--config", severity]),
            ("severity overrides allow", fixture, [*jsonl, "--config", severity, "--allow", "discarded_failure"]),
            ("invalid severity", fixture, [*jsonl, "--config", bad_severity]),
            ("unknown config key", fixture, [*jsonl, "--config", unknown_key]),
            ("write baseline without path", fixture, [*jsonl, "--write-baseline"]),
            ("allow", fixture, [*jsonl, "--allow", "discarded_failure"]),
            ("unknown option", fixture, ["--no-such-option"]),
            ("unknown rule", fixture, [*jsonl, "--deny", "no_such_rule"]),
            ("unknown group", fixture, [*jsonl, "--group", "no_such_group"]),
            ("help", None, ["--help"]),
        ]
        for label, source, options in cases:
            self.tally("diagnostics")
            results = []
            for compiler in (self.candidate, self.baseline):
                if source is None:
                    result = run([compiler.goose, "lint", *options])
                    results.append((result.returncode, compiler.normalize(result.stdout),
                                    compiler.normalize(result.stderr)))
                else:
                    results.append(lint(compiler, source, *options))
            reason = describe(*results)
            if reason:
                self.difference("diagnostics", label, reason)

        # Baselines are stateful: each compiler writes, matches, drifts and
        # stales its own baseline at the same path, one after the other.
        sequences = []
        for compiler in (self.candidate, self.baseline):
            source = scratch / "baseline-source.goose"
            baseline = scratch / "baseline.json"
            shutil.copyfile(fixture, source)
            baseline.unlink(missing_ok=True)
            steps = []
            steps.append(("write", lint(compiler, source, *jsonl, "--baseline", baseline, "--write-baseline")))
            steps.append(("written file", (0, baseline.read_bytes(), b"")))
            steps.append(("matched", lint(compiler, source, *jsonl, "--baseline", baseline,
                                          "--deny", "discarded_failure")))
            config = scratch / "baseline-config.json"
            config.write_text(json.dumps({"schema_version": 1, "default_groups": ["correctness"],
                                          "deny": ["discarded_failure"], "baseline": str(baseline)}))
            steps.append(("config baseline", lint(compiler, source, *jsonl, "--config", config)))
            source.write_text(source.read_text().replace("    42;", "    42;\n    99;"))
            steps.append(("new finding", lint(compiler, source, *jsonl, "--baseline", baseline,
                                              "--deny", "unused_pure_value")))
            source.write_text(source.read_text().replace("    42;\n    99;", "    let saved = 42;"))
            steps.append(("stale", lint(compiler, source, *jsonl, "--baseline", baseline,
                                        "--deny", "stale_baseline")))
            stored = json.loads(baseline.read_text())
            stored["entries"].append(stored["entries"][0])
            duplicate = scratch / "duplicate-baseline.json"
            duplicate.write_text(json.dumps(stored))
            steps.append(("duplicate entry", lint(compiler, source, *jsonl, "--baseline", duplicate)))
            sequences.append(steps)
        for (label, a), (_, b) in zip(*sequences):
            self.tally("diagnostics")
            reason = describe(a, b)
            if reason:
                self.difference("diagnostics", f"baseline {label}", reason)

        # An install without its companion, and a relocated install run from
        # an unrelated directory without --stdlib.
        installs = []
        for compiler in (self.candidate, self.baseline):
            root = self.scratch / f"install-{compiler.name}"
            for name, with_companion in (("lonely", False), ("relocated", True)):
                bin_dir = root / name / "bin"
                bin_dir.mkdir(parents=True)
                shutil.copy2(compiler.goose, bin_dir / compiler.goose.name)
                if with_companion:
                    shutil.copy2(compiler.companion, bin_dir / "goose-lint")
                    shutil.copytree(STDLIB, root / name / "stdlib")
            cwd = root / "cwd"
            cwd.mkdir()
            lonely = lint(compiler, fixture, *jsonl, goose=root / "lonely/bin" / compiler.goose.name)
            relocated = lint(compiler, fixture, *jsonl, "--group", "correctness", cwd=cwd, stdlib=False,
                             goose=root / "relocated/bin" / compiler.goose.name)
            installs.append((lonely, relocated))
        for index, label in enumerate(("missing companion", "relocated install")):
            self.tally("diagnostics")
            # The missing-companion error names no path; the relocated run's
            # output must not either, so no normalization beyond the compiler's.
            reason = describe(installs[0][index], installs[1][index])
            if reason:
                self.difference("diagnostics", label, reason)

    # --- facts ---------------------------------------------------------------

    def facts_install(self, compiler):
        root = self.scratch / f"facts-{compiler.name}"
        bin_dir = root / "bin"
        bin_dir.mkdir(parents=True)
        shutil.copy2(compiler.goose, bin_dir / "goose")
        wrapper = bin_dir / "goose-lint"
        wrapper.write_text(
            '#!/bin/sh\nprev=\nfor a in "$@"; do\n'
            '  if [ "$prev" = --facts ]; then cp "$a" "$LINT_PARITY_FACTS_OUT" || exit 4; fi\n'
            '  prev=$a\ndone\nexec "$LINT_PARITY_REAL" "$@"\n')
        wrapper.chmod(0o755)
        return bin_dir / "goose"

    def facts(self, extra_sources):
        installed = {c.name: self.facts_install(c) for c in (self.candidate, self.baseline)}
        sources = [ROOT / "test/lint" / n for n in ("rules.goose", "review.goose", "contracts.goose",
                                                    "suppressions.goose", "fanout_root_depth.goose")]
        sources += [ROOT / "tools/lint/main.goose"]
        sources += [p for p in marker_fixtures() if p not in sources]
        sources += extra_sources
        self.facts_sources = len(sources)
        revisions = {}

        def capture(compiler, source):
            out = self.scratch / f"facts-out-{compiler.name}-{abs(hash(str(source)))}"
            env = dict(os.environ, LINT_PARITY_FACTS_OUT=str(out), LINT_PARITY_REAL=str(compiler.companion))
            result = run([installed[compiler.name], "lint", source, "--stdlib", STDLIB, "--format", "jsonl"],
                         env=env)
            data = compiler.normalize(out.read_bytes()) if out.exists() else None
            out.unlink(missing_ok=True)
            if data is not None:
                header = json.loads(data.split(b"\n", 1)[0])
                revisions[compiler.name] = header.get("compiler_revision")
            return (result.returncode, data)

        def both(source):
            return source, capture(self.candidate, source), capture(self.baseline, source)

        with ThreadPoolExecutor(self.jobs) as pool:
            for source, a, b in pool.map(both, sources):
                self.tally("facts")
                label = str(source.relative_to(ROOT)) if source.is_relative_to(ROOT) else source.name
                if a[1] is None and b[1] is None:
                    continue
                if a != b:
                    reason = "no facts on one side" if None in (a[1], b[1]) else self.first_difference(a[1], b[1])
                    self.difference("facts", label, reason)
        self.facts_streams = sum(1 for _ in sources)
        if revisions and revisions.get(self.candidate.name) != revisions.get(self.baseline.name):
            self.difference("facts", "compiler_revision", f"{revisions}")

    @staticmethod
    def first_difference(a, b):
        for number, (x, y) in enumerate(zip(a.splitlines(), b.splitlines()), 1):
            if x != y:
                return f"record {number}: {x[:160]!r} != {y[:160]!r}"
        return f"record counts {len(a.splitlines())} != {len(b.splitlines())}"

    # --- ordinary warnings -----------------------------------------------------

    def warnings(self):
        jobs = []
        for source in marker_fixtures():
            for options in (["--check"], ["--check", "-O0"], ["--check", "-O2"], ["--roundtrip", "--check"]):
                label = f"{source.relative_to(ROOT)} {' '.join(options)}"
                jobs.append((label, lambda c, s=source, o=options: check_run(c, s, *o)))

        def seen(compiler):
            lines = 0
            for source in marker_fixtures():
                result = check_run(compiler, source, "--check")
                lines += sum(1 for line in (result[1] + result[2]).splitlines() if b": warning: " in line)
            return lines
        self.compare_pairs("warnings", jobs)
        self.warning_lines = seen(self.candidate)
        if self.warning_lines == 0:
            self.difference("warnings", "vacuous", "no warning line was printed by any marker fixture")

    # --- fanout --------------------------------------------------------------------

    def fanout(self):
        program = self.scratch / "fanout"
        subprocess.run([sys.executable, str(ROOT / "test/scale/gen.py"), "--shareable", "2",
                        "--root-params", "3", "--helpers", "3", "--contexts", "6", "--distinct",
                        "--out", str(program)], check=True, capture_output=True)
        source = program / "main.goose"
        options = ["--format", "jsonl", "--group", "performance"]
        a, b = lint(self.candidate, source, *options), lint(self.baseline, source, *options)
        self.tally("fanout")
        reason = describe(a, b)
        if reason:
            self.difference("fanout", "lint output", reason)
        records = [json.loads(line) for line in a[1].decode().splitlines()]
        coverage = [r for r in records if r["kind"] == "coverage"][0]
        findings = [r for r in records if r["kind"] == "diagnostic" and r["code"] == "specialization_fanout"]
        report = self.scratch / "fanout-report.json"
        built = run([self.candidate.goose, "-O2", "--share", "--standalone", "--stdlib", STDLIB,
                     "--build-report", report, "-o", program / "main.c", source])
        if built.returncode != 0:
            self.difference("fanout", "candidate build", built.stderr.decode()[-300:])
            return
        counts = json.loads(report.read_text())
        sharing = counts["extensions"]["sharing"]
        counts = counts["counts"]
        self.fanout_numbers = {
            "lint_checked_specializations": coverage["checked_specializations"],
            "report_entry_reachable_contexts": counts["entry_reachable_contexts"],
            "report_checked_contexts": counts["checked_contexts"],
            "report_emitted_instances": counts["emitted_instances"]["total"],
            "implementations_after_share": sharing["functions_after"],
            "fanout_findings": len(findings),
        }
        n = self.fanout_numbers
        self.tally("fanout")
        if n["lint_checked_specializations"] != n["report_entry_reachable_contexts"]:
            self.difference("fanout", "contexts", f"lint counts {n['lint_checked_specializations']}, "
                            f"report counts {n['report_entry_reachable_contexts']}")
        self.tally("fanout")
        if not n["implementations_after_share"] < n["report_entry_reachable_contexts"]:
            self.difference("fanout", "implementations", f"{n['implementations_after_share']} emitted is not "
                            f"fewer than {n['report_entry_reachable_contexts']} contexts")
        self.tally("fanout")
        if not findings:
            self.difference("fanout", "vacuous", "the program produced no fanout finding")
        self.fanout_source = source

    # --- no backend in check ---------------------------------------------------------------

    def backend(self):
        sources = [ROOT / "test/lint/rules.goose", ROOT / "tools/lint/main.goose", self.fanout_source]
        for source in sources:
            self.tally("backend")
            report = self.scratch / "check-report.json"
            report.unlink(missing_ok=True)
            result = run([self.candidate.goose, "--check", "--stdlib", STDLIB, "--build-report", report, source])
            label = source.name
            if result.returncode != 0 or not report.exists():
                self.difference("backend", label, f"--check --build-report failed ({result.returncode})")
                continue
            data = json.loads(report.read_text())
            phases = set(data["phases"])
            if not phases <= FRONTEND_PHASES:
                self.difference("backend", label, f"phases beyond the frontend: {sorted(phases - FRONTEND_PHASES)}")
            extensions = data["extensions"]
            if data["output"] is not None or any(extensions[k] is not None
                                                 for k in ("sharing", "units", "native_compile")):
                self.difference("backend", label, "output, sharing, units or native compile recorded")
            if any(data["counts"][k] is not None for k in ("emitted_instances", "live_instances", "runtime_text")):
                self.difference("backend", label, "emitted counts recorded by a check")
            plain = run([self.candidate.goose, "--check", "--stdlib", STDLIB, source])
            self.tally("backend")
            quiet = run([self.candidate.goose, "--check", "--stdlib", STDLIB, source])
            if plain.stdout != quiet.stdout:
                self.difference("backend", label, "check output not deterministic")


def stripped_path():
    keep = []
    for directory in os.environ.get("PATH", "").split(os.pathsep):
        if directory and not any((Path(directory) / tool).exists() for tool in ("lean", "lake")):
            keep.append(directory)
    return os.pathsep.join(keep)


def suites(candidate, differences):
    """The linter suite and the facts scale case against the candidate with
    no directory holding lean or lake on PATH."""
    env = dict(os.environ, PATH=stripped_path())
    results = {}
    for script in ("run_tests.py", "facts_scale.py"):
        result = subprocess.run([sys.executable, str(ROOT / "test/lint" / script), "--goose", str(candidate.goose)],
                                cwd=ROOT, env=env, capture_output=True, text=True)
        results[script] = result.returncode
        if result.returncode != 0:
            differences.append(f"DIFF suite {script}: exit {result.returncode}: {(result.stdout + result.stderr)[-300:]}")
    return results


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--goose", type=Path, required=True, help="candidate compiler")
    parser.add_argument("--baseline", type=Path, required=True, help="reference compiler")
    parser.add_argument("--jobs", type=int, default=4)
    parser.add_argument("--suites", action="store_true",
                        help="also run test/lint/run_tests.py and facts_scale.py on the candidate, "
                             "with lean and lake off PATH")
    args = parser.parse_args()
    candidate, baseline = Compiler("candidate", args.goose), Compiler("baseline", args.baseline)
    for compiler in (candidate, baseline):
        if not compiler.goose.is_file() or not compiler.companion.is_file():
            sys.exit(f"{compiler.name}: no goose and goose-lint at {compiler.goose}")

    work = ROOT / ".work" / "tmp"
    work.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="lint-parity-", dir=work) as directory:
        parity = Parity(candidate, baseline, Path(directory), args.jobs)
        parity.diagnostics()
        parity.fanout()
        parity.facts([parity.fanout_source] if hasattr(parity, "fanout_source") else [])
        parity.warnings()
        parity.backend() if hasattr(parity, "fanout_source") else None
        suite_results = suites(candidate, parity.differences) if args.suites else None
        cast = Path(directory) / "cast_and_marker.goose"
        cast_contexts = {}
        for compiler in (candidate, baseline):
            records = [json.loads(line) for line in
                       lint(compiler, cast, "--format", "jsonl")[1].decode().splitlines()]
            for record in records:
                if record["kind"] == "diagnostic":
                    cast_contexts.setdefault(compiler.name, {})[record["code"]] = len(record["specializations"])

    for line in parity.differences:
        print(line)
    summary = {
        "kind": "summary",
        "differences": len(parity.differences),
        "compared": parity.counts,
        "lint_inputs": parity.core_count + parity.marker_count,
        "option_sets_per_core_input": parity.option_set_count,
        "facts_streams": parity.facts_streams,
        "marker_fixtures": parity.marker_count,
        "warning_lines": parity.warning_lines,
        "fanout": getattr(parity, "fanout_numbers", None),
        "normalized_compiler_dir_replacements": {"candidate": candidate.normalized,
                                                  "baseline": baseline.normalized},
        "specialization_contexts_per_warning_code": cast_contexts,
        "suites": suite_results,
    }
    print(json.dumps(summary, sort_keys=True))
    sys.exit(1 if parity.differences else 0)


if __name__ == "__main__":
    main()
