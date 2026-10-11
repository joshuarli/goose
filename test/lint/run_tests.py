#!/usr/bin/env python3
"""Focused black-box tests for the bundled Goose linter."""

import argparse
from concurrent.futures import ThreadPoolExecutor
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[2]
FIXTURES = Path(__file__).resolve().parent


def check(condition, message):
    if not condition:
        raise AssertionError(message)


def find_built_goose():
    executable = "goose.exe" if os.name == "nt" else "goose"
    for configuration in ("Debug", "", "Release", "RelWithDebInfo"):
        candidate = ROOT / "build" / configuration / executable
        if candidate.is_file():
            return candidate
    raise AssertionError("no Goose executable under build/; pass --goose or build the default CMake targets")


def parse_jsonl(result, label):
    try:
        records = [json.loads(line) for line in result.stdout.splitlines()]
    except (json.JSONDecodeError, UnicodeDecodeError) as error:
        raise AssertionError(f"{label}: invalid JSONL: {error}\n{result.stdout}\n{result.stderr}")
    check(records, f"{label}: empty JSONL output")
    check(records[0].get("kind") == "header", f"{label}: missing header")
    check(records[-1].get("kind") == "summary", f"{label}: missing summary")
    return records


def find_records(records, kind):
    return [record for record in records if record.get("kind") == kind]


def check_rule_contracts(records, contracts, label):
    by_code = {rule["code"]: rule for rule in contracts}
    messages = {}
    for diagnostic in find_records(records, "diagnostic"):
        rule = by_code.get(diagnostic["code"])
        check(rule is not None, f"{label}: diagnostic uses an undocumented rule {diagnostic['code']}")
        example = rule["json_example"]
        check(diagnostic["group"] == rule["group"] and diagnostic["severity"] == rule["severity"] and
              diagnostic["confidence"] == rule["confidence"],
              f"{label}: output metadata differs from the rule contract for {rule['code']}")
        check(diagnostic["code"] == example["code"] and diagnostic["group"] == example["group"] and
              diagnostic["severity"] == example["severity"] and diagnostic["confidence"] == example["confidence"],
              f"{label}: JSON example metadata differs for {rule['code']}")
        evidence = diagnostic["evidence"]
        expected = rule["json_evidence"]
        if expected is None:
            check(evidence is None, f"{label}: {rule['code']} unexpectedly added semantic evidence")
        else:
            check(isinstance(evidence, dict) and all(key in evidence for key in expected),
                  f"{label}: {rule['code']} omitted evidence keys from its rule contract")
        example_keys = example["evidence_keys"]
        check((evidence is None and not example_keys) or
              (isinstance(evidence, dict) and all(key in evidence for key in example_keys)),
              f"{label}: JSON example evidence is missing for {rule['code']}")
        messages.setdefault(rule["code"], []).append(diagnostic["message"])
    for code, rule in by_code.items():
        if code in messages:
            check(any(rule["text_example"] in message for message in messages[code]),
                  f"{label}: text example was not observed for {code}")


def run_lint(goose, source, *options, env=None):
    command = [str(goose), "lint", str(source), "--stdlib", str(ROOT / "stdlib"), *options]
    return subprocess.run(command, cwd=ROOT, env=env, text=True, capture_output=True)


def check_rule_example(goose, code, source, options, examples, env):
    expected = examples["rules"][code]
    json_result = run_lint(goose, source, "--format", "jsonl", *options, env=env)
    records = parse_jsonl(json_result, f"{code} JSON example")
    check(json_result.returncode == 0 and expected["diagnostic"] in find_records(records, "diagnostic"),
          f"{code} JSON diagnostic snapshot changed")
    text_result = run_lint(goose, source, *options, env=env)
    check(text_result.returncode == 0 and expected["text"] in text_result.stdout.splitlines(),
          f"{code} text diagnostic snapshot changed")


def fnv1a64(data):
    value = 14695981039346656037
    for byte in data:
        value = ((value ^ byte) * 1099511628211) & 0xFFFFFFFFFFFFFFFF
    return f"fnv1a64:{value:016x}"


def encode_facts(records):
    lines = [json.dumps(record, separators=(",", ":")) for record in records]
    integrity = fnv1a64(("\n".join(lines) + "\n").encode())
    lines.append(json.dumps({"kind": "end", "record_count": len(records), "integrity": integrity}, separators=(",", ":")))
    return "\n".join(lines) + "\n"


def minimal_fact_records():
    return [
        {"kind": "header", "facts_version": 1, "compiler": "goose", "compiler_revision": "test-runtime",
         "entries": ["synthetic.goose"], "profile": "O1",
         "frontend_options": {"debug": False, "unsafe_no_rf_check": False, "allow_fetch": False}},
        {"kind": "source", "file_id": 0, "path": "synthetic.goose", "content_hash": "fnv1a64:0000000000000000",
         "byte_length": 0, "line_endings": "none"},
        {"kind": "coverage", "file_id": 0, "path": "synthetic.goose", "parse": "complete",
         "semantic": "entry-reachable-specializations", "checked_specializations": 0,
         "unchecked_generics": 0, "unsupported": []},
    ]


def minimal_facts():
    return encode_facts(minimal_fact_records())


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--goose", type=Path, help="built goose executable (default: find it under build/)")
    args = parser.parse_args()
    goose = (args.goose or find_built_goose()).resolve()
    contracts_doc = json.loads((FIXTURES / "rule_contracts.json").read_text())
    check(contracts_doc.get("schema_version") == 1, "rule-contract fixture schema changed")
    contracts = contracts_doc.get("rules", [])
    required_codes = {
        "redundant_cast", "redundant_reference_marker", "avoidable_reference_copy",
        "discarded_failure", "unchecked_poll_result", "unused_pure_value", "stale_suppression",
        "post_overflow_guard", "stale_slice_length", "specialization_fanout",
        "view_before_append_argument", "foreign_container_index",
    }
    rule_examples = json.loads((FIXTURES / "expected/rule_examples.json").read_text())
    check(rule_examples.get("schema_version") == 1 and set(rule_examples.get("rules", {})) == required_codes,
          "per-rule JSON/text snapshot fixture must cover the 12 required rules exactly once")
    check({rule.get("code") for rule in contracts} == required_codes and len(contracts) == 12,
          "rule-contract fixture must describe each required rule exactly once")
    for rule in contracts:
        check(rule.get("severity") and rule.get("confidence") and rule.get("positive") and
              len(rule.get("counterexamples", [])) >= 2 and rule.get("triggering_proof") and
              rule.get("text_example") and isinstance(rule.get("json_example"), dict) and
              rule.get("context") and rule.get("cost"),
              f"rule-contract fixture is incomplete for {rule.get('code')}")

    inventory = (ROOT / "docs/lint/rule-inventory.md").read_text()
    required_section, remainder = inventory.split("## Required v1 — 12", 1)
    required_body, deferred_body = remainder.split("## Deferred — 53", 1)
    inventory_ids = re.findall(r"^\| ([a-z][a-z0-9_]*) \|", inventory, re.M)
    required_ids = re.findall(r"^\| ([a-z][a-z0-9_]*) \|", required_body, re.M)
    deferred_ids = re.findall(r"^\| ([a-z][a-z0-9_]*) \|", deferred_body, re.M)
    check(len(inventory_ids) == 65 and len(set(inventory_ids)) == 65 and
          set(required_ids) == required_codes and len(required_ids) == 12 and
          len(deferred_ids) == 53 and not set(required_ids) & set(deferred_ids),
          "rule inventory must contain the 12 required and 53 deferred Issue #10 IDs exactly once")

    companion = goose.with_name("goose-lint")
    if os.name == "nt":
        companion = goose.with_name("goose-lint.exe")
    check(goose.is_file(), f"goose executable does not exist: {goose}")
    check(companion.is_file(), f"lint companion does not exist: {companion}")
    help_result = subprocess.run([str(goose), "lint", "--help"], cwd=ROOT, text=True, capture_output=True)
    check(help_result.returncode == 0 and "exit status" in help_result.stdout.lower() and
          "specialization_fanout" in help_result.stdout and "foreign_container_index" in help_result.stdout,
          "lint help omitted rules or statuses")

    with tempfile.TemporaryDirectory(prefix="goose-lint-tests-") as temporary:
        temp = Path(temporary)
        env = os.environ.copy()
        env["GOOSE_HOME"] = str(temp / "goose-home")

        # A relocated executable/companion pair finds its packaged standard
        # library when launched from an unrelated working directory.
        install_root = temp / "installed ü space"
        installed_bin = install_root / "bin"
        unrelated_cwd = temp / "unrelated cwd"
        installed_bin.mkdir(parents=True)
        unrelated_cwd.mkdir()
        installed_goose = installed_bin / goose.name
        shutil.copy2(goose, installed_goose)
        shutil.copy2(companion, installed_bin / companion.name)
        shutil.copytree(ROOT / "stdlib", install_root / "stdlib")
        relocated = subprocess.run(
            [str(installed_goose), "lint", str(FIXTURES / "rules.goose"), "--format", "jsonl", "--group", "correctness"],
            cwd=unrelated_cwd, env=env, text=True, capture_output=True,
        )
        relocated_records = parse_jsonl(relocated, "relocated install")
        relocated_diagnostics = find_records(relocated_records, "diagnostic")
        check(relocated.returncode == 0 and len(relocated_diagnostics) == 6 and
              relocated_records[0]["entries"] == ["rules.goose"] and
              all(str(temp) not in json.dumps(record) for record in relocated_records),
              "relocated install failed from a path containing spaces/Unicode or exposed host paths")

        # The normal result is deterministic JSONL and does not run the target.
        fixture = FIXTURES / "rules.goose"
        first = run_lint(goose, fixture, "--format", "jsonl", env=env)
        records = parse_jsonl(first, "rules fixture")
        check(first.returncode == 0, f"default analysis returned {first.returncode}: {first.stderr}")
        check("target-program-ran" not in first.stdout, "lint executed or printed target program output")
        diagnostics = find_records(records, "diagnostic")
        counts = {}
        for diagnostic in diagnostics:
            counts[diagnostic["code"]] = counts.get(diagnostic["code"], 0) + 1
        check(counts.get("discarded_failure") == 3, f"unexpected parse status findings: {counts}")
        overwritten_status = next(d for d in diagnostics if d["code"] == "discarded_failure" and
                                 d["evidence"].get("use") == "overwritten")
        check("overwritten before inspection" in overwritten_status["message"],
              "an unchecked status overwritten before a later read was not identified accurately")
        check(counts.get("unchecked_poll_result") == 3, f"unexpected qpoll status findings: {counts}")
        check(counts.get("unused_pure_value") == 5, f"unexpected pure-value findings: {counts}")
        pure_findings = [d for d in diagnostics if d["code"] == "unused_pure_value"]
        check(sum(d["evidence"]["expression_kind"] == "constant_integer_expression" for d in pure_findings) == 1,
              "unused_pure_value did not accept one proven constant operation or admitted an unproven operation")
        check(not counts.get("specialization_fanout"), "opt-in fanout ran by default")
        check_rule_contracts(records, contracts, "default rules")
        second = run_lint(goose, fixture, "--format", "jsonl", env=env)
        check(second.returncode == 0 and second.stdout == first.stdout, "JSONL output is not repeatable")
        with ThreadPoolExecutor(max_workers=2) as pool:
            concurrent = list(pool.map(lambda _: run_lint(goose, fixture, "--format", "jsonl", env=env), range(2)))
        check(all(result.returncode == 0 and result.stdout == first.stdout for result in concurrent),
              "concurrent lint invocations interfered with one another")

        # Byte offsets survive CRLF, multibyte UTF-8, and tabs; a directive-like
        # string in a raw string is data rather than a suppression comment.
        source_bytes = (
            '// π\r\nimport std;\r\nfn main() {\r\n\tlet parsed, status = parse_int("42");\r\n'
            '\tprint(parsed);\r\n\tlet text = """goose-lint: allow[not_a_rule] -- raw text""";\r\n}\r\n'
        ).encode("utf-8")
        span_source = temp / "utf8-crlf.goose"
        span_source.write_bytes(source_bytes)
        spans = run_lint(goose, span_source, "--format", "jsonl", env=env)
        span_records = parse_jsonl(spans, "CRLF/UTF-8 span fixture")
        span_diagnostics = find_records(span_records, "diagnostic")
        check(spans.returncode == 0 and len(span_diagnostics) == 1 and
              span_diagnostics[0]["code"] == "discarded_failure" and
              not any(d["code"] == "stale_suppression" for d in span_diagnostics),
              "raw-string directive text was treated as a comment or valid source was rejected")
        primary = span_diagnostics[0]["primary"]
        check(primary["start_line"] == 4 and primary["start_column"] == 23 and
              source_bytes[primary["start_byte"]:primary["end_byte"]] == b'parse_int("42")',
              "CRLF, UTF-8, or tab indentation corrupted the exact source range")
        text_result = run_lint(goose, fixture, env=env)
        check(text_result.returncode == 0 and "warning[discarded_failure]" in text_result.stdout,
              "text output omitted the supported warning")
        for option, profile in (("-O0", "O0"), ("-O1", "O1"), ("-O2", "O2")):
            profiled = run_lint(goose, fixture, "--format", "jsonl", option, env=env)
            profile_records = parse_jsonl(profiled, option)
            check(profiled.returncode == 0 and profile_records[0]["profile"] == profile,
                  f"{option} profile was not preserved in output")

        denied = run_lint(goose, fixture, "--format", "jsonl", "--deny", "discarded_failure", env=env)
        parse_jsonl(denied, "denied finding")
        check(denied.returncode == 1, f"--deny returned {denied.returncode}, expected 1")
        allowed = run_lint(goose, fixture, "--format", "jsonl", "--allow", "discarded_failure", env=env)
        allowed_records = parse_jsonl(allowed, "allowed finding")
        check(allowed.returncode == 0 and not any(d["code"] == "discarded_failure" for d in find_records(allowed_records, "diagnostic")),
              "--allow did not remove the selected finding")

        performance = run_lint(goose, fixture, "--format", "jsonl", "--group", "performance", env=env)
        performance_records = parse_jsonl(performance, "performance group")
        performance_codes = [d["code"] for d in find_records(performance_records, "diagnostic")]
        check(performance.returncode == 0 and performance_codes == ["specialization_fanout"],
              f"unexpected performance-group findings: {performance_codes}")
        fanout = find_records(performance_records, "diagnostic")[0]
        check(fanout["primary"]["precision"] == "exact",
              "specialization fanout lost its declaration span")
        check("identity" in fanout["evidence"]["function"] and len(fanout["specializations"]) == 2,
              "fanout omitted the source function or actual contributor contexts")
        root_depth_fixture = FIXTURES / "fanout_root_depth.goose"
        root_depth_result = run_lint(
            goose, root_depth_fixture, "--format", "jsonl", "--group", "performance", env=env,
        )
        root_depth_records = parse_jsonl(root_depth_result, "root-depth fanout")
        root_depth_diagnostics = find_records(root_depth_records, "diagnostic")
        root_depth_coverage = find_records(root_depth_records, "coverage")
        check(root_depth_result.returncode == 0 and len(root_depth_diagnostics) == 1 and
              root_depth_diagnostics[0]["evidence"]["reachable_specializations"] == 2 and
              len(root_depth_coverage) == 1 and root_depth_coverage[0]["check"] == "complete" and
              root_depth_coverage[0]["checked_specializations"] == 3,
              "global/local root fanout changed its complete count")
        root_depth_contexts = root_depth_diagnostics[0]["specializations"]
        check(len(root_depth_contexts) == 2 and len(set(root_depth_contexts)) == 2 and
              any(":depthkey0:" in context for context in root_depth_contexts) and
              any(":depthkey-1:" in context for context in root_depth_contexts),
              "fanout contexts did not expose the distinct global/local depth keys")
        denied_fanout = run_lint(goose, fixture, "--format", "jsonl", "--deny", "specialization_fanout", env=env)
        parse_jsonl(denied_fanout, "denied fanout")
        check(denied_fanout.returncode == 1, "explicit fanout denial did not fail")
        check_rule_contracts(performance_records, contracts, "performance rules")

        review_fixture = FIXTURES / "review.goose"
        review = run_lint(goose, review_fixture, "--format", "jsonl", "--group", "review", env=env)
        review_records = parse_jsonl(review, "review rules")
        review_diagnostics = find_records(review_records, "diagnostic")
        expected_review = json.loads((FIXTURES / "expected/review.json").read_text())
        check(review_diagnostics == expected_review,
              "review JSON diagnostic snapshot changed")
        review_text = run_lint(goose, review_fixture, "--group", "review", env=env)
        check(review_text.returncode == 0 and review_text.stdout == (FIXTURES / "expected/review.txt").read_text(),
              "review text snapshot changed")
        review_counts = {}
        for diagnostic in review_diagnostics:
            review_counts[diagnostic["code"]] = review_counts.get(diagnostic["code"], 0) + 1
        check(review.returncode == 0 and review_counts == {"post_overflow_guard": 2, "stale_slice_length": 1},
              f"restricted review proof shapes changed or admitted a counterexample: {review_counts}")
        check_rule_contracts(review_records, contracts, "review rules")
        overflow = next(d for d in review_diagnostics if d["code"] == "post_overflow_guard")
        check(overflow["confidence"] == "medium" and "debug builds trap" in overflow["message"] and
              overflow["evidence"]["attempted_guard"]["start_byte"] > overflow["primary"]["start_byte"],
              "overflow review omitted debug/release behavior or related guard evidence")
        stale_slice = next(d for d in review_diagnostics if d["code"] == "stale_slice_length")
        check(stale_slice["evidence"]["captured_length_is_fixed"] and stale_slice["evidence"]["same_root"],
              "stale-slice evidence omitted the captured-length/root proof")
        denied_overflow = run_lint(goose, review_fixture, "--format", "jsonl", "--deny", "post_overflow_guard", env=env)
        parse_jsonl(denied_overflow, "denied overflow review")
        check(denied_overflow.returncode == 1, "post_overflow_guard was not selectable for denial")

        no_project_contracts = run_lint(goose, FIXTURES / "contracts.goose", "--format", "jsonl",
                                        "--group", "project", "--require-complete", env=env)
        no_project_records = parse_jsonl(no_project_contracts, "missing project contracts")
        check(no_project_contracts.returncode == 4 and
              any(item.get("analysis") == "foreign_container_index" for cov in find_records(no_project_records, "coverage") for item in cov["unsupported"]),
              "selected project analysis without a contract file was reported complete")

        contract_file = temp / "lint-contracts.json"
        contract_file.write_text(json.dumps({"schema_version": 1, "apis": [
            {"callee": "contracts::append_and_return", "role": "append_to", "owner_arg": 0},
            {"callee": "contracts::after_append", "role": "view_after_append", "view_arg": 0, "append_arg": 1},
            {"callee": "contracts::find_for", "role": "index_of", "owner_arg": 0},
            {"callee": "contracts::use_index", "role": "consumes_index", "owner_arg": 0, "index_arg": 1},
        ]}))
        contract_config = temp / "contracts-config.json"
        contract_config.write_text(json.dumps({"schema_version": 1, "default_groups": ["project"],
                                              "enable": [], "contracts": str(contract_file)}))
        project = run_lint(goose, FIXTURES / "contracts.goose", "--format", "jsonl", "--config", str(contract_config), env=env)
        project_records = parse_jsonl(project, "project contract rules")
        project_counts = {}
        for diagnostic in find_records(project_records, "diagnostic"):
            project_counts[diagnostic["code"]] = project_counts.get(diagnostic["code"], 0) + 1
        check(project.returncode == 0 and project_counts == {"view_before_append_argument": 1, "foreign_container_index": 1},
              f"project contracts did not distinguish same-owner from foreign-owner cases: {project_counts}")
        check_rule_contracts(project_records, contracts, "project rules")

        examples = (
            ("redundant_cast", ROOT / "test/typing/redundant_casts.goose", ["--group", "existing"]),
            ("redundant_reference_marker", ROOT / "test/typing/warnings_once.goose", ["--group", "existing"]),
            ("avoidable_reference_copy", ROOT / "test/typing/warnings_once.goose", ["--group", "existing"]),
            ("discarded_failure", FIXTURES / "rules.goose", ["--group", "correctness"]),
            ("unchecked_poll_result", FIXTURES / "rules.goose", ["--group", "correctness"]),
            ("unused_pure_value", FIXTURES / "rules.goose", ["--group", "suspicious"]),
            ("stale_suppression", FIXTURES / "suppressions.goose", []),
            ("post_overflow_guard", FIXTURES / "review.goose", ["--group", "review"]),
            ("stale_slice_length", FIXTURES / "review.goose", ["--group", "review"]),
            ("specialization_fanout", FIXTURES / "rules.goose", ["--group", "performance"]),
            ("view_before_append_argument", FIXTURES / "contracts.goose", ["--config", str(contract_config)]),
            ("foreign_container_index", FIXTURES / "contracts.goose", ["--config", str(contract_config)]),
        )
        for code, source, options in examples:
            check_rule_example(goose, code, source, options, rule_examples, env)

        denied_foreign = run_lint(goose, FIXTURES / "contracts.goose", "--format", "jsonl", "--config",
                                  str(contract_config), "--deny", "foreign_container_index", env=env)
        parse_jsonl(denied_foreign, "denied foreign-container index")
        check(denied_foreign.returncode == 1, "foreign_container_index was not selectable for denial")

        contract_file.write_text(json.dumps({"schema_version": 1, "apis": [
            {"callee": "contracts::use_index", "role": "consumes_index", "owner_arg": 99, "index_arg": 1},
        ]}))
        drift = run_lint(goose, FIXTURES / "contracts.goose", "--format", "jsonl", "--config", str(contract_config), env=env)
        drift_records = parse_jsonl(drift, "contract arity drift")
        check(drift.returncode == 3 and find_records(drift_records, "error")[0]["code"] == "invalid_config",
              "contract arity drift was silently ignored")

        incomplete = run_lint(goose, fixture, "--format", "jsonl", "--require-complete", env=env)
        incomplete_records = parse_jsonl(incomplete, "required complete analysis")
        check(incomplete.returncode == 4 and any(r.get("code") == "analysis_incomplete" for r in incomplete_records),
              "--require-complete did not report unsupported analysis")

        # Local directives bind to one statement; strings are not comments.
        suppression = run_lint(goose, FIXTURES / "suppressions.goose", "--format", "jsonl", env=env)
        suppression_records = parse_jsonl(suppression, "suppression fixture")
        suppression_diagnostics = find_records(suppression_records, "diagnostic")
        check(any(d["code"] == "discarded_failure" and d["suppression"] for d in suppression_diagnostics),
              "valid reasoned suppression was not applied")
        stale_count = sum(d["code"] == "stale_suppression" for d in suppression_diagnostics)
        check(stale_count == 4, f"expected malformed, duplicate, unknown, and unmatched suppression diagnostics, got {stale_count}")
        check_rule_contracts(suppression_records, contracts, "suppression rules")

        for fixture_path, selected, expected_counts in (
            (FIXTURES / "rules.goose", "correctness", {"discarded_failure": 3, "unchecked_poll_result": 3}),
            (FIXTURES / "rules.goose", "suspicious", {"unused_pure_value": 5}),
            (ROOT / "test/typing/redundant_casts.goose", "existing", {"redundant_cast": 13}),
            (ROOT / "test/typing/warnings_once.goose", "existing",
             {"redundant_reference_marker": 10, "avoidable_reference_copy": 1}),
        ):
            result = run_lint(goose, fixture_path, "--format", "jsonl", "--group", selected, env=env)
            result_records = parse_jsonl(result, f"rule contract {fixture_path.name}")
            counts = {}
            for diagnostic in find_records(result_records, "diagnostic"):
                counts[diagnostic["code"]] = counts.get(diagnostic["code"], 0) + 1
            check(result.returncode == 0 and counts == expected_counts,
                  f"rule contract counts changed for {fixture_path.name}: {counts}")
            if fixture_path.name == "rules.goose" and selected == "suspicious":
                pure_findings = [d for d in find_records(result_records, "diagnostic") if d["code"] == "unused_pure_value"]
                check(sum(d["evidence"]["expression_kind"] == "constant_integer_expression" for d in pure_findings) == 1,
                      "unused_pure_value did not accept one proven constant operation or admitted an unproven operation")
            if fixture_path.name == "warnings_once.goose":
                warning_contexts = [d["specializations"] for d in find_records(result_records, "diagnostic")
                                    if d["code"] == "redundant_reference_marker"]
                check(warning_contexts and all(warning_contexts) and
                      any(len(contexts) > 1 for contexts in warning_contexts),
                      "repeated generic warning did not retain its checked specialization contexts")
            check_rule_contracts(result_records, contracts, fixture_path.name)

        # Baselines match exact rule/context occurrences, preserve findings in
        # output, expose new findings, and report removed findings as stale.
        baseline_source = temp / "rules.goose"
        shutil.copyfile(fixture, baseline_source)
        baseline = temp / "baseline.json"
        write = run_lint(goose, baseline_source, "--format", "jsonl", "--baseline", str(baseline), "--write-baseline", env=env)
        write_records = parse_jsonl(write, "baseline write")
        check(write.returncode == 0 and baseline.is_file(), "explicit baseline write failed")
        saved_baseline = json.loads(baseline.read_text())
        check(saved_baseline["schema_version"] == 1 and saved_baseline["fingerprint_version"] == 1,
              "baseline version fields are invalid")
        matched = run_lint(goose, baseline_source, "--format", "jsonl", "--baseline", str(baseline), "--deny", "discarded_failure", env=env)
        matched_records = parse_jsonl(matched, "matching baseline")
        check(matched.returncode == 0, "a matched baseline finding still triggered --deny")
        check(matched_records[-1]["baselined"] == len(saved_baseline["entries"]), "matched findings were removed or miscounted")

        changed_text = baseline_source.read_text().replace("    42;", "    42;\n    99;")
        baseline_source.write_text(changed_text)
        new_finding = run_lint(goose, baseline_source, "--format", "jsonl", "--baseline", str(baseline), "--deny", "unused_pure_value", env=env)
        new_records = parse_jsonl(new_finding, "new finding beside baseline")
        check(new_finding.returncode == 1, "baseline hid a new distinct finding")
        check(new_records[-1]["stale_baseline_entries"] == 0, "a new finding was misreported as stale")

        baseline_source.write_text(baseline_source.read_text().replace("    42;\n    99;", "    let saved = 42;"))
        stale = run_lint(goose, baseline_source, "--format", "jsonl", "--baseline", str(baseline), "--deny", "stale_baseline", env=env)
        stale_records = parse_jsonl(stale, "stale baseline")
        stale_entries = [r for r in stale_records if r.get("kind") == "baseline" and r.get("status") == "stale"]
        check(stale.returncode == 1 and len(stale_entries) == 1, "removed finding was not reported as a denied stale baseline entry")

        malformed_baseline = temp / "malformed-baseline.json"
        malformed_baseline.write_text("{not json")
        bad_baseline = run_lint(goose, fixture, "--format", "jsonl", "--baseline", str(malformed_baseline), env=env)
        bad_baseline_records = parse_jsonl(bad_baseline, "malformed baseline")
        check(bad_baseline.returncode == 3 and find_records(bad_baseline_records, "error")[0]["code"] == "invalid_config",
              "malformed baseline was not rejected")
        duplicate_baseline = temp / "duplicate-baseline.json"
        saved_baseline["entries"].append(saved_baseline["entries"][0])
        duplicate_baseline.write_text(json.dumps(saved_baseline))
        duplicate = run_lint(goose, baseline_source, "--format", "jsonl", "--baseline", str(duplicate_baseline), env=env)
        duplicate_records = parse_jsonl(duplicate, "duplicate baseline entry")
        check(duplicate.returncode == 3 and find_records(duplicate_records, "error")[0]["code"] == "invalid_config",
              "duplicate baseline entry was accepted")

        config = temp / "goose.lint.json"
        config.write_text(json.dumps({
            "schema_version": 1,
            "default_groups": ["correctness"],
            "enable": [],
            "allow": [],
            "deny": ["discarded_failure"],
            "baseline": str(baseline),
        }))
        config_result = run_lint(goose, baseline_source, "--format", "jsonl", "--config", str(config), env=env)
        config_records = parse_jsonl(config_result, "config baseline")
        check(config_result.returncode == 0 and config_records[-1]["baselined"] > 0,
              "config baseline/deny precedence failed")
        severity_config = temp / "severity-config.json"
        severity_config.write_text(json.dumps({
            "schema_version": 1,
            "default_groups": ["correctness"],
            "severity": {"discarded_failure": "error", "unchecked_poll_result": "note"},
        }))
        severity_result = run_lint(goose, fixture, "--format", "jsonl", "--config", str(severity_config), env=env)
        severity_records = parse_jsonl(severity_result, "severity overrides")
        severity_diagnostics = find_records(severity_records, "diagnostic")
        check(severity_result.returncode == 1 and
              {d["severity"] for d in severity_diagnostics if d["code"] == "discarded_failure"} == {"error"} and
              {d["severity"] for d in severity_diagnostics if d["code"] == "unchecked_poll_result"} == {"note"},
              "configuration severity did not change classification and denied-error status")
        allowed_error = run_lint(goose, fixture, "--format", "jsonl", "--config", str(severity_config),
                                "--allow", "discarded_failure", env=env)
        allowed_error_records = parse_jsonl(allowed_error, "allow overrides error severity")
        check(allowed_error.returncode == 0 and
              not any(d["code"] == "discarded_failure" for d in find_records(allowed_error_records, "diagnostic")),
              "CLI allow did not override a configuration error severity")
        invalid_severity = temp / "invalid-severity.json"
        invalid_severity.write_text(json.dumps({"schema_version": 1, "severity": {"discarded_failure": "fatal"}}))
        invalid_severity_result = run_lint(goose, fixture, "--format", "jsonl", "--config", str(invalid_severity), env=env)
        invalid_severity_records = parse_jsonl(invalid_severity_result, "invalid severity")
        check(invalid_severity_result.returncode == 3 and
              find_records(invalid_severity_records, "error")[0]["code"] == "invalid_config",
              "invalid configuration severity was accepted")
        bad_config = temp / "bad-config.json"
        bad_config.write_text('{"schema_version":1,"surprise":true}')
        config_error = run_lint(goose, fixture, "--format", "jsonl", "--config", str(bad_config), env=env)
        config_error_records = parse_jsonl(config_error, "unknown config key")
        check(config_error.returncode == 3 and find_records(config_error_records, "error")[0]["code"] == "invalid_config",
              "unknown config field was accepted")

        no_baseline = run_lint(goose, fixture, "--format", "jsonl", "--write-baseline", env=env)
        no_baseline_records = parse_jsonl(no_baseline, "write without path")
        check(no_baseline.returncode == 3, "--write-baseline without a path was accepted")

        # Compiler failures and analyzer failures retain the documented status.
        bad_source = temp / "bad.goose"
        bad_source.write_text("fn main( {\n")
        syntax_error = run_lint(goose, bad_source, "--format", "jsonl", env=env)
        syntax_records = parse_jsonl(syntax_error, "invalid source")
        check(syntax_error.returncode == 2 and find_records(syntax_records, "error")[0]["code"] == "invalid_source",
              "invalid source status/code changed")

        missing_import = temp / "missing-import.goose"
        missing_import.write_text('import dep from "https://example.invalid/org/dep.git@main";\nfn main() {}\n')
        offline_error = run_lint(goose, missing_import, "--format", "jsonl", env=env)
        offline_records = parse_jsonl(offline_error, "offline missing package")
        check(offline_error.returncode == 2 and find_records(offline_records, "error")[0]["code"] == "missing_import",
              "offline missing package did not fail as an input error")
        offline_message = find_records(offline_records, "error")[0]["message"]
        check("example.invalid" not in offline_message and str(temp) not in offline_message,
              "offline package error exposed its URL or temporary host path")
        check(not (temp / "goose-home" / "pkg").exists(), "offline lint created a package cache directory")

        valid_facts = temp / "valid-facts.jsonl"
        valid_facts.write_text(minimal_facts())
        valid_output = temp / "valid-companion-output.jsonl"
        valid_result = subprocess.run([
            str(companion), "--facts", str(valid_facts), "--output", str(valid_output),
            "--entry", "synthetic.goose", "--revision", "test", "--profile", "O1", "--format", "jsonl",
        ], cwd=ROOT, env=env, text=True, capture_output=True)
        valid_records = [json.loads(line) for line in valid_output.read_text().splitlines()]
        check(valid_result.returncode == 0 and valid_records[-1]["exit_status"] == 0,
              "valid versioned facts did not pass companion validation")

        corrupt_facts = temp / "corrupt-facts.jsonl"
        damaged = minimal_facts().splitlines()
        terminal = json.loads(damaged[-1])
        terminal["integrity"] = terminal["integrity"][:-1] + ("0" if terminal["integrity"][-1] != "0" else "1")
        damaged[-1] = json.dumps(terminal, separators=(",", ":"))
        corrupt_facts.write_text("\n".join(damaged) + "\n")
        corrupt_output = temp / "companion-output.jsonl"
        companion_error = subprocess.run([
            str(companion), "--facts", str(corrupt_facts), "--output", str(corrupt_output),
            "--entry", "test/lint/rules.goose", "--revision", "test", "--profile", "O1", "--format", "jsonl",
        ], cwd=ROOT, env=env, text=True, capture_output=True)
        companion_records = [json.loads(line) for line in corrupt_output.read_text().splitlines()]
        check(companion_error.returncode == 4 and find_records(companion_records, "error")[0]["code"] == "tool_failure",
              "corrupt facts were not rejected as a tool failure")

        def expect_fact_failure(label, fact_text):
            facts_path = temp / f"{label}-facts.jsonl"
            output_path = temp / f"{label}-output.jsonl"
            facts_path.write_text(fact_text)
            result = subprocess.run([
                str(companion), "--facts", str(facts_path), "--output", str(output_path),
                "--entry", "synthetic.goose", "--revision", "test", "--profile", "O1", "--format", "jsonl",
            ], cwd=ROOT, env=env, text=True, capture_output=True)
            records = [json.loads(line) for line in output_path.read_text().splitlines()]
            check(result.returncode == 4 and find_records(records, "error")[0]["code"] == "tool_failure",
                  f"{label} facts did not fail closed")

        wrong_version = minimal_fact_records()
        wrong_version[0]["facts_version"] = 2
        expect_fact_failure("wrong-version", encode_facts(wrong_version))

        duplicate_source = minimal_fact_records()
        duplicate_source.insert(2, dict(duplicate_source[1]))
        expect_fact_failure("duplicate-source-id", encode_facts(duplicate_source))

        truncated = "\n".join(minimal_facts().splitlines()[:-1]) + "\n"
        expect_fact_failure("truncated-stream", truncated)

        oversized_path = temp / "oversized-record-facts.jsonl"
        oversized_output = temp / "oversized-record-output.jsonl"
        prefix = minimal_fact_records()[:2]
        with oversized_path.open("wb") as stream:
            for record in prefix:
                stream.write(json.dumps(record, separators=(",", ":")).encode() + b"\n")
            stream.write(b'{"kind":"unknown","payload":"' + b"x" * (16 * 1024 * 1024) + b'"}\n')
        oversized_result = subprocess.run([
            str(companion), "--facts", str(oversized_path), "--output", str(oversized_output),
            "--entry", "synthetic.goose", "--revision", "test", "--profile", "O1", "--format", "jsonl",
        ], cwd=ROOT, env=env, text=True, capture_output=True)
        oversized_records = [json.loads(line) for line in oversized_output.read_text().splitlines()]
        check(oversized_result.returncode == 4 and
              find_records(oversized_records, "error")[0]["code"] == "tool_failure",
              "oversized facts record was not rejected as a tool failure")

        missing_companion_dir = temp / "without-companion"
        missing_companion_dir.mkdir()
        missing_companion_goose = missing_companion_dir / goose.name
        shutil.copy2(goose, missing_companion_goose)
        missing_companion = run_lint(missing_companion_goose, fixture, "--format", "jsonl", env=env)
        missing_companion_records = parse_jsonl(missing_companion, "missing companion")
        check(missing_companion.returncode == 4 and find_records(missing_companion_records, "error")[0]["code"] == "tool_failure",
              "missing companion produced a successful result")

        # The linter's own Goose source must typecheck and pass its defaults.
        self_lint = run_lint(
            goose, ROOT / "tools/lint/main.goose", "--format", "jsonl",
            "--deny", "redundant_cast", "--deny", "redundant_reference_marker",
            "--deny", "avoidable_reference_copy", "--deny", "discarded_failure",
            "--deny", "unchecked_poll_result", "--deny", "unused_pure_value",
            "--deny", "stale_suppression", env=env,
        )
        self_records = parse_jsonl(self_lint, "self lint")
        check(self_lint.returncode == 0 and not find_records(self_records, "diagnostic"),
              "the linter does not pass its own default rules")

    print("PASS: Goose lint CLI, rules, coverage, suppressions, baselines, offline mode, and failure statuses")


if __name__ == "__main__":
    main()
