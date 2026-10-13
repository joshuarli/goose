import copy
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import report_check


ROOT = Path(__file__).resolve().parents[2]
SCRIPT = Path(report_check.__file__).resolve()
SCRATCH = ROOT / ".work" / "tmp"


def synthetic_report():
    causes = {"bounds_check_sites": 1, "inlined_calls": 1, "callee": 0, "other": 0}
    blocked_bytes = {"bounds_check_sites": 40, "inlined_calls": 60, "callee": 0, "other": 0}
    phase = {"wall_seconds": 0.0, "cpu_seconds": 0.0}
    return {
        "format": report_check.FORMAT,
        "input": {"mode": "emit", "optimization_level": 2},
        "counts": {
            "source_functions": 1,
            "checked_contexts": 2,
            "entry_reachable_contexts": 2,
            "live_instances": 2,
            "duplicate_contexts": {"count": 1, "same_key": 1},
            "generated_helpers": {},
            "type_declarations": {"bytes": 0},
            "literal_data": {"bytes": 0},
            "runtime_text": {"bytes": 0},
            "emitted_instances": {
                "bodies": 2,
                "element_run_twins": 0,
                "thread_entries": 0,
                "total": 2,
            },
        },
        "functions": [{
            "decl_key": "fn-1",
            "name": "f",
            "contexts": 2,
            "duplicate_contexts": 1,
            "live_instances": 2,
            "emitted_instances": 2,
            "emitted_bytes": 800,
            "implementations": 2,
            "dimensions": [],
            "self_check_seconds": 0.0,
        }],
        "dimensions": [],
        "output": {
            "c_bytes": 1000,
            "attributed": {
                "function_bodies": 800,
                "generated_helpers": 0,
                "type_declarations": 0,
                "literal_data": 0,
                "global_data": 0,
                "prototypes": 0,
                "extern_support": 0,
                "program_glue": 0,
                "compiler_defines": 0,
                "runtime_text": 0,
            },
            "unattributed_bytes": 200,
        },
        "phases": {
            "parse_and_resolve": phase,
            "check_and_specialize": phase,
            "optimize": phase,
            "bounds_check_elimination": phase,
            "code_generation": phase,
        },
        "total": {"wall_seconds": 0.0, "cpu_seconds": 0.0},
        "unattributed_seconds": {"wall": 0.0, "cpu": 0.0},
        "extensions": {
            "sharing": {
                "functions_before": 2,
                "functions_after": 2,
                "function_bytes_before": 900,
                "function_bytes_after": 800,
                "not_merged_same_declaration": causes,
                "not_merged_same_declaration_bytes": blocked_bytes,
            },
            "units": None,
            "native_compile": None,
        },
    }


class ReportCheckTests(unittest.TestCase):
    def setUp(self):
        SCRATCH.mkdir(parents=True, exist_ok=True)

    def run_cli(self, report, *args):
        with tempfile.TemporaryDirectory(dir=SCRATCH) as temp:
            report_path = Path(temp) / "report.json"
            report_path.write_text(json.dumps(report), encoding="utf-8")
            return subprocess.run(
                [sys.executable, str(SCRIPT), str(report_path), *args],
                cwd=ROOT,
                capture_output=True,
                text=True,
                check=False,
            )

    def test_sharing_blocker_bytes_are_bounded_by_emitted_function_bytes(self):
        report = synthetic_report()
        self.assertEqual(report_check.check(report, None), [])

        report["extensions"]["sharing"]["not_merged_same_declaration_bytes"]["other"] = 801
        problems = report_check.check(report, None)
        self.assertIn("sharing blocker bytes exceed function_bytes_after", problems)

    def test_cli_o2_threshold_and_legacy_opt_in_behavior(self):
        report = synthetic_report()
        result = self.run_cli(report, "--require-o2-sharing-threshold")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

        below_threshold = copy.deepcopy(report)
        below_threshold["extensions"]["sharing"]["not_merged_same_declaration_bytes"][
            "inlined_calls"] = 59
        result = self.run_cli(below_threshold, "--require-o2-sharing-threshold")
        self.assertEqual(result.returncode, 1)
        self.assertIn("context-dependent blocker bytes 99 / emitted C bytes 1000", result.stdout)
        self.assertIn("below the 10% threshold", result.stdout)

        wrong_level = copy.deepcopy(report)
        wrong_level["input"]["optimization_level"] = 1
        result = self.run_cli(wrong_level, "--require-o2-sharing-threshold")
        self.assertEqual(result.returncode, 1)
        self.assertIn("requires input.optimization_level == 2 (got 1)", result.stdout)

        legacy = copy.deepcopy(report)
        sharing = legacy["extensions"]["sharing"]
        del sharing["not_merged_same_declaration_bytes"]
        result = self.run_cli(legacy)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

        result = self.run_cli(legacy, "--require-o2-sharing-threshold")
        self.assertEqual(result.returncode, 1)
        self.assertIn(
            "O2 sharing threshold requires "
            "extensions.sharing.not_merged_same_declaration_bytes",
            result.stdout,
        )

    def test_o2_threshold_rejects_inconsistent_cli_report(self):
        report = synthetic_report()
        report["extensions"]["sharing"]["not_merged_same_declaration_bytes"]["other"] = 801
        result = self.run_cli(report, "--require-o2-sharing-threshold")
        self.assertEqual(result.returncode, 1)
        self.assertIn("blocker bytes exceeding function_bytes_after", result.stdout)


if __name__ == "__main__":
    unittest.main()
