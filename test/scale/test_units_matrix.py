import contextlib
import io
import tempfile
import unittest
from pathlib import Path
import sys
from types import SimpleNamespace
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parent))
import units_matrix


ROOT = Path(__file__).resolve().parents[2]


class UnitsMatrixTests(unittest.TestCase):
    def setUp(self):
        self.scratch = ROOT / ".work" / "tmp"
        self.scratch.mkdir(parents=True, exist_ok=True)

    def test_clean_equivalence_compares_stdout(self):
        matrix = units_matrix.Matrix("unused", self.scratch)
        clean = SimpleNamespace(exit=0, stdout="clean\n", stderr="",
                                exe=self.scratch / "clean.exe",
                                home=self.scratch / "clean-home")
        session = SimpleNamespace(home=self.scratch / "home", dir=self.scratch,
                                  clean=lambda *args, **kwargs: clean)
        incremental = SimpleNamespace(exit=0, stdout="incremental\n", stderr="",
                                      exe=self.scratch / "incremental.exe",
                                      runtime_cache_snapshot=None)

        with contextlib.redirect_stdout(io.StringIO()):
            matrix.equal_to_clean("stdout", session, incremental)

        self.assertEqual(len(matrix.failures), 1)
        self.assertIn("stdout differs", matrix.failures[0])

    def test_clean_equivalence_normalizes_executable_paths(self):
        matrix = units_matrix.Matrix("unused", self.scratch)
        directory = self.scratch / "program"
        incremental_exe = directory / "prog.exe"
        clean_exe = directory / "clean0.exe"
        clean = SimpleNamespace(exit=1, stdout=f"built {clean_exe}\n", stderr="",
                                exe=clean_exe, home=self.scratch / "clean-home")
        session = SimpleNamespace(home=self.scratch / "home", dir=directory,
                                  clean=lambda *args, **kwargs: clean)
        incremental = SimpleNamespace(exit=1, stdout=f"built {incremental_exe}\n", stderr="",
                                      exe=incremental_exe, runtime_cache_snapshot=None)

        matrix.equal_to_clean("executable path", session, incremental)

        self.assertEqual(matrix.failures, [])

    def test_warm_contract_store_allows_verified_frontend_recheck(self):
        native = {"no_op": False, "frontend_phases": ["parse"],
                  "native_compiler_invocations": [], "objects_missed": 0,
                  "link": {"ran": False}}

        self.assertTrue(units_matrix.Matrix.is_warm(native))

    def test_unavailable_contract_dimensions_make_matrix_incomplete(self):
        matrix = units_matrix.Matrix("unused", self.scratch)
        with contextlib.redirect_stdout(io.StringIO()):
            matrix.record_unavailable("E10", {"target": "no target option"})

        record = matrix.records[0]
        self.assertEqual(record["status"], "unavailable")
        self.assertNotIn("ok", record)
        self.assertEqual(matrix.completion(), ("incomplete", 2))

    def test_random_non_error_build_failure_is_reported_for_edits_and_warning(self):
        class SequenceRng:
            def __init__(self, seed, edit):
                self.edit = edit

            def choice(self, options):
                return self.edit if "E02" in options else "edit"

        class FakeBuild:
            def __init__(self, exit_code):
                self.exit = exit_code
                self.stderr = units_matrix.edits.EDITS["E15b"].message
                self.stdout = ""
                self.native = {}

            def record(self, row):
                return {"row": row, "exit": self.exit}

        class FakeSession:
            def __init__(self, goose, work, name):
                self.edit = None
                self.calls = 0

            def build(self, *flags, **kwargs):
                self.calls += 1
                return FakeBuild(0 if self.calls == 1 else 1)

            def write(self, edit):
                self.edit = edit

        for edit in ("E02", "E15b"):
            with self.subTest(edit=edit):
                matrix = units_matrix.Matrix("unused", self.scratch)
                with patch.object(units_matrix, "Session", FakeSession), \
                        patch.object(units_matrix.random, "Random",
                                     lambda seed: SequenceRng(seed, edit)), \
                        patch.object(units_matrix.Matrix, "equal_to_clean", lambda *args, **kwargs: None), \
                        contextlib.redirect_stdout(io.StringIO()):
                    matrix.random_sequence(1, seed=1)

                self.assertEqual(len(matrix.failures), 1)
                self.assertIn("unexpected build failure", matrix.failures[0])

    def test_random_sequence_forces_reuse_verification(self):
        class FixedRandom:
            def choice(self, options):
                return "nothing"

        class FakeBuild:
            exit = 0
            stdout = ""
            stderr = ""
            native = {}

            def record(self, row):
                return {"row": row, "exit": self.exit}

        class FakeSession:
            verification = []

            def __init__(self, goose, work, name):
                self.edit = None
                type(self).verification = []

            def build(self, *flags, verify=False):
                type(self).verification.append(verify)
                return FakeBuild()

        matrix = units_matrix.Matrix("unused", self.scratch)
        with patch.object(units_matrix, "Session", FakeSession), \
                patch.object(units_matrix.random, "Random", lambda seed: FixedRandom()), \
                patch.object(units_matrix.Matrix, "equal_to_clean", lambda *args, **kwargs: None), \
                contextlib.redirect_stdout(io.StringIO()):
            matrix.random_sequence(1, seed=1)

        self.assertEqual(matrix.failures, [])
        self.assertEqual(FakeSession.verification, [True, True])

    def test_build_kills_only_after_predicate(self):
        with tempfile.TemporaryDirectory(dir=self.scratch) as temp:
            directory = Path(temp)
            marker = directory / "started"
            goose = directory / "fake-goose"
            goose.write_text("#!/bin/sh\n: > \"$MARKER\"\nexec sleep 30\n", encoding="utf-8")
            goose.chmod(0o755)
            session = SimpleNamespace(dir=directory, home=directory / "home", goose=str(goose))

            build = units_matrix.Build(session, [], "interrupted", env_overrides={
                "MARKER": str(marker),
            }, kill_when=marker.exists, kill_timeout=2)

            self.assertTrue(build.killed)
            self.assertNotEqual(build.exit, 0)

    def test_e16_fails_when_intermediate_edit_build_fails(self):
        with tempfile.TemporaryDirectory(dir=self.scratch) as temp:
            directory = Path(temp)

            class FakeBuild:
                def __init__(self, store, exit_code):
                    self.store = store
                    self.exit = exit_code
                    self.stderr = "intermediate failed" if exit_code else ""
                    self.stdout = ""
                    self.native = {}

                def record(self, row):
                    return {"row": row, "exit": self.exit}

            class FakeSession:
                def __init__(self, goose, work, name):
                    self.dir = directory / name
                    self.dir.mkdir()
                    self.home = self.dir / "home"
                    self.calls = 0
                    self.edit = None
                    store = self.dir / "store"
                    (store / "units").mkdir(parents=True)
                    (store / "units" / "main.c").write_bytes(b"initial")
                    self.store = store

                def build(self):
                    self.calls += 1
                    return FakeBuild(self.store, 0 if self.calls == 1 else 1)

                def write(self, edit):
                    self.edit = edit

            matrix = units_matrix.Matrix("unused", directory)
            with patch.object(units_matrix, "Session", FakeSession), \
                    contextlib.redirect_stdout(io.StringIO()):
                matrix.row_E16()

            self.assertEqual(len(matrix.failures), 1)
            self.assertIn("E16 edit", matrix.failures[0])

    def test_edit_error_is_compared_with_a_clean_build(self):
        class FakeBuild:
            def __init__(self, exit_code, stderr="", no_op=False, store=None, exe=None,
                         runtime_cache_snapshot=None):
                self.exit = exit_code
                self.stdout = ""
                self.stderr = stderr
                self.native = {"no_op": no_op}
                self.store = store
                self.exe = exe
                self.home = None
                self.runtime_cache_snapshot = runtime_cache_snapshot

            def record(self, row):
                return {"row": row, "exit": self.exit}

        class FakeSession:
            instances = []

            def __init__(self, goose, work, name):
                self.calls = 0
                self.clean_calls = []
                self.dir = work / "program"
                units_matrix.shutil.rmtree(self.dir, ignore_errors=True)
                self.dir.mkdir(parents=True)
                self.home = work / "home"
                self.output = None
                type(self).instances.append(self)

            def build(self, *args, **kwargs):
                self.calls += 1
                snapshot = None
                if self.calls > 1:
                    snapshot = self.dir / f"runtime-cache-before-{self.calls}"
                    snapshot.mkdir()
                if self.calls == 2:
                    return FakeBuild(1, stderr=units_matrix.edits.EDITS["E15a"].message,
                                     runtime_cache_snapshot=snapshot)
                return FakeBuild(0, no_op=self.calls == 3,
                                 store=self.dir / "store", exe=self.dir / "prog.exe",
                                 runtime_cache_snapshot=snapshot)

            def write(self, edit):
                self.edit = edit

            def clean(self, *flags, runtime_snapshot=None, **kwargs):
                self.clean_calls.append(runtime_snapshot)
                if len(self.clean_calls) == 1:
                    return FakeBuild(1, stderr="different clean diagnostic")
                return FakeBuild(0, store=self.dir / "clean-store", exe=self.dir / "clean.exe")

            def run(self, exe):
                return 0, "", ""

        matrix = units_matrix.Matrix("unused", self.scratch)
        with patch.object(units_matrix, "Session", FakeSession), \
                contextlib.redirect_stdout(io.StringIO()):
            matrix.edit_row("E15a", "E15a", lambda *args: None)

        self.assertEqual(len(matrix.failures), 1)
        self.assertIn("diagnostics differ", matrix.failures[0])
        self.assertEqual(FakeSession.instances[-1].clean_calls, [
            self.scratch / "program" / "runtime-cache-before-2",
            self.scratch / "program" / "runtime-cache-before-3",
        ])

    def test_edit_case_selection_runs_only_requested_failure_rows(self):
        matrix = units_matrix.Matrix("unused", self.scratch)
        called = []
        with patch.object(matrix, "edit_row", lambda row, edit, check: called.append(row)), \
                patch.object(matrix, "row_E16", lambda: called.append("E16")), \
                patch.object(matrix, "ok_build", lambda row, build: False), \
                patch.object(units_matrix, "Session", lambda *args: SimpleNamespace(build=lambda: object())), \
                contextlib.redirect_stdout(io.StringIO()):
            matrix.run_all({"E15a", "E07c"})

        self.assertEqual(called, ["E07c", "E15a"])

    def test_warning_warm_build_must_succeed(self):
        matrix, _ = self.run_warning_case(1)

        self.assertEqual(len(matrix.failures), 1)
        self.assertIn("E15b warm: build failed", matrix.failures[0])

    def test_warning_warm_build_is_compared_with_clean(self):
        matrix, compared = self.run_warning_case(0)

        self.assertEqual(matrix.failures, [])
        self.assertEqual(compared, ["edit", "warm"])

    def run_warning_case(self, warm_exit):
        warning = units_matrix.edits.EDITS["E15b"].message
        compared = []

        class FakeBuild:
            def __init__(self, label, scratch, exit_code=0):
                self.label = label
                self.exit = exit_code
                self.stdout = ""
                self.stderr = warning if label != "initial" else ""
                self.native = {"native_compiler_invocations": [], "link": {"ran": False}}
                self.store = scratch / f"{label}-store"
                self.exe = scratch / f"{label}.exe"
                self.runtime_cache_snapshot = None

            def record(self, row):
                return {"row": row, "exit": self.exit}

        class FakeSession:
            def __init__(self, goose, work, name):
                self.scratch = work
                self.output = None
                self.calls = 0
                self.edit = None

            def build(self, *args, **kwargs):
                self.calls += 1
                if self.calls == 1:
                    return FakeBuild("initial", self.scratch)
                if self.calls == 2:
                    return FakeBuild("edit", self.scratch)
                return FakeBuild("warm", self.scratch, warm_exit)

            def write(self, edit):
                self.edit = edit

        matrix = units_matrix.Matrix("unused", self.scratch)

        def compare(self, row, session, build, *args, **kwargs):
            compared.append(build.label)

        with patch.object(units_matrix, "Session", FakeSession), \
                patch.object(units_matrix, "units_of", lambda store: {"main.c": b"same"}), \
                patch.object(units_matrix.Matrix, "equal_to_clean", compare), \
                contextlib.redirect_stdout(io.StringIO()):
            matrix.edit_row("E15b", "E15b", lambda *args: None)

        return matrix, compared


if __name__ == "__main__":
    unittest.main()
