import os
from pathlib import Path
import signal
import tempfile
import unittest

import verify_closure


REPO_ROOT = Path(__file__).resolve().parents[2]
SCRATCH_ROOT = REPO_ROOT / ".work" / "tmp"
SCRATCH_ROOT.mkdir(parents=True, exist_ok=True)


class FakeProcess:
    pid = 41234

    def __init__(self, outcomes):
        self.outcomes = iter(outcomes)
        self.wait_calls = 0

    def wait(self):
        self.wait_calls += 1
        outcome = next(self.outcomes)
        if isinstance(outcome, BaseException):
            raise outcome
        return outcome


class VerifyClosureTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(dir=SCRATCH_ROOT)
        self.project = Path(self.temporary.name)
        self.semantics = self.project / "semantics"
        self.semantics.mkdir()
        (self.semantics / "lakefile.toml").write_text(
            'name = "fixture"\n\n[[lean_lib]]\nname = "Goose"\n',
            encoding="utf-8",
        )

    def tearDown(self):
        self.temporary.cleanup()

    def write_module(self, module, contents=""):
        source = self.semantics.joinpath(*module.split(".")).with_suffix(".lean")
        source.parent.mkdir(parents=True, exist_ok=True)
        source.write_text(contents, encoding="utf-8")
        return source

    def test_dependency_order_is_postorder_and_deduplicated(self):
        self.write_module(
            "Goose.Root",
            "/-\nimport Goose.Missing\n/- nested -/\n-/\n"
            "import Std Goose.Left Goose.Right -- Goose.AlsoMissing\n",
        )
        self.write_module("Goose.Left", "import Goose.Shared\n")
        self.write_module("Goose.Right", "import Goose.Shared\n")
        self.write_module("Goose.Shared")

        self.assertEqual(
            verify_closure.dependency_order(self.semantics, ["Goose.Root"]),
            ["Goose.Shared", "Goose.Left", "Goose.Right", "Goose.Root"],
        )

    def test_unresolved_project_import_fails(self):
        self.write_module("Goose.Root", "import Goose.Missing\n")

        with self.assertRaisesRegex(verify_closure.VerificationError, "unresolved import Goose.Missing"):
            verify_closure.dependency_order(self.semantics, ["Goose.Root"])

    def test_missing_module_root_fails(self):
        with self.assertRaisesRegex(verify_closure.VerificationError, "module root does not exist"):
            verify_closure.dependency_order(self.semantics, ["Goose.Missing"])

    def test_module_root_rejects_path_components(self):
        with self.assertRaisesRegex(verify_closure.VerificationError, "invalid Lean module name"):
            verify_closure.dependency_order(self.semantics, ["../outside"])

    def test_module_symlink_cannot_escape_semantics_root(self):
        outside = self.project / "outside.lean"
        outside.write_text("", encoding="utf-8")
        module = self.semantics / "Goose" / "Outside.lean"
        module.parent.mkdir()
        module.symlink_to(outside)

        with self.assertRaisesRegex(verify_closure.VerificationError, "escapes semantics root"):
            verify_closure.dependency_order(self.semantics, ["Goose.Outside"])

    def test_lakefile_inserts_lean_args_before_first_table(self):
        contents = 'name = "fixture"\n\n[[lean_lib]]\nname = "Goose"\n'

        updated = verify_closure.lakefile_with_lean_args(contents)

        self.assertEqual(
            updated,
            'name = "fixture"\nweakLeanArgs = ["-j1", "-M4096"]\n'
            '\n[[lean_lib]]\nname = "Goose"\n',
        )

    def test_lakefile_replaces_existing_root_setting(self):
        contents = (
            'name = "fixture"\nweakLeanArgs = ["-j8"]\n'
            '[[lean_lib]]\nname = "Goose"\n'
        )

        updated = verify_closure.lakefile_with_lean_args(contents)

        self.assertEqual(updated.count("weakLeanArgs"), 1)
        self.assertIn('weakLeanArgs = ["-j1", "-M4096"]\n[[lean_lib]]', updated)

    def test_build_failure_stops_before_next_module(self):
        self.write_module("Goose.First")
        self.write_module("Goose.Second")
        lakefile_source = self.semantics / "lakefile.toml"
        original_lakefile = lakefile_source.read_text(encoding="utf-8")
        processes = []

        def popen(command, **kwargs):
            processes.append((command, kwargs))
            self.assertTrue(Path(command[4]).is_file())
            lakefile = Path(command[4]).read_text(encoding="utf-8")
            self.assertIn('weakLeanArgs = ["-j1", "-M4096"]', lakefile)
            self.assertEqual(kwargs["start_new_session"], True)
            return FakeProcess([23])

        with self.assertRaises(verify_closure.BuildFailure) as raised:
            verify_closure.verify(
                self.semantics,
                ["Goose.First", "Goose.Second"],
                popen=popen,
            )

        self.assertEqual(raised.exception.returncode, 23)
        self.assertEqual(len(processes), 1)
        self.assertEqual(
            processes[0][0][0:4],
            ("lake", "--dir", str(self.semantics.resolve()), "--file"),
        )
        self.assertEqual(processes[0][0][5:8], ("--rehash", "--verbose", "build"))
        self.assertEqual(processes[0][0][-1], "+Goose.First:olean")
        self.assertEqual(processes[0][1]["env"]["LEAN_NUM_THREADS"], "1")
        self.assertEqual(processes[0][1]["env"]["TMPDIR"], str(self.project / ".work" / "tmp"))
        self.assertFalse(Path(processes[0][0][4]).exists())
        self.assertEqual(lakefile_source.read_text(encoding="utf-8"), original_lakefile)

    def test_interruption_terms_kills_and_reaps_process_group(self):
        process = FakeProcess([KeyboardInterrupt(), -signal.SIGKILL])
        build = verify_closure.Build("Goose.Root", "+Goose.Root:olean", ("lake", "build"))
        events = []
        spawned = []

        def popen(command, **kwargs):
            spawned.append((command, kwargs))
            return process

        def kill_group(pid, signum):
            events.append(("signal", pid, signum))

        def pause(duration):
            events.append(("pause", duration))

        with self.assertRaises(KeyboardInterrupt):
            verify_closure.run_build(
                build,
                self.semantics,
                os.environ.copy(),
                popen=popen,
                kill_group=kill_group,
                pause=pause,
            )

        self.assertEqual(spawned[0][1]["start_new_session"], True)
        self.assertEqual(
            events,
            [
                ("signal", process.pid, signal.SIGTERM),
                ("pause", verify_closure.TERMINATION_GRACE_SECONDS),
                ("signal", process.pid, signal.SIGKILL),
            ],
        )
        self.assertEqual(process.wait_calls, 2)


if __name__ == "__main__":
    unittest.main()
