import os
from pathlib import Path
import signal
import subprocess
import sys
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
        (self.semantics / "lean-toolchain").write_text(
            (REPO_ROOT / "semantics" / "lean-toolchain").read_text(encoding="utf-8"),
            encoding="utf-8",
        )
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

    def test_closure_uses_one_process_and_keeps_resource_limits(self):
        self.write_module("Goose.First")
        self.write_module("Goose.Second", "import Goose.First\n")
        source = self.semantics / "lakefile.toml"
        original = source.read_text(encoding="utf-8")
        processes = []

        def popen(command, **kwargs):
            processes.append((command, kwargs))
            self.assertTrue(Path(command[6]).is_file())
            self.assertIn('weakLeanArgs = ["-j1", "-M4096"]',
                          Path(command[6]).read_text(encoding="utf-8"))
            return FakeProcess([0])

        verify_closure.verify(self.semantics, ["Goose.Second"], popen=popen)

        self.assertEqual(len(processes), 1)
        command, options = processes[0]
        self.assertEqual(command[:4], ("lean", "-j1", "-M4096", "--run"))
        self.assertEqual(command[7:], ("Goose.First", "Goose.Second"))
        self.assertTrue(options["start_new_session"])
        self.assertEqual(options["env"]["LEAN_NUM_THREADS"], "1")
        self.assertEqual(options["env"]["TMPDIR"], str(self.project / ".work" / "tmp"))
        self.assertFalse(Path(command[6]).exists())
        self.assertEqual(source.read_text(encoding="utf-8"), original)

    def test_build_failure_preserves_exit_status_and_cleans_scratch(self):
        self.write_module("Goose.First")
        commands = []

        def popen(command, **kwargs):
            commands.append(command)
            self.assertTrue(Path(command[6]).is_file())
            return FakeProcess([23])

        with self.assertRaises(verify_closure.BuildFailure) as raised:
            verify_closure.verify(self.semantics, ["Goose.First"], popen=popen)

        self.assertEqual(raised.exception.returncode, 23)
        self.assertEqual(len(commands), 1)
        self.assertFalse(Path(commands[0][6]).exists())

    def run_verifier(self, *modules):
        command = [sys.executable, str(Path(verify_closure.__file__).resolve()),
                   "--semantics-root", str(self.semantics)]
        for module in modules:
            command.extend(["--module", module])
        return subprocess.run(command, text=True, stdout=subprocess.PIPE,
                              stderr=subprocess.STDOUT, timeout=60)

    def test_real_wrong_toolchain_stops_before_build(self):
        self.write_module("Goose.Root", "example : True := True.intro\n")
        (self.semantics / "lean-toolchain").write_text("leanprover/lean4:v0.0.0\n", encoding="utf-8")

        result = self.run_verifier("Goose.Root")

        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn("toolchain mismatch", result.stdout)
        self.assertNotIn("built +Goose.", result.stdout)

    def test_real_lake_rehashes_cached_imports_and_stops_at_first_failure(self):
        base = self.write_module("Goose.Base", "def value : Nat := 1\n")
        self.write_module("Goose.Left", "import Goose.Base\ndef left := value\n")
        self.write_module("Goose.Right", "import Goose.Base\ndef right := value\n")
        self.write_module("Goose.Root", "import Goose.Left\nimport Goose.Right\n"
                          "example : left = 1 := rfl\nexample : right = 1 := rfl\n")
        first = self.run_verifier("Goose.Root")
        self.assertEqual(first.returncode, 0, first.stdout)
        self.assertEqual(first.stdout.count("built +Goose."), 4, first.stdout)
        metadata = base.stat()
        base.write_text("def value : Nat := 2\n", encoding="utf-8")
        os.utime(base, ns=(metadata.st_atime_ns, metadata.st_mtime_ns))
        self.write_module("Goose.After", "example : True := True.intro\n")
        changed = self.run_verifier("Goose.Root", "Goose.After")
        self.assertNotEqual(changed.returncode, 0, changed.stdout)
        self.assertIn("Goose/Root.lean", changed.stdout)
        self.assertNotIn("built +Goose.Root", changed.stdout)
        self.assertNotIn("[5/5] +Goose.After:olean", changed.stdout)
        self.assertFalse((self.semantics / ".lake/build/lib/lean/Goose/After.olean").exists())

    def test_real_lake_compiles_serially_with_resource_limits(self):
        self.write_module("Goose.Base", "def value : Nat := 1\n")
        self.write_module("Goose.Left", "import Goose.Base\ndef left := value\n")
        self.write_module("Goose.Right", "import Goose.Base\ndef right := value\n")
        self.write_module("Goose.Root", "import Goose.Left\nimport Goose.Right\n"
                          "example : left = right := rfl\n")
        install = Path(subprocess.check_output(["lean", "--print-prefix"], text=True).strip())
        isolated = self.project / "toolchain"
        (isolated / "bin").mkdir(parents=True)
        for entry in ("lib", "include", "src"):
            (isolated / entry).symlink_to(install / entry, target_is_directory=True)
        for entry in (install / "bin").iterdir():
            if entry.name != "lean":
                (isolated / "bin" / entry.name).symlink_to(entry)
        lock = self.project / "active-compiler"
        compiled = self.project / "compiled"
        wrapper = isolated / "bin" / "lean"
        wrapper.write_text(
            f"#!{sys.executable}\n"
            "import os,subprocess,sys\n"
            f"lock = {str(lock)!r}\n"
            "compiling = '-o' in sys.argv[1:]\n"
            "if compiling:\n"
            "    descriptor = os.open(lock, os.O_CREAT | os.O_EXCL | os.O_WRONLY)\n"
            "    os.close(descriptor)\n"
            "    assert '-j1' in sys.argv and '-M4096' in sys.argv\n"
            "    assert os.environ['LEAN_NUM_THREADS'] == '1'\n"
            f"    with open({str(compiled)!r}, 'a') as output:\n"
            "        output.write(sys.argv[sys.argv.index('-o') + 1] + '\\n')\n"
            "try:\n"
            f"    raise SystemExit(subprocess.run([{str(install / 'bin/lean')!r}, *sys.argv[1:]]).returncode)\n"
            "finally:\n"
            "    if compiling:\n"
            "        os.unlink(lock)\n",
            encoding="utf-8",
        )
        wrapper.chmod(0o755)
        environment = os.environ.copy()
        environment.update(LEAN_SYSROOT=str(isolated), LAKE_OVERRIDE_LEAN="true")
        result = subprocess.run(
            [sys.executable, str(Path(verify_closure.__file__).resolve()),
             "--semantics-root", str(self.semantics), "--module", "Goose.Root"],
            env=environment, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            timeout=60,
        )
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertEqual([Path(path).stem for path in compiled.read_text().splitlines()],
                         ["Base", "Left", "Right", "Root"])
        self.assertFalse(lock.exists())

    def test_real_cancellation_kills_descendants_and_reaps_owned_process(self):
        child = "import os,signal; signal.signal(signal.SIGTERM, signal.SIG_IGN); print(os.getpid(), flush=True); signal.pause()"
        parent = ("import os,subprocess,sys; print(os.getpid(), flush=True); "
                  "subprocess.Popen([sys.executable, '-c', sys.argv[1]]).wait()")
        driver = self.project / "cancel.py"
        driver.write_text(
            "import signal,sys\n"
            f"sys.path.insert(0, {str(Path(verify_closure.__file__).parent)!r})\n"
            "import verify_closure as v\n"
            "build = v.Build('fixture', tuple(sys.argv[1:]))\n"
            "try:\n"
            "    with v.cancellation_handlers():\n"
            "        v.run_build(build, '.', None)\n"
            "except v.SignalCancellation as error:\n"
            "    raise SystemExit(128 + error.signum)\n",
            encoding="utf-8",
        )
        process = subprocess.Popen(
            [sys.executable, str(driver), sys.executable, "-c", parent, child],
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
        )
        group = None
        try:
            group = int(process.stdout.readline())
            descendant = int(process.stdout.readline())
            process.send_signal(signal.SIGTERM)
            _, stderr = process.communicate(timeout=10)
            self.assertEqual(process.returncode, 128 + signal.SIGTERM, stderr)
            with self.assertRaises(ProcessLookupError):
                os.kill(group, 0)
            state = subprocess.run(["ps", "-o", "stat=", "-p", str(descendant)],
                                   text=True, stdout=subprocess.PIPE, check=False)
            self.assertTrue(not state.stdout.strip() or state.stdout.lstrip().startswith("Z"),
                            state.stdout)
        finally:
            if process.poll() is None:
                process.kill()
                process.wait()
            if group is not None:
                try:
                    os.killpg(group, signal.SIGKILL)
                except ProcessLookupError:
                    pass

    def test_interruption_terms_kills_and_reaps_process_group(self):
        process = FakeProcess([KeyboardInterrupt(), -signal.SIGKILL])
        build = verify_closure.Build("Goose.Root", ("lake", "build"))
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
