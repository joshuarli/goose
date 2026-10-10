import os
from pathlib import Path
import signal
import sys
import tempfile
import time
import unittest
from unittest import mock

from fuzz.process import run


@unittest.skipUnless(sys.platform == "linux", "runner requires Linux")
class ProcessTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)

    def run_python(self, program, **kwargs):
        return run(
            [sys.executable, "-c", program],
            cwd=self.directory.name,
            timeout=kwargs.pop("timeout", 2.0),
            output_limit=kwargs.pop("output_limit", 1024),
            **kwargs,
        )

    def assert_reaped(self, pid):
        self.assertFalse(Path(f"/proc/{pid}").exists(), f"process {pid} remains")

    def test_timeout_kills_and_reaps_descendant(self):
        result = self.run_python(
            "import os,time; pid=os.fork(); "
            "print(pid if pid else os.getpid(), flush=True); time.sleep(30)",
            timeout=0.2,
        )
        self.assertEqual(result.limit, "timeout")
        self.assertEqual(result.returncode, -signal.SIGKILL)
        for pid in result.stdout.splitlines():
            self.assert_reaped(int(pid))

    def test_success_reaps_descendant_with_open_pipes(self):
        result = self.run_python(
            "import os,time; pid=os.fork(); "
            "print(pid, flush=True) if pid else time.sleep(30)"
        )
        self.assertEqual(result.returncode, 0)
        self.assertIsNone(result.limit)
        self.assertLess(result.elapsed, 1.0)
        self.assert_reaped(int(result.stdout))

    def test_output_limit_bounds_combined_streams_and_reaps_descendant(self):
        result = self.run_python(
            "import os,time; pid=os.fork(); "
            "print(pid, flush=True) if pid else time.sleep(30); "
            "os.write(2,b'e'*1000000) if pid else None; "
            "time.sleep(30)",
            output_limit=100,
        )
        self.assertEqual(result.limit, "output")
        self.assertEqual(len(result.stdout) + len(result.stderr), 100)
        self.assert_reaped(int(result.stdout))

    def test_stream_separation_and_nonzero_status(self):
        result = self.run_python(
            "import os; os.write(1,b'out\\x00'); os.write(2,b'err'); raise SystemExit(7)"
        )
        self.assertEqual(result.stdout, b"out\x00")
        self.assertEqual(result.stderr, b"err")
        self.assertEqual(result.returncode, 7)
        self.assertIsNone(result.limit)

    def test_signal_status(self):
        result = self.run_python("import os,signal; os.kill(os.getpid(),signal.SIGTERM)")
        self.assertEqual(result.returncode, -signal.SIGTERM)
        self.assertIsNone(result.limit)

    def test_clean_environment_and_explicit_override(self):
        os.environ["FUZZ_PROCESS_TEST_SECRET"] = "secret"
        self.addCleanup(os.environ.pop, "FUZZ_PROCESS_TEST_SECRET")
        result = self.run_python(
            "import os; print(os.getenv('FUZZ_PROCESS_TEST_SECRET')); "
            "print(os.environ['ASAN_OPTIONS'])",
            env={"ASAN_OPTIONS": "detect_leaks=0"},
        )
        self.assertEqual(result.stdout, b"None\ndetect_leaks=0\n")

    def test_result_is_json_serializable(self):
        import base64
        import json

        result = self.run_python("import os; os.write(1,b'\\xff')")
        data = json.loads(json.dumps(result.to_dict()))
        self.assertEqual(base64.b64decode(data["stdout_b64"]), b"\xff")

    def test_interrupt_kills_and_reaps_group(self):
        pid_path = Path(self.directory.name) / "pids"

        def interrupt(process, deadline, output_limit, cleanup):
            until = time.monotonic() + 2
            while not pid_path.exists():
                if time.monotonic() >= until:
                    self.fail("child did not start")
                time.sleep(0.005)
            raise KeyboardInterrupt

        with mock.patch("fuzz.process._capture", side_effect=interrupt):
            with self.assertRaises(KeyboardInterrupt):
                self.run_python(
                    "import os,time,pathlib; pid=os.fork(); "
                    "pathlib.Path('pids').write_text(f'{os.getpid()} {pid}') if pid else None; "
                    "time.sleep(30)"
                )
        for pid in pid_path.read_text().split():
            self.assert_reaped(int(pid))

    def test_closed_pipes_still_obey_timeout(self):
        result = self.run_python("import os,time; os.close(1); os.close(2); time.sleep(30)", timeout=0.1)
        self.assertEqual(result.limit, "timeout")
        self.assertEqual(result.returncode, -signal.SIGKILL)

    def test_stack_limit_is_inherited(self):
        import resource

        expected = repr(resource.getrlimit(resource.RLIMIT_STACK)).encode("ascii") + b"\n"
        result = self.run_python("import resource; print(resource.getrlimit(resource.RLIMIT_STACK))")
        self.assertEqual(result.stdout, expected)


if __name__ == "__main__":
    unittest.main()
