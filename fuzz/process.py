"""Bounded compiler subprocesses with Linux process-group cleanup."""

import base64
from collections.abc import Callable, Mapping, Sequence
import ctypes
from dataclasses import dataclass
import math
import os
from pathlib import Path
import selectors
import signal
import subprocess
import sys
import threading
import time
from typing import Literal


@dataclass(frozen=True)
class Result:
    command: tuple[str, ...]
    returncode: int
    stdout: bytes
    stderr: bytes
    elapsed: float
    limit: Literal["timeout", "output"] | None

    def to_dict(self) -> dict[str, object]:
        return {
            "command": list(self.command),
            "returncode": self.returncode,
            "stdout_b64": base64.b64encode(self.stdout).decode("ascii"),
            "stderr_b64": base64.b64encode(self.stderr).decode("ascii"),
            "elapsed": self.elapsed,
            "limit": self.limit,
        }


_ENVIRONMENT_KEYS = frozenset(
    {
        "PATH", "TMPDIR", "LANG", "LC_ALL", "ASAN_OPTIONS", "UBSAN_OPTIONS",
        "MSAN_OPTIONS", "TSAN_OPTIONS", "LSAN_OPTIONS",
    }
)
# Subreaper state belongs to this Python process, so runner calls share one lock.
_RUN_LOCK = threading.Lock()


def _subreaper(enabled: int | None = None) -> int:
    library = ctypes.CDLL(None, use_errno=True)
    prctl = library.prctl
    prctl.argtypes = [ctypes.c_int, ctypes.c_ulong, ctypes.c_ulong, ctypes.c_ulong, ctypes.c_ulong]
    prctl.restype = ctypes.c_int
    state = ctypes.c_int()
    operation = 37 if enabled is None else 36
    argument = ctypes.addressof(state) if enabled is None else enabled
    if prctl(operation, argument, 0, 0, 0) == -1:
        error = ctypes.get_errno()
        raise OSError(error, os.strerror(error))
    return state.value


def _kill_and_reap(process: subprocess.Popen[bytes]) -> None:
    try:
        os.killpg(process.pid, signal.SIGKILL)
    except ProcessLookupError:
        pass
    process.wait()
    # Orphans become our children through subreaper adoption. Waiting by group
    # avoids consuming exit statuses from other subprocesses owned by callers.
    while True:
        try:
            os.waitpid(-process.pid, 0)
        except ChildProcessError:
            return


def _capture(
    process: subprocess.Popen[bytes], deadline: float, output_limit: int,
    cleanup: Callable[[], None],
) -> tuple[bytes, bytes, Literal["timeout", "output"] | None]:
    output = [bytearray(), bytearray()]
    total = 0
    limit: Literal["timeout", "output"] | None = None
    stopped = False
    with selectors.DefaultSelector() as selector:
        for index, stream in enumerate((process.stdout, process.stderr)):
            assert stream is not None
            os.set_blocking(stream.fileno(), False)
            selector.register(stream, selectors.EVENT_READ, index)
        while selector.get_map():
            if not stopped:
                if process.poll() is not None:
                    cleanup()
                    stopped = True
                elif time.monotonic() >= deadline:
                    limit = "timeout"
                    cleanup()
                    stopped = True
            remaining = max(0.0, deadline - time.monotonic())
            events = selector.select(0.01 if stopped else min(0.01, remaining))
            for key, _ in events:
                chunk = os.read(key.fileobj.fileno(), 65536)
                if not chunk:
                    selector.unregister(key.fileobj)
                    continue
                available = output_limit - total
                kept = chunk[:available]
                output[key.data].extend(kept)
                total += len(kept)
                if len(chunk) > available and limit is None:
                    limit = "output"
                    if not stopped:
                        cleanup()
                        stopped = True
        # A child can close both pipes and keep running, so EOF is not success.
        if not stopped:
            try:
                process.wait(timeout=max(0.0, deadline - time.monotonic()))
            except subprocess.TimeoutExpired:
                limit = "timeout"
            cleanup()
    return bytes(output[0]), bytes(output[1]), limit


def run(
    argv: Sequence[str],
    cwd: str | Path,
    timeout: float,
    output_limit: int,
    env: Mapping[str, str] | None = None,
) -> Result:
    """Run on Linux, retaining at most output_limit bytes across both streams.

    Descendants must remain in their inherited process group. Resource limits,
    including the compiler's stack allowance, are inherited without adjustment.
    Explicit environment entries are restricted to execution and sanitizer knobs.
    """
    if sys.platform != "linux" or os.name != "posix":
        raise RuntimeError("compiler subprocess runner requires Linux POSIX")
    if isinstance(argv, (str, bytes)) or not argv or any(not isinstance(arg, str) for arg in argv):
        raise ValueError("argv must be a nonempty sequence of strings")
    if not math.isfinite(timeout) or timeout <= 0:
        raise ValueError("timeout must be finite and positive")
    if isinstance(output_limit, bool) or not isinstance(output_limit, int) or output_limit < 0:
        raise ValueError("output_limit must be a nonnegative integer")
    environment = {"PATH": os.defpath, "TMPDIR": "/tmp", "LANG": "C", "LC_ALL": "C"}
    if env is not None:
        unknown = set(env) - _ENVIRONMENT_KEYS
        if unknown:
            raise ValueError(f"unsupported environment keys: {', '.join(sorted(unknown))}")
        environment.update(env)
    command = tuple(argv)
    with _RUN_LOCK:
        previous_subreaper = _subreaper()
        _subreaper(1)
        process = None
        cleaned = False

        def cleanup() -> None:
            nonlocal cleaned
            if process is not None and not cleaned:
                _kill_and_reap(process)
                cleaned = True

        started = time.monotonic()
        try:
            process = subprocess.Popen(
                command,
                cwd=cwd,
                env=environment,
                stdin=subprocess.DEVNULL,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                start_new_session=True,
            )
            stdout, stderr, limit = _capture(process, started + timeout, output_limit, cleanup)
            assert process.returncode is not None
            return Result(command, process.returncode, stdout, stderr, time.monotonic() - started, limit)
        finally:
            try:
                if process is not None:
                    cleanup()
                    if process.stdout is not None:
                        process.stdout.close()
                    if process.stderr is not None:
                        process.stderr.close()
            finally:
                _subreaper(previous_subreaper)
