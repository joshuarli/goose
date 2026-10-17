#!/usr/bin/env python3
import argparse
from contextlib import contextmanager
from dataclasses import dataclass
import os
from pathlib import Path
import re
import shlex
import signal
import subprocess
import sys
import tempfile
import time


MODULE_PART = r"[A-Za-z_][A-Za-z0-9_']*"
MODULE_NAME = re.compile(rf"{MODULE_PART}(?:\.{MODULE_PART})*")
IMPORT_LINE = re.compile(r"^\s*import(?:\s+|$)(.*)$")
WEAK_LEAN_ARGS = 'weakLeanArgs = ["-j1", "-M4096"]\n'
TERMINATION_GRACE_SECONDS = 0.5
CANCELLATION_SIGNALS = (signal.SIGINT, signal.SIGTERM)


class VerificationError(Exception):
    pass


class BuildFailure(VerificationError):
    def __init__(self, module, returncode):
        self.module = module
        self.returncode = returncode
        super().__init__(f"Lake failed building {module}: exit status {returncode}")


class SignalCancellation(Exception):
    def __init__(self, signum):
        self.signum = signum
        super().__init__(f"cancelled by signal {signum}")


class ProcessCleanupFailure(Exception):
    pass


@dataclass(frozen=True)
class Build:
    module: str
    selector: str
    command: tuple[str, ...]


def _signal_handler(signum, frame):
    raise SignalCancellation(signum)


@contextmanager
def cancellation_handlers():
    original = {signum: signal.getsignal(signum) for signum in CANCELLATION_SIGNALS}
    try:
        for signum in CANCELLATION_SIGNALS:
            signal.signal(signum, _signal_handler)
        yield
    finally:
        for signum, handler in original.items():
            signal.signal(signum, handler)


def module_source(semantics_root, module):
    if not MODULE_NAME.fullmatch(module):
        raise VerificationError(f"invalid Lean module name: {module!r}")
    semantics_root = Path(semantics_root).resolve()
    source = semantics_root.joinpath(*module.split(".")).with_suffix(".lean").resolve()
    if not source.is_relative_to(semantics_root):
        raise VerificationError(f"module source escapes semantics root: {module} ({source})")
    return source


def imports_in(source):
    imports = []
    depth = 0
    for line_number, original_line in enumerate(source.read_text(encoding="utf-8").splitlines(), 1):
        line = []
        index = 0
        while index < len(original_line):
            if depth:
                if original_line.startswith("/-", index):
                    depth += 1
                    index += 2
                elif original_line.startswith("-/", index):
                    depth -= 1
                    index += 2
                else:
                    index += 1
            elif original_line.startswith("--", index):
                break
            elif original_line.startswith("/-", index):
                depth = 1
                index += 2
            else:
                line.append(original_line[index])
                index += 1
        line = "".join(line)
        match = IMPORT_LINE.match(line)
        if not match:
            continue
        imported = match.group(1).split()
        if not imported:
            raise VerificationError(f"empty import in {source}:{line_number}")
        for module in imported:
            if not MODULE_NAME.fullmatch(module):
                raise VerificationError(f"invalid import {module!r} in {source}:{line_number}")
            imports.append(module)
    return imports


def dependency_order(semantics_root, roots):
    semantics_root = Path(semantics_root).resolve()
    ordered = []
    visited = set()
    visiting = []

    def visit(module, importer=None):
        source = module_source(semantics_root, module)
        if not source.is_file():
            if importer is None:
                raise VerificationError(f"module root does not exist: {module} ({source})")
            raise VerificationError(f"unresolved import {module} in {importer}")
        if module in visited:
            return
        if module in visiting:
            cycle = " -> ".join([*visiting[visiting.index(module):], module])
            raise VerificationError(f"cyclic project imports: {cycle}")
        visiting.append(module)
        try:
            for imported in imports_in(source):
                if imported == "Goose" or imported.startswith("Goose."):
                    visit(imported, source)
        finally:
            visiting.pop()
        visited.add(module)
        ordered.append(module)

    for root in roots:
        visit(root)
    return ordered


def lakefile_with_lean_args(contents):
    lines = contents.splitlines(keepends=True)
    first_table = next(
        (index for index, line in enumerate(lines) if re.match(r"\s*\[", line)),
        len(lines),
    )
    setting = re.compile(r"^[ \t]*weakLeanArgs[ \t]*=")
    existing = next(
        (index for index, line in enumerate(lines[:first_table]) if setting.match(line)),
        None,
    )
    if existing is not None:
        lines[existing] = WEAK_LEAN_ARGS
    else:
        insert_at = first_table
        if insert_at and not lines[insert_at - 1].strip():
            insert_at -= 1
        lines.insert(insert_at, WEAK_LEAN_ARGS)
    return "".join(lines)


@contextmanager
def scratch_lakefile(semantics_root):
    repo_root = semantics_root.parent.resolve()
    work_root = repo_root / ".work"
    scratch_root = repo_root / ".work" / "tmp"
    if work_root.is_symlink() or scratch_root.is_symlink():
        raise VerificationError(f"scratch directory must not be a symlink: {scratch_root}")
    scratch_root.mkdir(parents=True, exist_ok=True)
    if not scratch_root.resolve().is_relative_to(repo_root):
        raise VerificationError(f"scratch directory escapes repository root: {scratch_root}")
    source = semantics_root / "lakefile.toml"
    if not source.is_file():
        raise VerificationError(f"Lake config does not exist: {source}")
    contents = lakefile_with_lean_args(source.read_text(encoding="utf-8"))
    descriptor, path = tempfile.mkstemp(prefix="verify-closure-", suffix=".toml", dir=scratch_root)
    lakefile = Path(path)
    try:
        with os.fdopen(descriptor, "w", encoding="utf-8") as output:
            output.write(contents)
        yield lakefile
    finally:
        lakefile.unlink(missing_ok=True)


def make_builds(semantics_root, lakefile, modules):
    builds = []
    for module in modules:
        selector = f"+{module}:olean"
        command = (
            "lake",
            "--dir",
            str(semantics_root),
            "--file",
            str(lakefile.resolve()),
            "--rehash",
            "--verbose",
            "build",
            selector,
        )
        builds.append(Build(module, selector, command))
    return builds


def _signal_group(process, signum, kill_group):
    try:
        kill_group(process.pid, signum)
    except ProcessLookupError:
        return None
    except OSError as error:
        return error
    return None


def terminate_process_group(process, kill_group=None, pause=None):
    kill_group = os.killpg if kill_group is None else kill_group
    pause = time.sleep if pause is None else pause
    previous_mask = signal.pthread_sigmask(signal.SIG_BLOCK, CANCELLATION_SIGNALS)
    failures = []
    try:
        term_error = _signal_group(process, signal.SIGTERM, kill_group)
        if term_error is not None:
            failures.append(f"SIGTERM failed: {term_error}")
        try:
            pause(TERMINATION_GRACE_SECONDS)
        except BaseException as error:
            failures.append(f"termination wait failed: {error}")
        kill_error = _signal_group(process, signal.SIGKILL, kill_group)
        if kill_error is not None:
            failures.append(f"SIGKILL failed: {kill_error}")
        try:
            process.wait()
        except BaseException as error:
            failures.append(f"waiting for Lake failed: {error}")
    finally:
        signal.pthread_sigmask(signal.SIG_SETMASK, previous_mask)
    if failures:
        raise ProcessCleanupFailure("; ".join(failures))


def run_build(build, semantics_root, environment, popen=None, kill_group=None, pause=None):
    popen = subprocess.Popen if popen is None else popen
    process = None
    try:
        previous_mask = signal.pthread_sigmask(signal.SIG_BLOCK, CANCELLATION_SIGNALS)
        try:
            process = popen(
                build.command,
                cwd=semantics_root,
                env=environment,
                start_new_session=True,
                stderr=subprocess.STDOUT,
            )
        finally:
            signal.pthread_sigmask(signal.SIG_SETMASK, previous_mask)
        returncode = process.wait()
    except BaseException:
        if process is not None:
            try:
                terminate_process_group(process, kill_group, pause)
            except BaseException as cleanup_error:
                print(f"Lake cleanup failed: {cleanup_error}", file=sys.stderr, flush=True)
        raise
    if returncode:
        raise BuildFailure(build.module, returncode)


def verify(semantics_root, roots, popen=None, kill_group=None, pause=None):
    semantics_root = Path(semantics_root).resolve()
    modules = dependency_order(semantics_root, roots)
    environment = os.environ.copy()
    environment["TMPDIR"] = str(semantics_root.parent / ".work" / "tmp")
    environment["LEAN_NUM_THREADS"] = "1"
    with scratch_lakefile(semantics_root) as lakefile:
        builds = make_builds(semantics_root, lakefile, modules)
        print(f"closure: {len(builds)} modules", flush=True)
        for index, build in enumerate(builds, 1):
            print(f"[{index}/{len(builds)}] {build.selector}", flush=True)
            print(f"$ {shlex.join(build.command)}", flush=True)
            run_build(build, semantics_root, environment, popen, kill_group, pause)
            print(f"built {build.selector}", flush=True)
        print("all module roots built", flush=True)


def main(argv=None):
    parser = argparse.ArgumentParser(
        description="Build exact sequential Lean module dependency closures."
    )
    parser.add_argument("--semantics-root", type=Path, required=True)
    parser.add_argument("--module", action="append", dest="modules", required=True)
    args = parser.parse_args(argv)
    try:
        with cancellation_handlers():
            verify(args.semantics_root, args.modules)
    except SignalCancellation as error:
        print(str(error), file=sys.stderr, flush=True)
        return 128 + error.signum
    except VerificationError as error:
        print(f"error: {error}", file=sys.stderr, flush=True)
        if isinstance(error, BuildFailure) and 0 < error.returncode < 256:
            return error.returncode
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
