"""A program's native C sources are rebuilt when one changes, and only then."""
import os
from pathlib import Path
import subprocess
import tempfile

import toolchain as tc


def check_native_rebuild(exe, base):
    base = Path(base).resolve()
    base.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="native-rebuild-", dir=base) as tmp:
        root = Path(tmp)
        env = dict(os.environ, GOOSE_HOME=str(root / "home"))
        source = root / "main.goose"
        impl = root / "impl.c"
        tc.write_text(source, "extern fn answer() -> i32;\nfn main() { print(answer()); }\n")
        tc.write_text(root / "main.build", 'c_sources = ["impl.c"];\n')
        program = root / ("main" + tc.EXE_SUFFIX)

        def build_and_run(value, what):
            tc.write_text(impl, f"int answer(void) {{ return {value}; }}\n")
            # Coarse file systems may give an edit the old time stamp; the
            # build must see a changed source, not guess from the clock tick.
            stat = impl.stat()
            os.utime(impl, ns=(stat.st_atime_ns, stat.st_mtime_ns + 2_000_000_000))
            return build(what)

        def build(what):
            built = subprocess.run([str(exe), "build", "-o", str(program), str(source)],
                                   cwd=root, env=env, capture_output=True, text=True,
                                   errors="replace", timeout=120)
            if built.returncode:
                raise RuntimeError(f"native rebuild: {what}: {built.stdout}{built.stderr}")
            ran = subprocess.run([str(program)], cwd=root, capture_output=True, text=True,
                                 timeout=30)
            return ran.stdout.strip()

        def objects():
            return list((root / "home").glob("build/prog/*/native/*/impl.o*"))

        def require(good, message):
            if not good:
                raise RuntimeError(f"native rebuild: {message}")

        out = build_and_run(1, "first build")
        require(out == "1", f"first build printed {out!r}, wanted '1'")
        (obj,) = objects()
        compiled = obj.stat().st_mtime_ns

        out = build("unchanged rebuild")
        require(out == "1" and obj.stat().st_mtime_ns == compiled,
                "an unchanged source was compiled again")

        out = build_and_run(2, "rebuild after an edit")
        require(out == "2", f"a rebuild after editing impl.c printed {out!r}, wanted '2'")
