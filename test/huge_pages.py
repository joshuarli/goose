import re
import selectors
import subprocess
import sys
import tempfile
from pathlib import Path

import toolchain as tc

ARENA_BYTES = 2 << 30

PROGRAM = """\
import os;

fn main() {
    print("ready");
    flush_stdout();
    var line: u8[>..] = [];
    read_line(line);
}
"""


def check_program(app):
    p = subprocess.Popen([str(app)], stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                         stderr=subprocess.PIPE)
    try:
        with selectors.DefaultSelector() as selector:
            selector.register(p.stdout, selectors.EVENT_READ)
            if not selector.select(60):
                raise RuntimeError("huge pages: program did not become ready")
            ready = p.stdout.readline()
        if b"ready" not in ready:
            raise RuntimeError(f"huge pages: the program said {ready!r}")
        smaps = Path(f"/proc/{p.pid}/smaps").read_text()
    finally:
        try:
            _, err = p.communicate(b"\n", timeout=60)
        except subprocess.TimeoutExpired:
            p.kill()
            p.communicate()
            raise
    if p.returncode:
        raise RuntimeError(f"huge pages: program exited {p.returncode}: {tc.decode(err)}")
    mappings = []
    for line in smaps.splitlines():
        header = re.match(r"^([0-9a-f]+)-([0-9a-f]+) (\S+) \S+ \S+ \d+\s*(.*)$", line)
        if header:
            lo, hi, access, name = header.groups()
            mappings.append((int(lo, 16), int(hi, 16), access, name, set()))
        elif line.startswith("VmFlags:"):
            mappings[-1][4].update(line.split()[1:])
    regions = 0
    for index, (lo, hi, access, name, _) in enumerate(mappings):
        if access != "---p" or name or hi - lo != 1 << 20:
            continue
        begin, end, segments = lo - ARENA_BYTES, lo, []
        for start, stop, access, name, flags in reversed(mappings[:index]):
            if stop != end or start < begin or access != "rw-p" or name:
                break
            end = start
            segments.append(flags)
            if end == begin:
                regions += 1
                if not all("nh" in flags for flags in segments):
                    raise RuntimeError("huge pages: a runtime arena is only partly marked nh")
                break
        if end != begin:
            raise RuntimeError("huge pages: incomplete configured runtime arena before guard")
    if not regions:
        raise RuntimeError("huge pages: no complete runtime arena with a protected guard")


def check_huge_pages(exe, base):
    """Returns why it was skipped, or None when the check ran; raises
    RuntimeError on a failure."""
    if not sys.platform.startswith("linux"):
        return "not Linux"
    if not Path("/sys/kernel/mm/transparent_hugepage").exists():
        return "no transparent huge pages"
    base = Path(base).resolve()
    base.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="huge-pages-", dir=base) as tmp:
        root = Path(tmp)
        source = root / "waits.goose"
        tc.write_text(source, PROGRAM)
        app = root / "waits"
        r = subprocess.run([str(exe), "build", "--stack-reserve", str(ARENA_BYTES),
                            "-o", str(app), str(source)], cwd=root,
                           capture_output=True, text=True, errors="replace", timeout=300)
        if r.returncode != 0:
            raise RuntimeError(f"huge pages: goose build:\n{r.stdout}{r.stderr}")
        check_program(app)
    return None
