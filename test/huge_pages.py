"""Check complete Linux data-stack reservations exclude transparent huge pages."""
import re
import subprocess
import sys
import tempfile
from pathlib import Path

import toolchain as tc

PROGRAM = """\
import os;

fn main() {
    print("ready");
    flush_stdout();
    var line: u8[>..] = [];
    read_line(line);
}
"""


def _check_arena_mappings(smaps):
    mappings = []
    for line in smaps.splitlines():
        header = re.match(r"^([0-9a-f]+)-([0-9a-f]+) (\S+) \S+ \S+ \d+\s*(.*)$", line)
        if header:
            lo, hi, access, name = header.groups()
            mappings.append((int(lo, 16), int(hi, 16), access, name, set()))
        elif line.startswith("VmFlags:"):
            mappings[-1][4].update(line.split()[1:])
        elif line.startswith("THPeligible:"):
            mappings[-1][4].add("THPeligible=" + line.split()[1])
    regions = 0
    for index, (lo, hi, access, name, _) in enumerate(mappings):
        if access != "---p" or name or hi - lo != 1 << 20:
            continue
        end, size, segments = lo, 0, []
        for start, stop, access, name, flags in reversed(mappings[:index]):
            if stop != end or access != "rw-p" or name:
                break
            end, size = start, size + stop - start
            segments.append(flags)
        if size >= 1 << 20 and size & (size - 1) == 0:
            regions += 1
            if not all("nh" in flags and "THPeligible=0" in flags for flags in segments):
                raise RuntimeError("huge pages: a runtime arena permits transparent huge pages")
    if not regions:
        raise RuntimeError("huge pages: no complete runtime arena with a protected guard")


def check_program(app):
    """Check every observed arena segment before its guard carries nh."""
    p = subprocess.Popen([str(app)], stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                         stderr=subprocess.PIPE)
    try:
        ready = p.stdout.readline()
        if b"ready" not in ready:
            raise RuntimeError(f"huge pages: the program said {ready!r}")
        smaps = Path(f"/proc/{p.pid}/smaps").read_text()
    finally:
        p.communicate(b"\n", timeout=60)
    _check_arena_mappings(smaps)

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
        r = subprocess.run([str(exe), "build", "-o", str(app), str(source)], cwd=root,
                           capture_output=True, text=True, errors="replace", timeout=300)
        if r.returncode != 0:
            raise RuntimeError(f"huge pages: goose build:\n{r.stdout}{r.stderr}")
        check_program(app)
    return None
