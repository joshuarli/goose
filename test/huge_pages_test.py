from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
from huge_pages import _check_arena_mappings


class CompleteArenaAdvice(unittest.TestCase):
    def test_final_nohuge_suffix_does_not_cover_the_reservation(self):
        smaps = '''100000000-17fe00000 rw-p 00000000 00:00 0
THPeligible: 1
VmFlags: rd wr
17fe00000-180000000 rw-p 00000000 00:00 0
THPeligible: 0
VmFlags: rd wr nh
180000000-180100000 ---p 00000000 00:00 0
THPeligible: 0
VmFlags: mr mw
'''
        with self.assertRaisesRegex(RuntimeError, 'permits transparent huge pages'):
            _check_arena_mappings(smaps)

    def test_all_segments_cover_the_reservation(self):
        smaps = '''100000000-17fe00000 rw-p 00000000 00:00 0
THPeligible: 0
VmFlags: rd wr nh
17fe00000-180000000 rw-p 00000000 00:00 0
THPeligible: 0
VmFlags: rd wr nh
180000000-180100000 ---p 00000000 00:00 0
THPeligible: 0
VmFlags: mr mw
'''
        _check_arena_mappings(smaps)


if __name__ == '__main__':
    unittest.main()
