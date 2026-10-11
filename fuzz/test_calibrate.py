import unittest

from fuzz.calibrate import BASE_REVISION, CALIBRATIONS, matches_failure


class CalibrationTests(unittest.TestCase):
    def test_recent_bug_calibrations_are_pinned(self):
        self.assertEqual(BASE_REVISION, 'de24a15659248fce28a1d5bdc8a6375bea322a0a')
        self.assertEqual(set(CALIBRATIONS), {'pr21', 'pr22', 'pr23'})
        self.assertEqual({case.lane for case in CALIBRATIONS.values()},
                         {'parse_flt', 'serialize', 'reference'})
        for case in CALIBRATIONS.values():
            self.assertEqual(len(case.fixed_revision), 40)
            self.assertEqual(case.seed, 0)

    def test_failure_match_uses_the_bug_class_and_stage(self):
        observed = {'class': 'output_mismatch', 'stage': 'program',
                    'goose_opt': 2, 'c_opt': 0}
        self.assertTrue(matches_failure(observed, 'output_mismatch', 'program'))
        self.assertFalse(matches_failure(observed, 'sanitizer', 'program'))
        self.assertFalse(matches_failure(None, 'output_mismatch', 'program'))


if __name__ == '__main__':
    unittest.main()
