import dataclasses
import tempfile
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import units_corpus


ROOT = Path(__file__).resolve().parents[2]


class UnitsCorpusTests(unittest.TestCase):
    def setUp(self):
        self.scratch = ROOT / ".work" / "tmp"
        self.scratch.mkdir(parents=True, exist_ok=True)

    def fixture(self):
        harness = units_corpus.semantics_harness()
        fixture = next(f for f in harness.discover(ROOT / "test" / "semantics")
                       if f.name == "sem_mem07_capacity_abort")
        return harness, fixture

    def test_pilot_accepts_main_runner_abort_metadata_without_location(self):
        harness, fixture = self.fixture()

        self.assertEqual(fixture.stderr, ROOT / "test" / "expected" / "sem_mem07_capacity_abort.stderr")
        self.assertEqual(units_corpus.expected_pilot_outcome(harness, fixture),
                         ("aborted", "user_abort", None))

    def test_pilot_still_matches_a_well_formed_location(self):
        harness, fixture = self.fixture()
        with tempfile.TemporaryDirectory(dir=self.scratch) as temporary:
            stderr = Path(temporary) / "located.stderr"
            stderr.write_text("limited array capacity exceeded\nfixture.goose:41)\n",
                              encoding="utf-8")
            located = dataclasses.replace(fixture, stderr=stderr)

            self.assertEqual(units_corpus.expected_pilot_outcome(harness, located),
                             ("aborted", "user_abort", 41))

    def test_pilot_rejects_malformed_source_location_metadata(self):
        harness, fixture = self.fixture()
        with tempfile.TemporaryDirectory(dir=self.scratch) as temporary:
            stderr = Path(temporary) / "bad.stderr"
            stderr.write_text("limited array capacity exceeded\nfixture.goose:line)\n",
                              encoding="utf-8")
            malformed = dataclasses.replace(fixture, stderr=stderr)

            with self.assertRaisesRegex(harness.HarnessFailure, "malformed source location"):
                units_corpus.expected_pilot_outcome(harness, malformed)


if __name__ == "__main__":
    unittest.main()
