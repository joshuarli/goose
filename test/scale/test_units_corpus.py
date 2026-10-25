import dataclasses
import tempfile
import sys
import unittest
from unittest.mock import Mock, patch
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

    def test_pilot_compares_raw_output_bytes(self):
        for actual, expected_status in ((b"\xff\n", "ok"), (b"\xfe\n", "FAIL")):
            with self.subTest(actual=actual), tempfile.TemporaryDirectory(dir=self.scratch) as temporary:
                directory = Path(temporary)
                output = directory / "binary.out"
                output.write_bytes(b"\xff\n")
                compiler = Mock()
                compiler.compile.return_value = (True, "")
                corpus = units_corpus.Corpus(Path("goose"), directory, compiler, {}, "gir")
                harness = corpus.harness
                fixture = harness.Fixture("binary", directory / "binary.goose", output,
                                          None, False, None, (harness.RELEASE,))
                ran = units_corpus.subprocess.CompletedProcess([], 0, actual, b"")
                with patch.object(units_corpus.tc, "run_capture", return_value=(0, "", "")), \
                        patch.object(harness, "run", return_value=ran):
                    status, _ = corpus.pilot(fixture)
                self.assertEqual(status, expected_status)

    def test_pilot_accepts_main_runner_abort_metadata_without_location(self):
        harness, fixture = self.fixture()

        self.assertEqual(fixture.stderr, ROOT / "test" / "expected" / "sem_mem07_capacity_abort.stderr")
        with tempfile.TemporaryDirectory(dir=self.scratch) as temporary:
            stderr = Path(temporary) / "unlocated.stderr"
            stderr.write_text("limited array capacity exceeded\n", encoding="utf-8")
            unlocated = dataclasses.replace(fixture, stderr=stderr)
            self.assertEqual(units_corpus.expected_pilot_outcome(harness, unlocated),
                             ("aborted", "capacity", None))

    def test_pilot_still_matches_a_well_formed_location(self):
        harness, fixture = self.fixture()
        with tempfile.TemporaryDirectory(dir=self.scratch) as temporary:
            stderr = Path(temporary) / "located.stderr"
            stderr.write_text("limited array capacity exceeded\nfixture.goose:41)\n",
                              encoding="utf-8")
            located = dataclasses.replace(fixture, stderr=stderr)

            self.assertEqual(units_corpus.expected_pilot_outcome(harness, located),
                             ("aborted", "capacity", 41))

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
