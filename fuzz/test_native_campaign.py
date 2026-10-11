import tempfile
import unittest
from pathlib import Path

from fuzz.native_campaign import artifact_fingerprints, parse_statistics


class NativeCampaignTests(unittest.TestCase):
    def test_parses_coverage_pipeline_and_libfuzzer_statistics(self):
        output = b'''#12 NEW cov: 120 ft: 450 corp: 8/900b lim: 100 exec/s: 12 rss: 80Mb
#20 DONE cov: 145 ft: 510 corp: 11/1200b lim: 100 exec/s: 20 rss: 90Mb
stat::number_of_executed_units: 20
stat::average_exec_per_sec:     19
stat::new_units_added:          4
stat::peak_rss_mb:              91
goose_pipeline_metrics inputs=20 accepted=7 compilations=140 input=40 parsed=10 resolved=20 typed=2 optimized=1 bounds_checked=0 generated=67
'''
        self.assertEqual(parse_statistics(output), {
            'coverage_edges': 145,
            'coverage_features': 510,
            'corpus_units': 11,
            'corpus_bytes': 1200,
            'executed_units': 20,
            'executions_per_second': 19,
            'new_units': 4,
            'peak_rss_mb': 91,
            'pipeline': {
                'inputs': 20, 'accepted': 7, 'compilations': 140,
                'input': 40, 'parsed': 10, 'resolved': 20, 'typed': 2,
                'optimized': 1, 'bounds_checked': 0, 'generated': 67,
                'acceptance_rate': 0.35,
            },
        })

    def test_fingerprints_only_failure_artifacts(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'crash-one').write_bytes(b'one')
            (root / 'timeout-two').write_bytes(b'two')
            (root / 'notes.txt').write_text('ignore')
            fingerprints = artifact_fingerprints(root)
        self.assertEqual([item['name'] for item in fingerprints],
                         ['crash-one', 'timeout-two'])
        self.assertEqual(len({item['sha256'] for item in fingerprints}), 2)

    def test_parses_scaled_corpus_size(self):
        statistics = parse_statistics(
            b'#44 DONE cov: 5111 ft: 24570 corp: 274/428Kb lim: 4096\n')
        self.assertEqual(statistics['corpus_bytes'], 428 * 1024)


if __name__ == '__main__':
    unittest.main()
