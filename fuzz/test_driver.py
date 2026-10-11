import base64
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from fuzz import aggregate_model, driver, numeric_model, order_model, resize_model, trap_model
from fuzz.model import evaluate, generate, render
from fuzz.process import Result


def result(returncode=0, stdout=b'', stderr=b'', limit=None):
    return Result(('fake',), returncode, stdout, stderr, 0.01, limit)


class ClassifierTests(unittest.TestCase):
    def test_limits_take_precedence_over_exit_and_output(self):
        for stage in ('goose', 'c', 'program'):
            for limit, failure in (('timeout', 'timeout'), ('output', 'output_limit')):
                with self.subTest(stage=stage, limit=limit):
                    observed = result(-9, stdout=b'wrong', limit=limit)
                    self.assertEqual(driver.classify(stage, observed, b'expected'), failure)

    def test_sanitizer_diagnostics_take_precedence_over_exit_and_output(self):
        for diagnostic in (b'ERROR: AddressSanitizer: heap-buffer-overflow',
                           b'source.c:12:3: runtime error: signed integer overflow'):
            for returncode in (0, 1, -6):
                for stream in ('stdout', 'stderr'):
                    with self.subTest(diagnostic=diagnostic, returncode=returncode, stream=stream):
                        observed = result(returncode, **{stream: diagnostic})
                        self.assertEqual(driver.classify('program', observed, b'expected'), 'sanitizer')

    def test_sanitizer_diagnostic_survives_process_limits(self):
        for limit in ('timeout', 'output'):
            observed = result(-9, stderr=b'ERROR: AddressSanitizer: heap-buffer-overflow', limit=limit)
            self.assertEqual(driver.classify('program', observed, b''), 'sanitizer')

    def test_stage_failures(self):
        for stage, code, failure in (
            ('goose', -11, 'compiler_crash'),
            ('goose', 1, 'false_rejection'),
            ('c', 1, 'c_compile_failure'),
            ('c', -11, 'c_compile_failure'),
            ('program', 1, 'unexpected_trap'),
            ('program', -11, 'unexpected_trap'),
        ):
            with self.subTest(stage=stage, code=code):
                self.assertEqual(driver.classify(stage, result(code), b''), failure)

    def test_success_requires_exact_program_output(self):
        self.assertIsNone(driver.classify('goose', result(stdout=b'compiler output'), None))
        self.assertIsNone(driver.classify('c', result(stdout=b'compiler output'), None))
        self.assertIsNone(driver.classify('program', result(stdout=b'1\n'), b'1\n'))
        self.assertEqual(driver.classify('program', result(stdout=b'1'), b'1\n'), 'output_mismatch')
        self.assertEqual(driver.classify('program', result(stdout=b'1\nextra'), b'1\n'), 'output_mismatch')
        self.assertEqual(driver.classify('program', result(stdout=b'1\n', stderr=b'warning\n'), b'1\n'),
                         'output_mismatch')

    def test_expected_trap_requires_exit_prefix_and_diagnostic(self):
        expected = trap_model.TrapExpectation(b'41\n0\n', ('division by zero',))
        self.assertIsNone(driver.classify(
            'program', result(1, stdout=b'41\n0\n', stderr=b'goose runtime error: division by zero\n'), expected))
        self.assertEqual(driver.classify('program', result(stdout=b'41\n0\n'), expected),
                         'missing_trap')
        self.assertEqual(driver.classify(
            'program', result(1, stdout=b'41\n', stderr=b'division by zero'), expected),
            'output_mismatch')
        self.assertEqual(driver.classify(
            'program', result(1, stdout=b'41\n0\n', stderr=b'other failure'), expected),
            'trap_diagnostic')


class DriverTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.work = Path(self.directory.name)
        self.program = generate(7)
        self.expected = evaluate(self.program)

    def check(self, matrix, **kwargs):
        return driver.check(self.program, Path('/tools/goose'), Path('/tools/cc'), matrix, self.work, **kwargs)

    def test_every_matrix_configuration_executes_all_stages(self):
        matrix = [(0, 0), (1, 2), (2, 3)]
        calls = []

        def run(argv, cwd, timeout, output_limit, **kwargs):
            calls.append((list(map(str, argv)), (cwd, timeout, output_limit)))
            return result(stdout=self.expected if len(calls) % 3 == 0 else b'')

        with patch.object(driver, 'run', side_effect=run):
            report = self.check(matrix, timeout=2.5, output_limit=1234)
        self.assertIsNone(report['failure'])
        self.assertEqual(report['expected'], {
            'kind': 'MustCompileAndReturn', 'stdout': self.expected.decode()})
        self.assertEqual(len(calls), 9)
        self.assertEqual(
            [(item['goose_opt'], item['c_opt'], item['stage']) for item in report['results']],
            [(goose_opt, c_opt, stage) for goose_opt, c_opt in matrix for stage in ('goose', 'c', 'program')],
        )
        for index, (goose_opt, c_opt) in enumerate(matrix):
            goose_command, _ = calls[index * 3]
            c_command, _ = calls[index * 3 + 1]
            self.assertEqual(goose_command[0], '/tools/goose')
            self.assertIn('--standalone', goose_command)
            self.assertIn('-o', goose_command)
            self.assertIn(f'-O{goose_opt}', goose_command)
            self.assertEqual(c_command[0], '/tools/cc')
            self.assertIn(f'-O{c_opt}', c_command)
        for _, (cwd, timeout, output_limit) in calls:
            self.assertEqual(cwd, self.work)
            self.assertEqual(timeout, 2.5)
            self.assertEqual(output_limit, 1234)

    def test_order_lane_uses_its_renderer_and_oracle(self):
        program = order_model.generate(7)
        expected = order_model.evaluate(program)
        calls = []

        def run(argv, cwd, timeout, output_limit, **kwargs):
            calls.append(list(map(str, argv)))
            return result(stdout=expected if len(calls) == 3 else b'')

        with patch.object(driver, 'run', side_effect=run):
            report = driver.check(program, Path('/tools/goose'), Path('/tools/cc'),
                                  [(0, 0)], self.work)
        self.assertIsNone(report['failure'])
        self.assertEqual(report['lane'], 'order')
        self.assertEqual((self.work / 'source.goose').read_text(), order_model.render(program))

    def test_recipe_lane_selects_the_matching_model(self):
        for lane, model in (('scalar', driver.scalar_model), ('aggregate', aggregate_model),
                            ('numeric', numeric_model),
                            ('order', order_model),
                            ('resize', resize_model), ('trap', trap_model)):
            recipe = model.generate(9).to_dict()
            selected, program = driver.load_recipe(recipe)
            self.assertIs(selected, model)
            self.assertEqual(program, model.Program.from_dict(recipe))
        with self.assertRaisesRegex(ValueError, 'unknown fuzz lane'):
            driver.load_recipe({'lane': 'missing'})

    def test_campaign_deadline_does_not_shorten_a_started_case(self):
        completed = {'failure': None, 'results': [], 'expected': '', 'lane': 'scalar',
                     'matrix': [(0, 0)], 'sanitize': False}
        with patch.object(driver, 'resolve_tools', return_value=(Path('/tools/goose'), Path('/tools/cc'))), \
             patch.object(driver, 'identity', return_value={'goose': '/tools/goose', 'cc': '/tools/cc'}), \
             patch.object(driver, 'check', return_value=completed) as check:
            status = driver.main(['run', '--count', '1', '--duration', '0.001',
                                  '--output', str(self.work / 'campaigns')])
        self.assertEqual(status, 0)
        self.assertNotIn('deadline', check.call_args.kwargs)
        self.assertEqual(check.call_args.args[5], 10)

    def test_compile_failure_stops_before_later_stages(self):
        for stage, replies, failure in (
            ('goose', [result(1, stderr=b'rejected')], 'false_rejection'),
            ('c', [result(), result(1, stderr=b'C compile failed')], 'c_compile_failure'),
        ):
            with self.subTest(stage=stage):
                with patch.object(driver, 'run', side_effect=replies) as run:
                    report = self.check([(1, 2), (2, 3)])
                self.assertEqual(run.call_count, len(replies))
                self.assertEqual(report['failure'], {'class': failure, 'stage': stage, 'goose_opt': 1, 'c_opt': 2})

    def test_sanitizer_build_flags(self):
        with patch.object(driver, 'run', side_effect=[result(), result(), result(stdout=self.expected)]) as run:
            report = self.check([(0, 0)], sanitize=True)
        self.assertIsNone(report['failure'])
        command = list(map(str, run.call_args_list[1].args[0]))
        self.assertIn('-fsanitize=address,undefined', command)
        self.assertIn('-fno-sanitize-recover=all', command)

    def test_artifact_preserves_recipe_source_report_and_identity(self):
        evidence = result(1, stdout=b'\xff\x00', stderr=b'original error\n').to_dict()
        report = {
            'failure': {'class': 'unexpected_trap', 'stage': 'program', 'goose_opt': 1, 'c_opt': 2},
            'results': [evidence],
            'expected': self.expected.decode(),
        }
        identity = {'goose': '/tools/goose', 'goose_sha256': 'abc', 'cc': '/tools/clang'}
        saved = driver.save_artifact(self.work / 'artifact', self.program, report, identity)
        self.assertEqual(json.loads((saved / 'recipe.json').read_text()), self.program.to_dict())
        self.assertEqual((saved / 'source.goose').read_text(), render(self.program))
        self.assertEqual(json.loads((saved / 'report.json').read_text()), report)
        self.assertEqual(json.loads((saved / 'identity.json').read_text()), identity)
        self.assertIn('--exe /tools/goose --cc /tools/clang', (saved / 'replay.txt').read_text())
        restored = json.loads((saved / 'report.json').read_text())['results'][0]
        self.assertEqual(base64.b64decode(restored['stdout_b64']), b'\xff\x00')
        self.assertEqual(base64.b64decode(restored['stderr_b64']), b'original error\n')

    def test_existing_artifact_cannot_be_overwritten(self):
        directory = self.work / 'artifact'
        identity = {'goose': '/tools/goose', 'cc': '/tools/clang'}
        driver.save_artifact(directory, self.program, {'original': True}, identity)
        with self.assertRaises(FileExistsError):
            driver.save_artifact(directory, self.program, {'original': False}, identity)
        self.assertEqual(json.loads((directory / 'report.json').read_text()), {'original': True})
        self.assertEqual(json.loads((directory / 'identity.json').read_text()), identity)

    def test_reduction_preserves_the_exact_failure(self):
        target = {'class': 'output_mismatch', 'stage': 'program', 'goose_opt': 2, 'c_opt': 0}
        with patch.object(driver, 'check', return_value={'failure': target}):
            reduced, attempts = driver.reduce_case(
                self.program, target, Path('/tools/goose'), Path('/tools/cc'), [(2, 0)],
                self.work, 1, 1, 1024, False)
        self.assertGreater(attempts, 0)
        self.assertLess(len(reduced.body), len(self.program.body))


if __name__ == '__main__':
    unittest.main()
