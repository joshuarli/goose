import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from fuzz import driver, trap_model
from fuzz.model import evaluate, generate
from fuzz.process import Result

GOOSE, CC, TOOL = Path('/tools/goose'), Path('/tools/cc'), Path('/tools/sem')


def result(returncode=0, stdout=b'', stderr=b'', limit=None):
    return Result(('fake',), returncode, stdout, stderr, 0.01, limit)


def answer(value, code=0):
    return result(code, stdout=(json.dumps(value) + '\n').encode())


class FakeTools:
    """Dispatches the driver's subprocesses to canned results and records the commands."""

    def __init__(self, program_stdout, export=None, tool=None, goose=None, program=None):
        self.program_stdout = program_stdout
        self.export = export or result(stderr=b'parsed ok\n')
        self.tool = tool or answer(['done', ['returned'], program_stdout.decode()])
        self.goose = goose or result()
        self.program = program or result(stdout=program_stdout)
        self.commands = []

    def __call__(self, argv, cwd, timeout, output_limit, **kwargs):
        argv = list(map(str, argv))
        self.commands.append(argv)
        if argv[0] == str(CC):
            return result()
        if argv[0] == str(TOOL):
            return self.tool
        if argv[0] == str(GOOSE):
            if '--emit-core' in argv:
                if self.export.returncode == 0:
                    Path(argv[argv.index('--emit-core') + 1]).write_text('{}')
                return self.export
            if '--jit' in argv:
                return self.program
            return self.goose
        return self.program


class SemanticsStageTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.work = Path(self.directory.name)
        self.program = generate(7)
        self.expected = evaluate(self.program)

    def check(self, tools, program=None, **kwargs):
        with patch.object(driver, 'run', side_effect=tools):
            return driver.check(program or self.program, GOOSE, CC, [(0, 0)], self.work, **kwargs)

    def failing(self, tool):
        report = self.check(FakeTools(self.expected, tool=tool), semantics=TOOL)
        self.assertEqual(report['failure']['stage'], 'semantics')
        return report

    def test_flags_absent_leave_the_check_unchanged(self):
        tools = FakeTools(self.expected)
        report = self.check(tools)
        self.assertIsNone(report['failure'])
        self.assertNotIn('semantics', report)
        self.assertNotIn('semantics_tool', report)
        self.assertEqual([c[0] for c in tools.commands], [str(GOOSE), str(CC), str(self.work / 'program-g0-c0')])

    def test_agreeing_case_exports_and_runs_the_tool_in_release_numerics(self):
        tools = FakeTools(self.expected)
        report = self.check(tools, semantics=TOOL)
        self.assertIsNone(report['failure'])
        self.assertEqual(report['semantics']['status'], 'agree')
        export = next(c for c in tools.commands if '--emit-core' in c)
        self.assertEqual(export[-2:], ['--check', str(self.work / 'source.goose')])
        run = next(c for c in tools.commands if c[0] == str(TOOL))
        self.assertEqual(run[1], 'run')
        self.assertEqual(run[-2:], ['--numeric', 'release'])
        self.assertEqual([r['stage'] for r in report['results']][-2:], ['export', 'semantics'])
        self.assertEqual(report['semantics_tool'], str(TOOL))

    def test_trapping_case_compares_kind_and_output_before_the_trap(self):
        program = trap_model.TrapProgram('division_zero', (4, 5))
        expected = trap_model.evaluate(program)
        kind = driver.tool_abort_kind(expected)
        trap = result(1, stdout=expected.stdout_prefix, stderr=expected.stderr_contains[0].encode())
        for tool, failure in (
                (answer(['done', ['aborted', kind, 9], expected.stdout_prefix.decode()]), None),
                (answer(['done', ['aborted', 'assert', 9], expected.stdout_prefix.decode()]), 'semantics_mismatch'),
                (answer(['done', ['aborted', kind, 9], '']), 'semantics_mismatch'),
                (answer(['done', ['returned'], expected.stdout_prefix.decode()]), 'semantics_mismatch')):
            with self.subTest(tool=tool.stdout):
                report = self.check(FakeTools(expected.stdout_prefix, tool=tool, program=trap),
                                    program, semantics=TOOL)
                self.assertEqual((report['failure'] or {}).get('class'), failure)

    def test_every_trap_diagnostic_names_one_tool_abort_kind(self):
        for kind in trap_model.TRAP_KINDS:
            with self.subTest(kind=kind):
                expected = trap_model.TrapExpectation(b'', trap_model.TRAP_DIAGNOSTICS[kind])
                driver.tool_abort_kind(expected)
        with self.assertRaises(ValueError):
            driver.tool_abort_kind(trap_model.TrapExpectation(b'', ('unrelated',)))

    def test_disagreement_is_a_finding(self):
        for tool in (answer(['done', ['returned'], 'wrong\n']),
                     answer(['done', ['aborted', 'div_zero', 3], self.expected.decode()]),
                     answer(['fault', 'root_absent'], 4),
                     answer(['malformed', 'bad'], 2),
                     answer(['rejected', 'V-ROOT', 'no'], 5)):
            with self.subTest(tool=tool.stdout):
                report = self.failing(tool)
                self.assertEqual(report['failure']['class'], 'semantics_mismatch')
                self.assertEqual(report['semantics']['status'], 'finding')

    def test_tool_contract_violations_are_findings_of_their_own(self):
        for tool in (result(0, stdout=b'not json\n'),
                     result(0, stdout=b'["timeout",""]\n'),
                     answer(['done', ['returned'], 'x'], 3),
                     result(0, stdout=b'["done",["returned"],"x"]\n["done",["returned"],"x"]\n'),
                     result(-11)):
            with self.subTest(tool=tool.stdout, code=tool.returncode):
                self.assertEqual(self.failing(tool)['failure']['class'], 'semantics_tool_failure')
        self.assertEqual(self.failing(result(0, limit='output'))['failure']['class'],
                         'semantics_tool_failure')

    def test_unsupported_export_is_counted_and_is_not_a_finding(self):
        export = result(1, stderr=b'source.goose:4: unsupported in core-pilot: optional\n')
        report = self.check(FakeTools(self.expected, export=export), semantics=TOOL)
        self.assertIsNone(report['failure'])
        self.assertEqual(report['semantics'], {'status': 'unsupported', 'class': None,
                                               'feature': 'optional', 'detail': ''})

    def test_other_export_failures_are_findings(self):
        for export in (result(1, stderr=b'internal error'), result(-11),
                       result(2, stderr=b'unsupported in core-pilot: optional'),
                       result(0, limit='timeout')):
            with self.subTest(code=export.returncode):
                report = self.check(FakeTools(self.expected, export=export), semantics=TOOL)
                self.assertEqual(report['failure']['class'], 'semantics_export_failure')

    def test_running_out_of_fuel_or_time_is_inconclusive_not_a_finding(self):
        for tool in (answer(['timeout', 'partial'], 3), result(-9, limit='timeout')):
            with self.subTest(tool=tool.stdout):
                report = self.check(FakeTools(self.expected, tool=tool), semantics=TOOL)
                self.assertIsNone(report['failure'])
                self.assertEqual(report['semantics']['status'], 'inconclusive')

    def test_rejection_recipes_skip_both_stages(self):
        from fuzz import reference_model
        program = reference_model.ReferenceProgram('return_local_reference', 'MustReject')
        tools = FakeTools(b'', goose=result(1, stderr=b'error: dies with this function'))
        report = self.check(tools, program, semantics=TOOL, pipeline='gir')
        self.assertIsNone(report['failure'])
        self.assertNotIn('semantics', report)
        self.assertEqual([c[0] for c in tools.commands], [str(GOOSE)])

    def test_pipeline_builds_and_runs_against_the_model(self):
        tools = FakeTools(self.expected)
        report = self.check(tools, pipeline='gir')
        self.assertIsNone(report['failure'])
        build = [c for c in tools.commands if '--pipeline' in c]
        self.assertEqual(len(build), 2)
        self.assertTrue(all(c[c.index('--pipeline') + 1] == 'gir' for c in build))
        self.assertEqual(report['pipeline'], 'gir')
        self.assertEqual([r['stage'] for r in report['results']][-4:],
                         ['gir_goose', 'gir_c', 'gir_program', 'gir_jit'])

    def test_pipeline_failures_name_the_pipeline_stage(self):
        tools = FakeTools(self.expected)
        with patch.object(driver, 'run', side_effect=lambda argv, *a, **k: (
                result(1, stderr=b'unknown option') if '--pipeline' in map(str, argv)
                else tools(argv, *a, **k))):
            report = driver.check(self.program, GOOSE, CC, [(0, 0)], self.work, pipeline='gir')
        self.assertEqual(report['failure'], {'class': 'false_rejection', 'stage': 'gir_goose',
                                             'goose_opt': None, 'c_opt': None})

        class Mismatch(FakeTools):
            def __call__(self, argv, *a, **k):
                argv = list(map(str, argv))
                if argv[0].endswith('gir-c0'):
                    return result(stdout=b'other\n')
                return super().__call__(argv, *a, **k)

        report = self.check(Mismatch(self.expected), pipeline='gir')
        self.assertEqual(report['failure'], {'class': 'output_mismatch', 'stage': 'gir_program',
                                             'goose_opt': None, 'c_opt': 0})

    def test_artifact_replays_with_the_flags_and_keeps_the_export(self):
        report = self.check(FakeTools(self.expected, tool=answer(['done', ['returned'], 'wrong\n'])),
                            semantics=TOOL, pipeline='gir')
        saved = driver.save_artifact(self.work / 'artifact', self.program, report,
                                     {'goose': str(GOOSE), 'cc': str(CC)})
        driver.preserve(self.work, saved)
        replay = (saved / 'replay.txt').read_text()
        self.assertIn(f'--semantics {TOOL}', replay)
        self.assertIn('--pipeline gir', replay)
        self.assertTrue((saved / 'program.core').is_file())
        self.assertEqual(json.loads((saved / 'report.json').read_text())['failure']['stage'], 'semantics')


class CampaignTests(unittest.TestCase):
    def test_summary_counts_the_semantic_statuses_separately(self):
        reports = iter([
            {'failure': None, 'results': [], 'semantics': {'status': 'agree', 'feature': None}},
            {'failure': None, 'results': [], 'semantics': {'status': 'unsupported', 'feature': 'optional'}},
            {'failure': None, 'results': [], 'semantics': {'status': 'unsupported', 'feature': 'optional'}},
            {'failure': None, 'results': [], 'semantics': {'status': 'inconclusive', 'feature': None}},
        ])
        with tempfile.TemporaryDirectory() as directory, \
                patch.object(driver, 'resolve_tools', return_value=(GOOSE, CC)), \
                patch.object(driver, 'identity', return_value={'goose': str(GOOSE), 'cc': str(CC)}), \
                patch.object(driver, 'check', side_effect=lambda *a, **k: next(reports)):
            tool = Path(directory) / 'tool'
            tool.write_text('')
            output = Path(directory) / 'out'
            status = driver.main(['run', '--count', '4', '--output', str(output), '--semantics', str(tool),
                                  '--pipeline', 'gir'])
            self.assertEqual(status, 0)
            summary = json.loads(next(output.glob('run-*/summary.json')).read_text())
        self.assertEqual(summary['semantics'], {'agree': 1, 'unsupported': 2, 'inconclusive': 1,
                                                'unsupported_features': {'optional': 2}})
        self.assertEqual(summary['pipeline'], 'gir')

    def test_summary_is_unchanged_without_the_flags(self):
        with tempfile.TemporaryDirectory() as directory, \
                patch.object(driver, 'resolve_tools', return_value=(GOOSE, CC)), \
                patch.object(driver, 'identity', return_value={'goose': str(GOOSE), 'cc': str(CC)}), \
                patch.object(driver, 'check', return_value={'failure': None, 'results': []}):
            output = Path(directory) / 'out'
            driver.main(['run', '--count', '1', '--output', str(output)])
            summary = json.loads(next(output.glob('run-*/summary.json')).read_text())
        self.assertNotIn('semantics', summary)
        self.assertNotIn('pipeline', summary)

    def test_missing_tool_is_rejected_before_any_case_runs(self):
        with patch.object(driver, 'resolve_tools', return_value=(GOOSE, CC)), \
                patch.object(driver, 'check') as check:
            with self.assertRaisesRegex(ValueError, 'reference tool is unavailable'):
                driver.main(['run', '--count', '1', '--semantics', '/nonexistent/tool'])
        check.assert_not_called()


if __name__ == '__main__':
    unittest.main()
