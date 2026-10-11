import copy
import json
import unittest

from fuzz.reference_model import (ReferenceProgram, RejectExpectation, evaluate,
                                  generate, reductions, render)


class ReferenceModelTests(unittest.TestCase):
    def test_historical_recursive_alias_case_models_locations(self):
        program = ReferenceProgram(
            'recursive_alias', 'MustCompileAndReturn', (1, -1), 0, 1, 2, 1,
            'positive', 0, 'q', 'q', True, 'array')
        self.assertEqual(evaluate(program), b'1\n2\n3\n')
        source = render(program)
        self.assertIn('recursive fn fuzz_descend(p: i64&, q: i64&, n: i64)', source)
        self.assertIn('fuzz_descend(q, q, n - 1);', source)

    def test_distinct_references_do_not_alias(self):
        program = ReferenceProgram(
            'recursive_alias', 'MustCompileAndReturn', (2, -1), 0, 1, 2, 1,
            'positive', 0, 'p', 'q', True, 'struct')
        self.assertEqual(evaluate(program), b'2\n2\n3\n')
        self.assertIn('struct FuzzCells', render(program))

    def test_readonly_alias_and_reference_rebinding(self):
        program = ReferenceProgram(
            'recursive_alias', 'MustCompileAndReturn', (2, 0, 9), 0, 1, 1, 1,
            'positive', 0, 'p', 'q', True, 'locals', True, True)
        source = render(program)
        self.assertIn('p: const i64&', source)
        self.assertIn('var fuzz_q: i64&', source)
        self.assertIn('fuzz_q .= fuzz_v1;', source)
        self.assertEqual(evaluate(program), b'2\n2\n9\n2\n')

    def test_recursive_slice_aliases_share_element_locations(self):
        program = ReferenceProgram(
            'recursive_slice_alias', 'MustCompileAndReturn', (2, 0), 0, 1, 2, 1,
            'equal', 2, 'q', 'q', True, 'array', True)
        source = render(program)
        self.assertIn('p: const i64[:], q: i64[:]', source)
        self.assertIn('q[0] += 1;', source)
        self.assertEqual(evaluate(program), b'2\n3\n3\n')

    def test_rejection_recipes_have_diagnostic_categories(self):
        for kind, fragment in (
                ('return_local_reference', 'dies with this function'),
                ('store_short_reference', 'does not outlive the destination'),
                ('shrink_live_alias', 'cannot clear')):
            program = ReferenceProgram(kind, 'MustReject')
            expected = evaluate(program)
            self.assertIsInstance(expected, RejectExpectation)
            self.assertIn(fragment, expected.diagnostic_contains)
            self.assertIn('fn main()', render(program))

    def test_generation_roundtrips_and_reduces(self):
        sources = set()
        kinds = set()
        for seed in range(128):
            program = generate(seed)
            self.assertEqual(program, generate(seed))
            rebuilt = ReferenceProgram.from_dict(json.loads(json.dumps(program.to_dict())))
            self.assertEqual(program, rebuilt)
            self.assertEqual(evaluate(program), evaluate(rebuilt))
            self.assertEqual(render(program), render(rebuilt))
            sources.add(render(program))
            kinds.add(program.kind)
            for candidate in reductions(program):
                self.assertNotEqual(candidate, program)
                self.assertEqual(candidate, ReferenceProgram.from_dict(candidate.to_dict()))
                evaluate(candidate)
                render(candidate)
        self.assertGreater(len(sources), 80)
        self.assertTrue({'recursive_alias', 'return_local_reference',
                         'store_short_reference', 'shrink_live_alias'} <= kinds)

    def test_strict_recipe_validation(self):
        original = generate(0).to_dict()
        for key, value in (('lane', 'scalar'), ('version', True),
                           ('expectation', 'MayCompile'), ('extra', 1)):
            recipe = copy.deepcopy(original)
            recipe[key] = value
            with self.assertRaises(ValueError):
                ReferenceProgram.from_dict(recipe)
        for seed in (True, -1, 1 << 64):
            with self.assertRaises(ValueError):
                generate(seed)


if __name__ == '__main__':
    unittest.main()
