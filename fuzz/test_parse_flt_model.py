import copy
import json
import unittest

from fuzz.parse_flt_model import ParseFltProgram, evaluate, generate, reductions, render


class ParseFltModelTests(unittest.TestCase):
    def test_seed_zero_is_the_historical_leading_zero_case(self):
        program = generate(0)
        self.assertEqual(program.text, '00000000000000000001')
        self.assertEqual(evaluate(program), b'true\n')
        self.assertIn('let fuzz_expected: f64 = 1.0;', render(program))

    def test_valid_negative_zero_checks_its_sign(self):
        program = ParseFltProgram('-00000000000000000000.000')
        source = render(program)
        self.assertIn('1.0 / fuzz_value < 0.0', source)
        self.assertIn('1.0 / fuzz_expected < 0.0', source)

    def test_invalid_forms_require_clean_parse_failure(self):
        for text in ('1x', '0.1e', '0.1e+', '.', '+'):
            source = render(ParseFltProgram(text))
            self.assertIn('!fuzz_ok && fuzz_value == 0.0', source)

    def test_generation_roundtrips_and_reduces(self):
        sources = set()
        for seed in range(128):
            program = generate(seed)
            rebuilt = ParseFltProgram.from_dict(json.loads(json.dumps(program.to_dict())))
            self.assertEqual(program, rebuilt)
            self.assertEqual(evaluate(program), evaluate(rebuilt))
            self.assertEqual(render(program), render(rebuilt))
            sources.add(render(program))
            for candidate in reductions(program):
                self.assertNotEqual(candidate, program)
                evaluate(candidate)
                render(candidate)
        self.assertGreater(len(sources), 100)

    def test_strict_recipe_validation(self):
        original = generate(0).to_dict()
        for key, value in (('lane', 'scalar'), ('version', True),
                           ('expectation', 'MustTrap'), ('source', '1')):
            recipe = copy.deepcopy(original)
            recipe[key] = value
            with self.assertRaises(ValueError):
                ParseFltProgram.from_dict(recipe)
        for text in ('', ' 1', 'nan', '1_0', '1\n'):
            with self.assertRaises(ValueError):
                render(ParseFltProgram(text))


if __name__ == '__main__':
    unittest.main()
