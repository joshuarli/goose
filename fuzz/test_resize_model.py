import copy
import json
import unittest

from fuzz.resize_model import (ResizeProgram, ResizeStep, evaluate, generate,
                               reductions, render)


class ResizeModelTests(unittest.TestCase):
    def test_operation_order_and_returned_pop_value(self):
        program = ResizeProgram((4, 7), (
            ResizeStep('print_len'),
            ResizeStep('push', (11,)),
            ResizeStep('append', (13, 17)),
            ResizeStep('pop'),
            ResizeStep('pop_n', count=2),
            ResizeStep('print_at', lo=1),
            ResizeStep('print_slice', lo=0, hi=2),
            ResizeStep('clear'),
            ResizeStep('print_len'),
        ))
        self.assertEqual(evaluate(program), b'2\n17\n7\n2\n4\n7\n0\n')
        source = render(program)
        self.assertIn('let fuzz_append_2: i64[2] = [(13), (17)];', source)
        self.assertIn('fuzz_values.append(fuzz_append_2);', source)
        self.assertNotIn('fuzz_values.append([', source)
        self.assertIn('print(fuzz_values.pop());', source)
        self.assertIn('fuzz_values.pop_n(2);', source)
        self.assertIn('fuzz_values.clear();', source)
        self.assertIn('print(fuzz_values[0..2].len);', source)

    def test_resize_growth_fill_and_empty_array(self):
        program = ResizeProgram((), (
            ResizeStep('resize', count=3, fill=-2),
            ResizeStep('print_slice', lo=0, hi=3),
            ResizeStep('resize', count=0),
            ResizeStep('print_len'),
        ))
        self.assertEqual(evaluate(program), b'3\n-2\n-2\n-2\n0\n')
        self.assertIn('var fuzz_values: i64[>..<] = [];', render(program))

    def test_generated_recipes_are_deterministic_strict_and_reducible(self):
        sources = set()
        for seed in range(128):
            program = generate(seed)
            self.assertEqual(program, generate(seed))
            recipe = json.loads(json.dumps(program.to_dict()))
            rebuilt = ResizeProgram.from_dict(recipe)
            self.assertEqual(program, rebuilt)
            self.assertEqual(evaluate(program), evaluate(rebuilt))
            self.assertEqual(render(program), render(rebuilt))
            sources.add(render(program))
            candidates = list(reductions(program))
            self.assertTrue(candidates)
            for candidate in candidates:
                self.assertNotEqual(candidate, program)
                self.assertEqual(candidate, ResizeProgram.from_dict(candidate.to_dict()))
                evaluate(candidate)
                render(candidate)
        self.assertEqual(len(sources), 128)

    def test_recipe_rejects_wrong_contract_and_non_integer_values(self):
        recipe = generate(4).to_dict()
        for key, value in (('lane', 'scalar'), ('version', True),
                           ('expectation', 'MayTrap'), ('extra', 1)):
            invalid = copy.deepcopy(recipe)
            invalid[key] = value
            with self.assertRaises(ValueError):
                ResizeProgram.from_dict(invalid)
        invalid = copy.deepcopy(recipe)
        invalid['initial'] = [True]
        with self.assertRaises(ValueError):
            ResizeProgram.from_dict(invalid)

    def test_invalid_operations_and_unproven_accesses_fail(self):
        invalid = (
            ResizeProgram((), (ResizeStep('pop'),)),
            ResizeProgram((1,), (ResizeStep('print_at', lo=1),)),
            ResizeProgram((1,), (ResizeStep('print_slice', lo=1, hi=0),)),
            ResizeProgram((), (ResizeStep('resize', count=1),)),
            ResizeProgram((1,), (ResizeStep('resize', count=0, fill=2),)),
            ResizeProgram((1,), (ResizeStep('append', (1,) * 13),)),
            ResizeProgram((1,), (ResizeStep('resize', count=13, fill=0),)),
            ResizeProgram((1,), (ResizeStep('unknown'),)),
            ResizeProgram((True,), ()),
        )
        for program in invalid:
            with self.subTest(program=program):
                with self.assertRaises(ValueError):
                    evaluate(program)
        for seed in (True, -1, 1 << 64):
            with self.assertRaises(ValueError):
                generate(seed)


if __name__ == '__main__':
    unittest.main()
