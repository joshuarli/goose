import copy
import json
import unittest

from fuzz.numeric_model import Expr, Program, bounds, evaluate, generate, normalize, reductions, render


class NumericModelTests(unittest.TestCase):
    def test_width_and_sign_normalization(self):
        self.assertEqual(normalize(128, 'i8'), -128)
        self.assertEqual(normalize(-1, 'u8'), 255)
        self.assertEqual(bounds('u64'), (0, (1 << 64) - 1))

    def test_modular_arithmetic_and_euclidean_remainder(self):
        x = Expr('literal', 'i8', 127)
        neg = Expr('literal', 'i8', -7)
        three = Expr('literal', 'i8', 3)
        program = Program((), (
            Expr('+', 'i8', args=(x, Expr('literal', 'i8', 1))),
            Expr('%', 'i8', args=(neg, three)),
            Expr('%', 'i8', args=(Expr('literal', 'i8', -128), Expr('literal', 'i8', -1))),
            Expr('/', 'i8', args=(Expr('literal', 'i8', -128), Expr('literal', 'i8', -1))),
        ))
        self.assertEqual(evaluate(program), b'-128\n2\n0\n-128\n')

    def test_masked_shifts_and_unchecked_cast(self):
        program = Program((('x', 'i8', -1), ('count', 'u8', 9)), (
            Expr('<<', 'i8', args=(Expr('local', 'i8', 'x'), Expr('local', 'u8', 'count'))),
            Expr('>>', 'i8', args=(Expr('local', 'i8', 'x'), Expr('local', 'u8', 'count'))),
            Expr('as!', 'i8', args=(Expr('literal', 'u64', (1 << 64) - 1),)),
        ))
        self.assertEqual(evaluate(program), b'-2\n-1\n-1\n')

    def test_comparisons_follow_signedness_of_operands(self):
        program = Program((), (
            Expr('<', 'bool', args=(Expr('literal', 'i8', -1), Expr('literal', 'i8', 1))),
            Expr('<', 'bool', args=(Expr('literal', 'u8', 255), Expr('literal', 'u8', 1))),
        ))
        self.assertEqual(evaluate(program), b'true\nfalse\n')

    def test_generation_roundtrip_rendering_and_reduction(self):
        for seed in range(32):
            program = generate(seed)
            self.assertEqual(program, generate(seed))
            rebuilt = Program.from_dict(json.loads(json.dumps(program.to_dict())))
            self.assertEqual(evaluate(program), evaluate(rebuilt))
            self.assertEqual(render(program), render(rebuilt))
            self.assertEqual(program.to_dict()['lane'], 'numeric')
            self.assertTrue(list(reductions(program)))

    def test_invalid_lane_and_trapping_operations_are_rejected(self):
        recipe = generate(2).to_dict()
        damaged = copy.deepcopy(recipe)
        damaged['lane'] = 'scalar'
        with self.assertRaises(ValueError):
            Program.from_dict(damaged)
        with self.assertRaises(ValueError):
            evaluate(Program((), (Expr('/', 'i64', args=(Expr('literal', 'i64', -(1 << 63)), Expr('literal', 'i64', -1))),)))
        with self.assertRaises(ValueError):
            evaluate(Program((), (Expr('%', 'u8', args=(Expr('literal', 'u8', 1), Expr('literal', 'u8', 0))),)))


if __name__ == '__main__':
    unittest.main()
