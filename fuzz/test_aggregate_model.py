import unittest

from fuzz import aggregate_model as model


class AggregateModelTest(unittest.TestCase):
    def test_generation_roundtrips_and_renders_all_shapes(self):
        for seed in range(96):
            program = model.generate(seed)
            restored = model.Program.from_dict(program.to_dict())
            self.assertEqual(program, restored)
            self.assertEqual(model.evaluate(program), model.evaluate(restored))
            source = model.render(program)
            self.assertIn('import std;', source)
            self.assertNotIn('import os', source)
            self.assertIn('fuzz_mut', source)
        self.assertEqual(set(model.generate(seed).shape for seed in range(3)), set(model.SHAPES))

    def test_integer_oracle_wraps_at_each_leaf_width(self):
        program = model.Program('array_u8', (255, 0, 128), (1, 1, 2),
                                (model.Operation('+', False),))
        self.assertEqual(model.evaluate(program), b'0\n1\n130\n')
        mixed = model.Program('mixed_nested', (10, 12, 32000, -32000, 5),
                              (1, 1, 100, -100, 2), (model.Operation('+', False),))
        self.assertEqual(model.evaluate(mixed), b'11\n13\n32100\n-32100\n7\n')
        overflow = model.Program('mixed_nested', (2147483647, 0, 0, 0, 0),
                                 (1, 1, 1, 1, 1), (model.Operation('+', False),))
        with self.assertRaises(ValueError): model.evaluate(overflow)

    def test_signed_remainder_is_euclidean(self):
        program = model.Program('mixed_nested', (-7, -7, -7, 7, 7), (3, 3, 3, -3, -3),
                                (model.Operation('%', False),))
        self.assertEqual(model.evaluate(program), b'2\n2\n2\n1\n1\n')

    def test_rejects_malformed_lane_and_trapping_division(self):
        p = model.generate(0).to_dict()
        p['lane'] = 'numeric'
        with self.assertRaises(ValueError): model.Program.from_dict(p)
        bad = model.Program('mixed_nested', (1, 1, 1, 1, 1), (1, 0, 1, 1, 1),
                            (model.Operation('/', False),))
        with self.assertRaises(ValueError): model.evaluate(bad)
        illegal = model.Program('mixed_nested', (1, 1, 1, 1, 1), (1, 1, 1, 1, 1),
                                (model.Operation('*', False, 2),))
        with self.assertRaises(ValueError): model.evaluate(illegal)

    def test_reductions_stay_valid(self):
        program = model.generate(1)
        reductions = list(model.reductions(program))
        self.assertTrue(reductions)
        for reduced in reductions:
            model.validate(reduced)
            self.assertEqual(model.Program.from_dict(reduced.to_dict()), reduced)


if __name__ == '__main__':
    unittest.main()
