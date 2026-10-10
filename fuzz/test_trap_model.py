import unittest

from fuzz.trap_model import (
    Program,
    TRAP_KINDS,
    TrapProgram,
    evaluate,
    generate,
    reductions,
    render,
    validate,
)


class TrapModelTests(unittest.TestCase):
    def test_every_kind_has_a_valid_rendering_and_trap_oracle(self):
        for kind in TRAP_KINDS:
            with self.subTest(kind=kind):
                program = Program(kind, (7, -2))
                validate(program)
                source = render(program)
                expectation = evaluate(program)
                self.assertIn('fn main()', source)
                self.assertTrue(source.endswith('}\n'))
                self.assertEqual(expectation.stdout_prefix.startswith(b'7\n-2\n'), True)
                self.assertTrue(expectation.stderr_contains)

    def test_effectful_division_oracle_records_left_to_right_prefix(self):
        program = TrapProgram('evaluation_order')
        expectation = evaluate(program)
        source = render(program)
        self.assertEqual(expectation.stdout_prefix, b'41\n0\n')
        self.assertIn('fuzz_left() / fuzz_right()', source)
        self.assertLess(source.index('print(41)'), source.index('print(0)'))
        self.assertEqual(expectation.stderr_contains, ('division by zero',))

    def test_recipe_round_trip_and_closed_contract(self):
        for kind in TRAP_KINDS:
            program = TrapProgram(kind, (3,))
            recipe = program.to_dict()
            self.assertEqual(recipe['lane'], 'trap')
            self.assertEqual(recipe['expectation'], 'MustTrap')
            self.assertEqual(Program.from_dict(recipe), program)

        bad = TrapProgram('division_zero').to_dict()
        bad['extra'] = True
        with self.assertRaises(ValueError):
            Program.from_dict(bad)

    def test_generator_is_seeded_and_covers_trap_families(self):
        generated = [generate(seed) for seed in range(500)]
        self.assertEqual(generated, [generate(seed) for seed in range(500)])
        self.assertEqual({program.kind for program in generated}, set(TRAP_KINDS))

    def test_validation_rejects_unknown_and_oversized_programs(self):
        with self.assertRaises(ValueError):
            validate(TrapProgram('not-a-trap'))
        with self.assertRaises(ValueError):
            validate(TrapProgram('division_zero', (0,) * 9))
        with self.assertRaises(ValueError):
            validate(TrapProgram('division_zero', (2**40,)))

    def test_reductions_keep_the_trap_contract(self):
        program = TrapProgram('slice_bounds', (8, -4, 1))
        candidates = list(reductions(program))
        self.assertEqual(candidates[0], TrapProgram('slice_bounds', (8, -4)))
        self.assertIn(TrapProgram('slice_bounds', (8, -4, 0)), candidates)
        for candidate in candidates:
            validate(candidate)
            self.assertEqual(evaluate(candidate).stderr_contains,
                             evaluate(program).stderr_contains)


if __name__ == '__main__':
    unittest.main()
