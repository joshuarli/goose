import copy
import json
import unittest

from fuzz.model import Expr, Local, Program, Statement, evaluate, generate, reductions, render


def integer(value):
    return Expr('literal', 'i64', value)


def reference(name, type='i64'):
    return Expr('local', type, name)


class ModelTests(unittest.TestCase):
    def test_assignment_branch_loop_and_helper_semantics(self):
        x = reference('x')
        program = Program((Local('x', 'i64', 2), Local('flag', 'bool', True)), (
            Statement('repeat', count=3, body=(Statement('assign', name='x', expr=Expr('+', 'i64', args=(x, integer(2)))),)),
            Statement('if', expr=reference('flag', 'bool'), body=(Statement('assign', name='x', expr=Expr('double', 'i64', args=(x,))),), otherwise=(Statement('assign', name='x', expr=integer(-1)),)),
            Statement('print', expr=x), Statement('print', expr=reference('flag', 'bool')),
        ))
        self.assertEqual(evaluate(program), b'16\ntrue\n')
        self.assertIn('fn fuzz_double(x: i64) -> i64', render(program))

    def test_generation_is_deterministic_and_roundtrips(self):
        for seed in range(100):
            program = generate(seed)
            self.assertEqual(program, generate(seed))
            self.assertEqual(program.to_dict()['lane'], 'scalar')
            rebuilt = Program.from_dict(json.loads(json.dumps(program.to_dict())))
            self.assertEqual(program, rebuilt)
            self.assertEqual(evaluate(program), evaluate(rebuilt))
            self.assertEqual(render(program), render(rebuilt))
        self.assertNotEqual(generate(0), generate(1))

    def test_reductions_recompute_expected_output(self):
        program = Program((Local('x', 'i64', 4),), (Statement('assign', name='x', expr=integer(9)), Statement('print', expr=reference('x'))))
        candidates = list(reductions(program))
        self.assertTrue(candidates)
        self.assertIn(b'4\n', [evaluate(candidate) for candidate in candidates])
        self.assertTrue(all(candidate != program for candidate in candidates))
        for candidate in candidates:
            self.assertEqual(candidate, Program.from_dict(candidate.to_dict()))

    def test_invalid_recipe_is_rejected(self):
        recipe = generate(0).to_dict()
        for key, value in [('expectation', 'MayTrap'), ('version', 99), ('source', 'print(999)')]:
            damaged = copy.deepcopy(recipe)
            damaged[key] = value
            with self.assertRaises(ValueError):
                Program.from_dict(damaged)
        with self.assertRaises(ValueError):
            evaluate(Program((Local('x', 'i64', (1 << 63) - 1),), (Statement('print', expr=Expr('double', 'i64', args=(reference('x'),))),)))
        with self.assertRaises(ValueError):
            evaluate(Program((Local('x; print(1)', 'i64', 0),), ()))
        with self.assertRaises(ValueError):
            evaluate(Program((Local('x', 'i64', 0),), (Statement('assign', name='x', expr=Expr('literal', 'bool', True)),)))

    def test_overflow_is_rejected_in_untaken_branch(self):
        x = reference('x')
        program = Program((Local('x', 'i64', (1 << 63) - 1),), (
            Statement('if', expr=Expr('literal', 'bool', False), body=(
                Statement('assign', name='x', expr=Expr('+', 'i64', args=(x, integer(1)))),
            )),
        ))
        with self.assertRaises(ValueError):
            evaluate(program)

    def test_unknown_operations_and_unbounded_loops_are_rejected(self):
        for statement in (
            Statement('print', expr=Expr('execute_source', 'i64', 'print(1)')),
            Statement('print', expr=reference('missing')),
            Statement('repeat', count=9),
            Statement('repeat', count=True),
        ):
            with self.assertRaises(ValueError):
                Program.from_dict({
                    'version': 1, 'lane': 'scalar', 'expectation': 'MustCompileAndReturn', 'locals': [],
                    'body': [{
                        'op': statement.op, 'name': None, 'count': statement.count,
                        'expr': None if statement.expr is None else {
                            'op': statement.expr.op, 'type': statement.expr.type,
                            'value': statement.expr.value, 'args': [],
                        },
                        'body': [], 'otherwise': [],
                    }],
                })
        for name in ('struct', 'in', 'fuzz_double', 'print'):
            with self.assertRaises(ValueError):
                render(Program((Local(name, 'i64', 0),), ()))

    def test_short_circuit_and_comparisons(self):
        program = Program((), (Statement('print', expr=Expr('&&', 'bool', args=(Expr('literal', 'bool', False), Expr('<', 'bool', args=(integer(1), integer(2)))))),))
        self.assertEqual(evaluate(program), b'false\n')


if __name__ == '__main__':
    unittest.main()
