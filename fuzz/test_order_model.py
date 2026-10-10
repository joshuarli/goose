import copy
import json
import unittest

from fuzz.order_model import (OrderArray, OrderExpr, OrderLocal, OrderProgram,
                              OrderSlice, OrderStatement, evaluate, generate,
                              reductions, render)


def literal(value):
    return OrderExpr('literal', 'bool' if type(value) is bool else 'i64', value)


def scalar(name):
    return OrderExpr('local', 'i64', name)


def view(name):
    return OrderExpr('view', 'slice', name)


def slice_local():
    return OrderExpr('local', 'slice', 's')


def index(receiver, offset=0):
    return OrderExpr('index', 'i64', args=(receiver, literal(offset)))


def assign(name, expr):
    return OrderStatement('assign', name=name, expr=expr)


def effect(body, result):
    return OrderExpr('effect', result.type, args=(result,), body=tuple(body))


def printing(expr):
    return OrderStatement('print', expr=expr)


def program(*body):
    return OrderProgram((OrderLocal('x', 'i64', 1), OrderLocal('i', 'i64', 0)),
                        (OrderArray('a', (10, 20, 30)), OrderArray('b', (40, 50, 60))),
                        (OrderSlice('s', 'a', 0, 3),), tuple(body))


class OrderModelTests(unittest.TestCase):
    def test_scalar_operand_and_compound_read_before_rhs_effect(self):
        change = effect((assign('x', literal(10)),), literal(2))
        p = program(printing(OrderExpr('+', 'i64', args=(scalar('x'), change))),
                    printing(scalar('x')), assign('x', literal(1)),
                    OrderStatement('add', name='x', expr=change), printing(scalar('x')))
        self.assertEqual(evaluate(p), b'3\n10\n3\n')
        self.assertIn('fn fuzz_order_effect_', render(p))

    def test_short_circuit_skips_and_runs_effects(self):
        change = effect((assign('x', literal(9)),), literal(True))
        p = program(printing(OrderExpr('&&', 'bool', args=(literal(False), change))),
                    printing(scalar('x')),
                    printing(OrderExpr('||', 'bool', args=(literal(True), change))),
                    printing(scalar('x')),
                    printing(OrderExpr('&&', 'bool', args=(literal(True), change))),
                    printing(scalar('x')))
        self.assertEqual(evaluate(p), b'false\n1\ntrue\n1\ntrue\n9\n')

    def test_indexed_compound_captures_destination_and_old_value(self):
        target = OrderExpr('index', 'i64', args=(view('a'), scalar('i')))
        change = effect((assign('i', literal(1)),
                         OrderStatement('store', target=index(view('a')), expr=literal(100))), literal(3))
        p = program(OrderStatement('add', target=target, expr=change),
                    printing(index(view('a'))), printing(index(view('a'), 1)))
        self.assertEqual(evaluate(p), b'13\n20\n')

    def test_index_captures_receiver_before_effect_repoints_slice(self):
        change = effect((assign('s', view('b')),), literal(0))
        p = program(printing(OrderExpr('index', 'i64', args=(slice_local(), change))),
                    printing(index(slice_local())))
        self.assertEqual(evaluate(p), b'10\n40\n')

    def test_slice_captures_receiver_and_lower_bound_before_upper_effect(self):
        change = effect((assign('i', literal(1)), assign('s', view('b'))), literal(2))
        sliced = OrderExpr('slice', 'slice', args=(slice_local(), scalar('i'), change))
        p = program(printing(OrderExpr('index', 'i64', args=(sliced, literal(0)))),
                    printing(index(slice_local())), printing(scalar('i')))
        self.assertEqual(evaluate(p), b'10\n40\n1\n')
        p = program(assign('s', sliced), printing(OrderExpr('len', 'i64', args=(slice_local(),))))
        self.assertEqual(evaluate(p), b'2\n')

    def test_call_snapshots_scalar_but_shares_slice_contents(self):
        change = effect((OrderStatement('store', target=index(view('a')), expr=literal(7)),), literal(2))
        call = OrderExpr('observe', 'i64', args=(index(view('a')), slice_local(), change))
        p = program(printing(call))
        self.assertEqual(evaluate(p), b'1072\n')

    def test_nested_effects_and_loop_state(self):
        bump = effect((OrderStatement('add', name='x', expr=literal(1)),), scalar('x'))
        p = program(OrderStatement('repeat', count=3, body=(printing(bump),)))
        self.assertEqual(evaluate(p), b'2\n3\n4\n')

    def test_generation_roundtrips_and_reduces_for_128_seeds(self):
        sources = set()
        for seed in range(128):
            p = generate(seed)
            self.assertEqual(p, generate(seed))
            rebuilt = OrderProgram.from_dict(json.loads(json.dumps(p.to_dict())))
            self.assertEqual(p, rebuilt)
            self.assertEqual(evaluate(p), evaluate(rebuilt))
            self.assertEqual(render(p), render(rebuilt))
            sources.add(render(p))
            candidates = list(reductions(p))
            self.assertTrue(candidates)
            for candidate in candidates:
                self.assertNotEqual(candidate, p)
                self.assertEqual(candidate, OrderProgram.from_dict(candidate.to_dict()))
                evaluate(candidate)
                render(candidate)
        self.assertEqual(len(sources), 128)

    def test_strict_recipes_and_invalid_programs(self):
        original = generate(0).to_dict()
        for key, value in (('lane', 'scalar'), ('version', True), ('expectation', 'MayTrap'),
                           ('source', 'print(9)')):
            recipe = copy.deepcopy(original)
            recipe[key] = value
            with self.assertRaises(ValueError):
                OrderProgram.from_dict(recipe)
        invalid = (program(printing(index(view('a'), 3))),
                   program(printing(OrderExpr('literal', 'i64', True))),
                   program(assign('missing', literal(0))),
                   program(printing(OrderExpr('unknown', 'i64'))),
                   program(OrderStatement('repeat', count=9)),
                   program(printing(OrderExpr('+', 'i64', args=(literal((1 << 63) - 1), literal(1))))),
                   OrderProgram((OrderLocal('fn', 'i64', 1),), (), (), ()))
        for p in invalid:
            with self.assertRaises(ValueError):
                evaluate(p)
        bad = OrderExpr('index', 'i64', args=(view('a'), literal(3)))
        skipped = OrderExpr('&&', 'bool', args=(literal(False), OrderExpr('<', 'bool', args=(bad, literal(0)))))
        with self.assertRaises(ValueError):
            evaluate(program(printing(skipped)))
        for seed in (True, -1, 1 << 64):
            with self.assertRaises(ValueError):
                generate(seed)


if __name__ == '__main__':
    unittest.main()
