"""Terminating evaluation-order programs over scalars and fixed array views."""

from dataclasses import dataclass, replace
import random
import re
from typing import Iterator, Literal

from fuzz.model import MAX_I64, MIN_I64, RESERVED_NAMES

OrderType = Literal['i64', 'bool', 'slice']


@dataclass(frozen=True)
class OrderLocal:
    name: str
    type: Literal['i64', 'bool']
    value: int | bool


@dataclass(frozen=True)
class OrderArray:
    name: str
    values: tuple[int, ...]


@dataclass(frozen=True)
class OrderSlice:
    name: str
    array: str
    lo: int
    hi: int


@dataclass(frozen=True)
class OrderExpr:
    op: str
    type: OrderType
    value: int | bool | str | None = None
    args: tuple['OrderExpr', ...] = ()
    body: tuple['OrderStatement', ...] = ()


@dataclass(frozen=True)
class OrderStatement:
    op: str
    name: str | None = None
    expr: OrderExpr | None = None
    target: OrderExpr | None = None
    count: int | None = None
    body: tuple['OrderStatement', ...] = ()


@dataclass(frozen=True)
class OrderProgram:
    locals: tuple[OrderLocal, ...]
    arrays: tuple[OrderArray, ...]
    slices: tuple[OrderSlice, ...]
    body: tuple[OrderStatement, ...]

    def to_dict(self) -> dict:
        validate(self)
        def expression(e):
            return {'op': e.op, 'type': e.type, 'value': e.value,
                    'args': [expression(a) for a in e.args], 'body': [statement(s) for s in e.body]}
        def statement(s):
            return {'op': s.op, 'name': s.name, 'expr': None if s.expr is None else expression(s.expr),
                    'target': None if s.target is None else expression(s.target), 'count': s.count,
                    'body': [statement(child) for child in s.body]}
        return {'version': 1, 'lane': 'order', 'expectation': 'MustCompileAndReturn',
                'locals': [{'name': v.name, 'type': v.type, 'value': v.value} for v in self.locals],
                'arrays': [{'name': a.name, 'values': list(a.values)} for a in self.arrays],
                'slices': [{'name': s.name, 'array': s.array, 'lo': s.lo, 'hi': s.hi} for s in self.slices],
                'body': [statement(s) for s in self.body]}

    @classmethod
    def from_dict(cls, recipe: dict) -> 'OrderProgram':
        def fields(v, keys):
            if type(v) is not dict or set(v) != set(keys):
                raise ValueError('invalid order recipe fields')
        def items(v):
            if type(v) is not list or len(v) > 64:
                raise ValueError('invalid order recipe list')
            return v
        nodes = 0
        def budget(depth):
            nonlocal nodes
            nodes += 1
            if depth > 10 or nodes > 512:
                raise ValueError('order recipe node budget exceeded')
        def expression(v, depth=0):
            budget(depth)
            fields(v, ('op', 'type', 'value', 'args', 'body'))
            return OrderExpr(v['op'], v['type'], v['value'],
                             tuple(expression(a, depth + 1) for a in items(v['args'])),
                             tuple(statement(s, depth + 1) for s in items(v['body'])))
        def statement(v, depth=0):
            budget(depth)
            fields(v, ('op', 'name', 'expr', 'target', 'count', 'body'))
            return OrderStatement(v['op'], v['name'],
                                  None if v['expr'] is None else expression(v['expr'], depth + 1),
                                  None if v['target'] is None else expression(v['target'], depth + 1),
                                  v['count'], tuple(statement(s, depth + 1) for s in items(v['body'])))
        fields(recipe, ('version', 'lane', 'expectation', 'locals', 'arrays', 'slices', 'body'))
        if type(recipe['version']) is not int or recipe['version'] != 1 or recipe['lane'] != 'order' or recipe['expectation'] != 'MustCompileAndReturn':
            raise ValueError('unsupported order recipe contract')
        locals = []
        for v in items(recipe['locals']):
            fields(v, ('name', 'type', 'value'))
            locals.append(OrderLocal(v['name'], v['type'], v['value']))
        arrays = []
        for a in items(recipe['arrays']):
            fields(a, ('name', 'values'))
            arrays.append(OrderArray(a['name'], tuple(items(a['values']))))
        slices = []
        for s in items(recipe['slices']):
            fields(s, ('name', 'array', 'lo', 'hi'))
            slices.append(OrderSlice(s['name'], s['array'], s['lo'], s['hi']))
        result = cls(tuple(locals), tuple(arrays), tuple(slices), tuple(statement(s) for s in items(recipe['body'])))
        validate(result)
        return result


# Semantic lanes expose one uniform driver interface while retaining their
# domain-specific class names inside each model.
Program = OrderProgram


def validate(program: OrderProgram) -> None:
    """Check closed syntax, then prove bounds and arithmetic by bounded execution.

    There is no external input or nondeterminism. Checking the exact state at
    every operation proves reachable accesses; skipped expressions are checked
    independently too, so reductions cannot conceal invalid source behind a
    constant short circuit or zero-trip loop.
    """
    if not isinstance(program, OrderProgram):
        raise ValueError('invalid order program')
    names, array_lengths = {}, {}
    def name(n, t):
        if type(n) is not str or re.fullmatch(r'[a-z][a-z0-9_]*', n) is None or n in names or n in RESERVED_NAMES or n.startswith('fuzz_'):
            raise ValueError('invalid order local name')
        names[n] = t
    def integer(v):
        if type(v) is not int or not MIN_I64 <= v <= MAX_I64:
            raise ValueError('invalid order integer')
    for collection in (program.locals, program.arrays, program.slices, program.body):
        if type(collection) is not tuple or len(collection) > 64:
            raise ValueError('invalid order program collection')
    if len(program.locals) + len(program.arrays) + len(program.slices) > 16:
        raise ValueError('too many order locals')
    for v in program.locals:
        if not isinstance(v, OrderLocal) or v.type not in ('i64', 'bool'):
            raise ValueError('invalid order scalar')
        name(v.name, v.type)
        if v.type == 'i64':
            integer(v.value)
        elif type(v.value) is not bool:
            raise ValueError('invalid order boolean')
    for a in program.arrays:
        if not isinstance(a, OrderArray) or type(a.values) is not tuple or not 1 <= len(a.values) <= 8:
            raise ValueError('invalid fixed array')
        name(a.name, 'array')
        array_lengths[a.name] = len(a.values)
        for v in a.values:
            integer(v)
    for s in program.slices:
        if not isinstance(s, OrderSlice) or type(s.array) is not str or s.array not in array_lengths:
            raise ValueError('invalid slice root')
        name(s.name, 'slice')
        integer(s.lo)
        integer(s.hi)
        if not 0 <= s.lo <= s.hi <= array_lengths[s.array]:
            raise ValueError('invalid initial slice bounds')
    nodes = 0
    def budget(depth):
        nonlocal nodes
        nodes += 1
        if nodes > 512 or depth > 10:
            raise ValueError('order node budget exceeded')
    def expression(e, depth=0):
        budget(depth)
        if not isinstance(e, OrderExpr) or type(e.op) is not str or e.type not in ('i64', 'bool', 'slice') or type(e.args) is not tuple or type(e.body) is not tuple:
            raise ValueError('invalid order expression')
        if e.op == 'literal':
            if e.args or e.body or e.type == 'slice':
                raise ValueError('invalid order literal')
            if e.type == 'i64':
                integer(e.value)
            elif type(e.value) is not bool:
                raise ValueError('invalid order literal boolean')
        elif e.op in ('local', 'view'):
            expected = 'array' if e.op == 'view' else e.type
            if e.args or e.body or type(e.value) is not str or names.get(e.value) != expected or (e.op == 'view' and e.type != 'slice'):
                raise ValueError('invalid order variable read')
        else:
            signatures = {'+': (('i64', 'i64'), 'i64'), '-': (('i64', 'i64'), 'i64'), '*': (('i64', 'i64'), 'i64'),
                          '<': (('i64', 'i64'), 'bool'), '==': (('i64', 'i64'), 'bool'),
                          '&&': (('bool', 'bool'), 'bool'), '||': (('bool', 'bool'), 'bool'), '!': (('bool',), 'bool'),
                          'index': (('slice', 'i64'), 'i64'), 'slice': (('slice', 'i64', 'i64'), 'slice'),
                          'len': (('slice',), 'i64'), 'observe': (('i64', 'slice', 'i64'), 'i64')}
            if e.op == 'effect':
                if e.type not in ('i64', 'bool'):
                    raise ValueError('effect result must be scalar')
                signature = ((e.type,), e.type)
                statements(e.body, depth + 1)
            elif e.op in signatures and not e.body:
                signature = signatures[e.op]
            else:
                raise ValueError('unknown order expression operator')
            if e.value is not None or len(e.args) != len(signature[0]) or e.type != signature[1]:
                raise ValueError('invalid order expression signature')
            for a, t in zip(e.args, signature[0]):
                expression(a, depth + 1)
                if a.type != t:
                    raise ValueError('invalid order operand type')
    def statements(body, depth=0):
        if type(body) is not tuple or len(body) > 64:
            raise ValueError('invalid order block')
        for s in body:
            budget(depth)
            if not isinstance(s, OrderStatement) or type(s.op) is not str or type(s.body) is not tuple:
                raise ValueError('invalid order statement')
            if s.op == 'repeat':
                if s.name is not None or s.expr is not None or s.target is not None or type(s.count) is not int or not 0 <= s.count <= 8:
                    raise ValueError('invalid order bounded loop')
                statements(s.body, depth + 1)
                continue
            if s.count is not None or s.body or s.expr is None:
                raise ValueError('invalid order scalar statement')
            expression(s.expr, depth + 1)
            if s.op == 'print':
                if s.name is not None or s.target is not None or s.expr.type == 'slice':
                    raise ValueError('invalid order print')
            elif s.op in ('assign', 'store', 'add'):
                if (s.name is None) == (s.target is None):
                    raise ValueError('order assignment needs exactly one destination')
                if s.name is not None:
                    if s.op == 'store' or type(s.name) is not str or names.get(s.name) != s.expr.type:
                        raise ValueError('invalid order assignment name or type')
                else:
                    expression(s.target, depth + 1)
                    if s.op == 'assign' or s.target.op != 'index' or s.expr.type != 'i64':
                        raise ValueError('invalid order indexed destination')
                if s.op == 'add' and s.expr.type != 'i64':
                    raise ValueError('invalid order compound type')
            else:
                raise ValueError('unknown order statement operator')
    statements(program.body)
    _execute(program, check_skipped=True)


def _execute(program: OrderProgram, check_skipped: bool) -> bytes:
    scalars = {v.name: v.value for v in program.locals}
    arrays = {a.name: list(a.values) for a in program.arrays}
    slices = {s.name: (s.array, s.lo, s.hi - s.lo) for s in program.slices}
    output, steps = [], 0
    def checked(v):
        if type(v) is int and not MIN_I64 <= v <= MAX_I64:
            raise ValueError('order arithmetic can overflow i64')
        return v
    def tick():
        nonlocal steps
        steps += 1
        if steps > 10000:
            raise ValueError('order execution budget exceeded')
    def probe(action):
        saved_scalars, saved_arrays, saved_slices = scalars.copy(), {n: a[:] for n, a in arrays.items()}, slices.copy()
        size = len(output)
        action()
        scalars.clear()
        scalars.update(saved_scalars)
        arrays.clear()
        arrays.update(saved_arrays)
        slices.clear()
        slices.update(saved_slices)
        del output[size:]
    def destination(e):
        receiver = expression(e.args[0])
        i = expression(e.args[1])
        root, start, length = receiver
        if not 0 <= i < length:
            raise ValueError('order index outside sampled view')
        return root, start + i
    def expression(e):
        tick()
        if e.op == 'literal':
            return e.value
        if e.op == 'local':
            return slices[e.value] if e.type == 'slice' else scalars[e.value]
        if e.op == 'view':
            return e.value, 0, len(arrays[e.value])
        if e.op == 'effect':
            block(e.body)
            return expression(e.args[0])
        if e.op == 'index':
            root, i = destination(e)
            return arrays[root][i]
        a = expression(e.args[0])
        if e.op == 'len':
            return a[2]
        if e.op == '!':
            return not a
        if e.op in ('&&', '||'):
            runs = a if e.op == '&&' else not a
            if runs:
                return expression(e.args[1])
            if check_skipped:
                probe(lambda: expression(e.args[1]))
            return a
        b = expression(e.args[1])
        if e.op == 'slice':
            hi = expression(e.args[2])
            root, start, length = a
            if not 0 <= b <= hi <= length:
                raise ValueError('order slice outside sampled view')
            return root, start + b, hi - b
        if e.op == 'observe':
            tail = expression(e.args[2])
            root, start, length = b
            if length == 0:
                raise ValueError('observe needs a nonempty view')
            return checked(checked(checked(a * 100) + checked(arrays[root][start] * 10)) + tail)
        if e.op == '+':
            return checked(a + b)
        if e.op == '-':
            return checked(a - b)
        if e.op == '*':
            return checked(a * b)
        if e.op == '<':
            return a < b
        return a == b
    def block(body):
        for s in body:
            tick()
            if s.op == 'repeat':
                if check_skipped and not s.count:
                    probe(lambda: block(s.body))
                for _ in range(s.count):
                    block(s.body)
            elif s.op == 'print':
                v = expression(s.expr)
                output.append(('true' if v else 'false') if type(v) is bool else str(v))
            else:
                target = destination(s.target) if s.target is not None else None
                old = (arrays[target[0]][target[1]] if target is not None else scalars[s.name]) if s.op == 'add' else None
                value = expression(s.expr)
                if s.op == 'add':
                    value = checked(old + value)
                if target is not None:
                    arrays[target[0]][target[1]] = value
                elif s.expr.type == 'slice':
                    slices[s.name] = value
                else:
                    scalars[s.name] = value
    block(program.body)
    return ''.join(v + '\n' for v in output).encode('ascii')


def evaluate(program: OrderProgram) -> bytes:
    validate(program)
    return _execute(program, check_skipped=False)


def render(program: OrderProgram) -> str:
    validate(program)
    helpers = []
    helper_id = 0
    def expression(e):
        nonlocal helper_id
        if e.op == 'literal':
            return ('true' if e.value else 'false') if e.type == 'bool' else f'({e.value})'
        if e.op == 'local':
            return e.value
        if e.op == 'view':
            return f'{e.value}[..]'
        if e.op == 'effect':
            helper_id += 1
            name = f'fuzz_order_effect_{helper_id}'
            body = block(e.body, 2)
            result = expression(e.args[0])
            helpers.extend([f'    fn {name}() -> {e.type} {{', *body, f'        return {result};', '    }'])
            return f'{name}()'
        args = [expression(a) for a in e.args]
        if e.op == 'index':
            return f'({args[0]})[{args[1]}]'
        if e.op == 'slice':
            return f'({args[0]})[{args[1]}..{args[2]}]'
        if e.op == 'len':
            return f'({args[0]}).len'
        if e.op == 'observe':
            return f'fuzz_order_observe({", ".join(args)})'
        if e.op == '!':
            return f'(!{args[0]})'
        return f'({args[0]} {e.op} {args[1]})'
    loop_id = 0
    def block(body, depth):
        nonlocal loop_id
        lines = []
        pad = '    ' * depth
        for s in body:
            if s.op == 'repeat':
                loop_id += 1
                lines.append(f'{pad}for fuzz_order_loop_{loop_id} in 0..{s.count} {{')
                lines.extend(block(s.body, depth + 1))
                lines.append(f'{pad}}}')
            elif s.op == 'print':
                lines.append(f'{pad}print({expression(s.expr)});')
            else:
                target = expression(s.target) if s.target is not None else s.name
                rhs = expression(s.expr)
                lines.append(f'{pad}{target} {"+=" if s.op == "add" else "="} {rhs};')
        return lines
    lines = ['import std;', '', 'fn fuzz_order_observe(value: i64, view: i64[:], tail: i64) -> i64 {',
             '    value * 100 + view[0] * 10 + tail', '}', '', 'fn main() {']
    for v in program.locals:
        lines.append(f'    var {v.name}: {v.type} = {expression(OrderExpr("literal", v.type, v.value))};')
    for a in program.arrays:
        lines.append(f'    var {a.name}: i64[{len(a.values)}] = [{", ".join(f"({v})" for v in a.values)}];')
    for s in program.slices:
        lines.append(f'    var {s.name}: i64[:] = {s.array}[{s.lo}..{s.hi}];')
    body = block(program.body, 1)
    return '\n'.join([*lines, *helpers, *body, '}', ''])


def generate(seed: int) -> OrderProgram:
    if type(seed) is not int or not 0 <= seed < 1 << 64:
        raise ValueError('seed must be an unsigned 64-bit integer')
    rng = random.Random(seed)
    n = rng.randint(2, 6)
    def literal(v):
        return OrderExpr('literal', 'bool' if type(v) is bool else 'i64', v)
    def scalar(v):
        return OrderExpr('local', 'i64', v)
    def view(v):
        return OrderExpr('view', 'slice', v)
    def current():
        return OrderExpr('local', 'slice', 's')
    def at(receiver, i):
        return OrderExpr('index', 'i64', args=(receiver, i))
    def set_(name, expr):
        return OrderStatement('assign', name=name, expr=expr)
    def print_(expr):
        return OrderStatement('print', expr=expr)
    def effect(body, result):
        return OrderExpr('effect', result.type, args=(result,), body=tuple(body))
    body = []
    for _ in range(rng.randint(4, 10)):
        kind = rng.randrange(6)
        value = literal(rng.randint(-20, 20))
        result = literal(rng.randint(-5, 5))
        j = literal(rng.randrange(n))
        root = rng.choice(('a', 'b'))
        if kind == 0:
            change = effect((set_('x', value), set_('y', scalar('x'))), result)
            expr = OrderExpr(rng.choice(('+', '-', '*')), 'i64', args=(scalar('x'), change))
            shape = (print_(expr), OrderStatement('add', name='x', expr=change))
        elif kind == 1:
            change = effect((set_('x', value),), literal(bool(rng.randrange(2))))
            expr = OrderExpr(rng.choice(('&&', '||')), 'bool', args=(OrderExpr('local', 'bool', 'flag'), change))
            shape = (print_(expr), set_('flag', OrderExpr('!', 'bool', args=(OrderExpr('local', 'bool', 'flag'),))))
        elif kind == 2:
            target = at(view(root), scalar('i'))
            change = effect((set_('i', j), OrderStatement('store', target=at(view(root), literal(0)), expr=value)), result)
            shape = (set_('i', literal(0)), OrderStatement('add', target=target, expr=change))
        elif kind == 3:
            change = effect((set_('s', view(root)),), j)
            shape = (print_(at(current(), change)),)
        elif kind == 4:
            lo = rng.randrange(n)
            hi = rng.randint(lo + 1, n)
            change = effect((set_('i', j), set_('s', view(root))), literal(hi))
            sliced = OrderExpr('slice', 'slice', args=(current(), scalar('i'), change))
            shape = (set_('i', literal(lo)), print_(at(sliced, literal(0))))
        else:
            change = effect((OrderStatement('store', target=at(current(), literal(0)), expr=value), set_('s', view(root))), result)
            call = OrderExpr('observe', 'i64', args=(at(current(), literal(0)), current(), change))
            shape = (print_(call),)
        if rng.randrange(3) == 0:
            body.append(OrderStatement('repeat', count=rng.randint(1, 3), body=shape))
        else:
            body.extend(shape)
    body.extend(print_(scalar(v)) for v in ('x', 'y', 'i'))
    body.append(print_(OrderExpr('local', 'bool', 'flag')))
    body.append(print_(OrderExpr('len', 'i64', args=(current(),))))
    for root in ('a', 'b'):
        body.extend(print_(at(view(root), literal(i))) for i in range(n))
    program = OrderProgram((OrderLocal('x', 'i64', rng.randint(-10, 10)), OrderLocal('y', 'i64', 0),
                            OrderLocal('i', 'i64', 0), OrderLocal('flag', 'bool', bool(rng.randrange(2)))),
                           tuple(OrderArray(root, tuple(rng.randint(-12, 12) for _ in range(n))) for root in ('a', 'b')),
                           (OrderSlice('s', 'a', 0, n),), tuple(body))
    validate(program)
    return program


def reductions(program: OrderProgram) -> Iterator[OrderProgram]:
    """Shrink effects and expressions while retaining their typed contracts."""
    validate(program)
    def expressions(e):
        if e.type in ('i64', 'bool'):
            zero = OrderExpr('literal', e.type, False if e.type == 'bool' else 0)
            if e != zero:
                yield zero
        for a in e.args:
            if a.type == e.type:
                yield a
        for i, a in enumerate(e.args):
            for smaller in expressions(a):
                yield replace(e, args=e.args[:i] + (smaller,) + e.args[i + 1:])
        for smaller in blocks(e.body):
            yield replace(e, body=smaller)
    def blocks(body):
        for i, s in enumerate(body):
            yield body[:i] + body[i + 1:]
            if s.op == 'repeat':
                yield body[:i] + s.body + body[i + 1:]
                if s.count:
                    yield body[:i] + (replace(s, count=0),) + body[i + 1:]
            for field in ('expr', 'target'):
                e = getattr(s, field)
                if e is not None:
                    for smaller in expressions(e):
                        yield body[:i] + (replace(s, **{field: smaller}),) + body[i + 1:]
            for smaller in blocks(s.body):
                yield body[:i] + (replace(s, body=smaller),) + body[i + 1:]
    seen = {program}
    for body in blocks(program.body):
        candidate = replace(program, body=body)
        if candidate in seen:
            continue
        seen.add(candidate)
        try:
            validate(candidate)
        except ValueError:
            continue
        yield candidate
