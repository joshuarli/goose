"""Closed, terminating Goose programs with an independent integer/boolean oracle."""

from dataclasses import dataclass, replace
import random
import re
from typing import Iterator, Literal

Type = Literal['i64', 'bool']
MIN_I64 = -(1 << 63)
MAX_I64 = (1 << 63) - 1
RESERVED_NAMES = frozenset(('import namespace struct enum type fn thread_fn export simd recursive let var extern const pad reusable if else while for in loop block guard match return break continue as true false null self bool varint i8 i16 i32 i64 u8 u16 u32 u64 f32 f64 print main').split())


@dataclass(frozen=True)
class Expr:
    op: str
    type: Type
    value: int | bool | str | None = None
    args: tuple['Expr', ...] = ()


@dataclass(frozen=True)
class Local:
    name: str
    type: Type
    value: int | bool


@dataclass(frozen=True)
class Statement:
    op: str
    name: str | None = None
    expr: Expr | None = None
    count: int | None = None
    body: tuple['Statement', ...] = ()
    otherwise: tuple['Statement', ...] = ()


@dataclass(frozen=True)
class Program:
    locals: tuple[Local, ...]
    body: tuple[Statement, ...]

    def to_dict(self) -> dict:
        validate(self)
        def expression(expr):
            return {'op': expr.op, 'type': expr.type, 'value': expr.value, 'args': [expression(arg) for arg in expr.args]}
        def statement(stmt):
            return {'op': stmt.op, 'name': stmt.name, 'expr': None if stmt.expr is None else expression(stmt.expr), 'count': stmt.count, 'body': [statement(child) for child in stmt.body], 'otherwise': [statement(child) for child in stmt.otherwise]}
        return {'version': 1, 'lane': 'scalar', 'expectation': 'MustCompileAndReturn', 'locals': [{'name': local.name, 'type': local.type, 'value': local.value} for local in self.locals], 'body': [statement(stmt) for stmt in self.body]}

    @classmethod
    def from_dict(cls, recipe: dict) -> 'Program':
        def fields(value, names):
            if type(value) is not dict or set(value) != set(names):
                raise ValueError('invalid recipe fields')
        def items(value):
            if type(value) is not list or len(value) > 64:
                raise ValueError('invalid recipe list')
            return value
        nodes = 0
        def expression(value, depth=0):
            nonlocal nodes
            nodes += 1
            if depth > 6 or nodes > 512:
                raise ValueError('recipe expression budget exceeded')
            fields(value, ('op', 'type', 'value', 'args'))
            return Expr(value['op'], value['type'], value['value'], tuple(expression(arg, depth + 1) for arg in items(value['args'])))
        def statement(value, depth=0):
            nonlocal nodes
            nodes += 1
            if depth > 4 or nodes > 512:
                raise ValueError('recipe statement budget exceeded')
            fields(value, ('op', 'name', 'expr', 'count', 'body', 'otherwise'))
            return Statement(value['op'], value['name'], None if value['expr'] is None else expression(value['expr']), value['count'], tuple(statement(child, depth + 1) for child in items(value['body'])), tuple(statement(child, depth + 1) for child in items(value['otherwise'])))
        fields(recipe, ('version', 'lane', 'expectation', 'locals', 'body'))
        if type(recipe['version']) is not int or recipe['version'] != 1 or recipe['lane'] != 'scalar' or recipe['expectation'] != 'MustCompileAndReturn':
            raise ValueError('unsupported recipe contract')
        locals = []
        for value in items(recipe['locals']):
            fields(value, ('name', 'type', 'value'))
            locals.append(Local(value['name'], value['type'], value['value']))
        result = cls(tuple(locals), tuple(statement(value) for value in items(recipe['body'])))
        validate(result)
        return result


def validate(program: Program) -> None:
    """Prove every arithmetic intermediate fits i64, including untaken branches."""
    env = {}
    nodes = 0
    steps = 0
    def checked(type, lo, hi):
        if type not in ('i64', 'bool') or lo < MIN_I64 or hi > MAX_I64:
            raise ValueError('invalid type or possible i64 overflow')
        return type, lo, hi
    if type(program.locals) is not tuple or type(program.body) is not tuple or len(program.locals) > 16:
        raise ValueError('invalid program shape')
    for local in program.locals:
        if not isinstance(local, Local) or type(local.name) is not str or re.fullmatch(r'[a-z][a-z0-9_]*', local.name) is None or local.name in env or local.name.startswith('fuzz_') or local.name in RESERVED_NAMES:
            raise ValueError('invalid local name')
        if local.type not in ('i64', 'bool') or type(local.value) is not (int if local.type == 'i64' else bool):
            raise ValueError('invalid local literal')
        env[local.name] = checked(local.type, int(local.value), int(local.value))
    def expression(expr, scope, depth=0):
        nonlocal nodes
        nodes += 1
        if not isinstance(expr, Expr) or depth > 6 or nodes > 100000 or type(expr.args) is not tuple:
            raise ValueError('invalid expression shape or budget')
        if expr.op == 'literal':
            if expr.args or expr.type not in ('i64', 'bool') or type(expr.value) is not (int if expr.type == 'i64' else bool):
                raise ValueError('invalid expression literal')
            result = checked(expr.type, int(expr.value), int(expr.value))
        elif expr.op == 'local':
            if expr.args or type(expr.value) is not str or expr.value not in scope:
                raise ValueError('unknown local')
            result = scope[expr.value]
        else:
            signatures = {'+': ('i64', 'i64', 2), '-': ('i64', 'i64', 2), '*': ('i64', 'i64', 2), '<': ('i64', 'bool', 2), '==': ('i64', 'bool', 2), '&&': ('bool', 'bool', 2), '||': ('bool', 'bool', 2), '!': ('bool', 'bool', 1), 'double': ('i64', 'i64', 1)}
            if type(expr.op) is not str or expr.op not in signatures or expr.value is not None:
                raise ValueError('unknown expression operator')
            argument_type, result_type, arity = signatures[expr.op]
            if len(expr.args) != arity:
                raise ValueError('invalid expression arity')
            args = [expression(arg, scope, depth + 1) for arg in expr.args]
            if any(arg[0] != argument_type for arg in args):
                raise ValueError('invalid expression operand type')
            lo, hi = args[0][1:]
            if expr.op == '+':
                lo, hi = lo + args[1][1], hi + args[1][2]
            elif expr.op == '-':
                lo, hi = lo - args[1][2], hi - args[1][1]
            elif expr.op == '*':
                products = [a * b for a in (lo, hi) for b in args[1][1:]]
                lo, hi = min(products), max(products)
            elif expr.op == 'double':
                lo, hi = lo * 2, hi * 2
            else:
                lo, hi = 0, 1
            result = checked(result_type, lo, hi)
        if expr.type != result[0]:
            raise ValueError('expression result type mismatch')
        return result
    def block(body, scope, depth=0):
        nonlocal steps
        if type(body) is not tuple or len(body) > 64 or depth > 4:
            raise ValueError('invalid statement block')
        for stmt in body:
            steps += 1
            if steps > 10000 or not isinstance(stmt, Statement):
                raise ValueError('statement budget exceeded')
            if stmt.op in ('assign', 'print'):
                if stmt.count is not None or stmt.body or stmt.otherwise or stmt.expr is None:
                    raise ValueError('invalid scalar statement')
                value = expression(stmt.expr, scope)
                if stmt.op == 'assign':
                    if type(stmt.name) is not str or stmt.name not in scope or scope[stmt.name][0] != value[0]:
                        raise ValueError('assignment type or target mismatch')
                    scope[stmt.name] = value
                elif stmt.name is not None:
                    raise ValueError('invalid print target')
            elif stmt.op == 'if':
                if stmt.name is not None or stmt.count is not None or stmt.expr is None or expression(stmt.expr, scope)[0] != 'bool':
                    raise ValueError('invalid conditional')
                left, right = scope.copy(), scope.copy()
                block(stmt.body, left, depth + 1)
                block(stmt.otherwise, right, depth + 1)
                for name in scope:
                    scope[name] = checked(scope[name][0], min(left[name][1], right[name][1]), max(left[name][2], right[name][2]))
            elif stmt.op == 'repeat':
                if stmt.name is not None or stmt.expr is not None or stmt.otherwise or type(stmt.count) is not int or not 0 <= stmt.count <= 8:
                    raise ValueError('invalid bounded loop')
                # Even a zero-trip body must be well typed and safe to render.
                probe = scope.copy()
                block(stmt.body, probe, depth + 1)
                for _ in range(stmt.count):
                    block(stmt.body, scope, depth + 1)
            else:
                raise ValueError('unknown statement operator')
    block(program.body, env)


def evaluate(program: Program) -> bytes:
    validate(program)
    env = {local.name: local.value for local in program.locals}
    output = []
    def expression(expr):
        if expr.op == 'literal':
            return expr.value
        if expr.op == 'local':
            return env[expr.value]
        a = expression(expr.args[0])
        if expr.op == '!':
            return not a
        if expr.op == 'double':
            return a + a
        if expr.op == '&&':
            return a and expression(expr.args[1])
        if expr.op == '||':
            return a or expression(expr.args[1])
        b = expression(expr.args[1])
        if expr.op == '+':
            return a + b
        if expr.op == '-':
            return a - b
        if expr.op == '*':
            return a * b
        if expr.op == '<':
            return a < b
        return a == b
    def block(body):
        for stmt in body:
            if stmt.op == 'assign':
                env[stmt.name] = expression(stmt.expr)
            elif stmt.op == 'print':
                value = expression(stmt.expr)
                output.append(('true' if value else 'false') if type(value) is bool else str(value))
            elif stmt.op == 'if':
                block(stmt.body if expression(stmt.expr) else stmt.otherwise)
            else:
                for _ in range(stmt.count):
                    block(stmt.body)
    block(program.body)
    return ''.join(line + '\n' for line in output).encode('ascii')


def render(program: Program) -> str:
    validate(program)
    def expression(expr):
        if expr.op == 'literal':
            if expr.type == 'bool':
                return 'true' if expr.value else 'false'
            return f'({expr.value})'
        if expr.op == 'local':
            return expr.value
        if expr.op == 'double':
            return f'fuzz_double({expression(expr.args[0])})'
        if expr.op == '!':
            return f'(!{expression(expr.args[0])})'
        return f'({expression(expr.args[0])} {expr.op} {expression(expr.args[1])})'
    lines = ['import std;', '', 'fn fuzz_double(x: i64) -> i64 { x + x }', '', 'fn main() {']
    for local in program.locals:
        lines.append(f'    var {local.name}: {local.type} = {expression(Expr("literal", local.type, local.value))};')
    loop_id = 0
    def block(body, indent):
        nonlocal loop_id
        pad = '    ' * indent
        for stmt in body:
            if stmt.op == 'assign':
                lines.append(f'{pad}{stmt.name} = {expression(stmt.expr)};')
            elif stmt.op == 'print':
                lines.append(f'{pad}print({expression(stmt.expr)});')
            elif stmt.op == 'if':
                lines.append(f'{pad}if {expression(stmt.expr)} {{')
                block(stmt.body, indent + 1)
                lines.append(f'{pad}}} else {{')
                block(stmt.otherwise, indent + 1)
                lines.append(f'{pad}}}')
            else:
                loop_id += 1
                lines.append(f'{pad}for fuzz_loop_{loop_id} in 0..{stmt.count} {{')
                block(stmt.body, indent + 1)
                lines.append(f'{pad}}}')
    block(program.body, 1)
    return '\n'.join(lines + ['}', ''])


def generate(seed: int) -> Program:
    if type(seed) is not int or not 0 <= seed < 1 << 64:
        raise ValueError('seed must be an unsigned 64-bit integer')
    rng = random.Random(seed)
    x, y = Expr('local', 'i64', 'x'), Expr('local', 'i64', 'y')
    flag = Expr('local', 'bool', 'flag')
    def integer():
        return Expr('literal', 'i64', rng.randint(-12, 12))
    def arithmetic():
        return Expr(rng.choice(('+', '-', '*')), 'i64', args=(rng.choice((x, y, integer())), integer()))
    body = []
    for _ in range(rng.randint(2, 6)):
        choice = rng.randrange(4)
        if choice == 0:
            body.append(Statement('assign', name=rng.choice(('x', 'y')), expr=arithmetic()))
        elif choice == 1:
            body.append(Statement('if', expr=Expr(rng.choice(('<', '==')), 'bool', args=(x, y)), body=(Statement('assign', name='x', expr=arithmetic()),), otherwise=(Statement('assign', name='y', expr=arithmetic()),)))
        elif choice == 2:
            body.append(Statement('repeat', count=rng.randrange(5), body=(Statement('assign', name='x', expr=Expr('+', 'i64', args=(x, integer()))), Statement('assign', name='flag', expr=Expr('!', 'bool', args=(flag,))))))
        else:
            body.append(Statement('assign', name='y', expr=Expr('double', 'i64', args=(arithmetic(),))))
    body.extend(Statement('print', expr=expr) for expr in (x, y, flag, Expr('&&', 'bool', args=(flag, Expr('<', 'bool', args=(x, y))))))
    program = Program((Local('x', 'i64', rng.randint(-20, 20)), Local('y', 'i64', rng.randint(-20, 20)), Local('flag', 'bool', bool(rng.randrange(2)))), tuple(body))
    # Small constants, six updates, and at most four loop trips bound growth.
    validate(program)
    return program


def reductions(program: Program) -> Iterator[Program]:
    """Yield smaller typed recipes; the caller evaluates each candidate anew."""
    validate(program)
    def expressions(expr):
        if expr.op == 'literal':
            if expr.value != 0:
                yield Expr('literal', expr.type, False if expr.type == 'bool' else 0)
                if expr.type == 'i64' and abs(expr.value) > 1:
                    yield Expr('literal', 'i64', expr.value // 2)
        else:
            yield Expr('literal', expr.type, False if expr.type == 'bool' else 0)
            for arg in expr.args:
                if arg.type == expr.type:
                    yield arg
        for index, arg in enumerate(expr.args):
            for smaller in expressions(arg):
                yield replace(expr, args=expr.args[:index] + (smaller,) + expr.args[index + 1:])
    def blocks(body):
        for index, stmt in enumerate(body):
            yield body[:index] + body[index + 1:]
            if stmt.expr is not None:
                for expr in expressions(stmt.expr):
                    yield body[:index] + (replace(stmt, expr=expr),) + body[index + 1:]
            if stmt.op == 'if':
                yield body[:index] + stmt.body + body[index + 1:]
                yield body[:index] + stmt.otherwise + body[index + 1:]
            if stmt.op == 'repeat' and stmt.count:
                yield body[:index] + (replace(stmt, count=0),) + body[index + 1:]
                if stmt.count > 1:
                    yield body[:index] + (replace(stmt, count=stmt.count // 2),) + body[index + 1:]
            for field in ('body', 'otherwise'):
                for smaller in blocks(getattr(stmt, field)):
                    yield body[:index] + (replace(stmt, **{field: smaller}),) + body[index + 1:]
    seen = {program}
    candidates = (replace(program, body=body) for body in blocks(program.body))
    local_candidates = []
    for index, local in enumerate(program.locals):
        if local.value != 0:
            smaller = replace(local, value=False if local.type == 'bool' else 0)
            local_candidates.append(replace(program, locals=program.locals[:index] + (smaller,) + program.locals[index + 1:]))
    from itertools import chain
    for candidate in chain(candidates, local_candidates):
        if candidate in seen:
            continue
        seen.add(candidate)
        try:
            evaluate(candidate)
        except ValueError:
            # Deleting an update can expose a larger value to later arithmetic.
            continue
        yield candidate
