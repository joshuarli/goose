"""Closed Goose integer programs with a width-accurate modular oracle."""

from dataclasses import dataclass, replace
import random
import re
from typing import Iterator

TYPES = ('i8', 'i16', 'i32', 'i64', 'u8', 'u16', 'u32', 'u64')
RESERVED = frozenset('import namespace struct enum type fn thread_fn export simd recursive let var extern const pad reusable if else while for in loop block guard match return break continue as true false null self bool varint i8 i16 i32 i64 u8 u16 u32 u64 f32 f64 print main'.split())


def width(ty: str) -> int:
    if ty not in TYPES:
        raise ValueError('invalid integer type')
    return int(ty[1:])


def signed(ty: str) -> bool:
    if ty not in TYPES:
        raise ValueError('invalid integer type')
    return ty[0] == 'i'


def bounds(ty: str) -> tuple[int, int]:
    bits = width(ty)
    return (-(1 << (bits - 1)), (1 << (bits - 1)) - 1) if signed(ty) else (0, (1 << bits) - 1)


def normalize(value: int, ty: str) -> int:
    bits = width(ty)
    value &= (1 << bits) - 1
    if signed(ty) and value >= (1 << (bits - 1)):
        value -= 1 << bits
    return value


@dataclass(frozen=True)
class Expr:
    op: str
    type: str
    value: int | str | None = None
    args: tuple['Expr', ...] = ()


@dataclass(frozen=True)
class Program:
    locals: tuple[tuple[str, str, int], ...]
    outputs: tuple[Expr, ...]

    def to_dict(self) -> dict:
        validate(self)
        def encode(expr):
            return {'op': expr.op, 'type': expr.type, 'value': expr.value,
                    'args': [encode(arg) for arg in expr.args]}
        return {'version': 1, 'lane': 'numeric', 'expectation': 'MustCompileAndReturn',
                'locals': [{'name': name, 'type': ty, 'value': value}
                           for name, ty, value in self.locals],
                'outputs': [encode(expr) for expr in self.outputs]}

    @classmethod
    def from_dict(cls, recipe: dict) -> 'Program':
        def fields(value, names):
            if type(value) is not dict or set(value) != set(names):
                raise ValueError('invalid recipe fields')
        def expr(value, depth=0, budget=None):
            if budget is None:
                budget = [0]
            budget[0] += 1
            if depth > 8 or budget[0] > 1024:
                raise ValueError('recipe expression budget exceeded')
            fields(value, ('op', 'type', 'value', 'args'))
            if type(value['args']) is not list or len(value['args']) > 4:
                raise ValueError('invalid expression arguments')
            return Expr(value['op'], value['type'], value['value'],
                        tuple(expr(arg, depth + 1, budget) for arg in value['args']))
        fields(recipe, ('version', 'lane', 'expectation', 'locals', 'outputs'))
        if type(recipe['version']) is not int or recipe['version'] != 1 or recipe['lane'] != 'numeric' or recipe['expectation'] != 'MustCompileAndReturn':
            raise ValueError('unsupported recipe contract')
        if type(recipe['locals']) is not list or len(recipe['locals']) > 32 or type(recipe['outputs']) is not list or not 1 <= len(recipe['outputs']) <= 256:
            raise ValueError('invalid recipe lists')
        locals = []
        for item in recipe['locals']:
            fields(item, ('name', 'type', 'value'))
            locals.append((item['name'], item['type'], item['value']))
        program = cls(tuple(locals), tuple(expr(item) for item in recipe['outputs']))
        validate(program)
        return program


def validate(program: Program) -> None:
    if type(program.locals) is not tuple or type(program.outputs) is not tuple or not 1 <= len(program.outputs) <= 256:
        raise ValueError('invalid program shape')
    env = {}
    for name, ty, value in program.locals:
        if type(name) is not str or re.fullmatch(r'[a-z][a-z0-9_]*', name) is None or name in env or name in RESERVED or name.startswith('fuzz_'):
            raise ValueError('invalid local name')
        lo, hi = bounds(ty)
        if type(value) is not int or not lo <= value <= hi:
            raise ValueError('invalid local value')
        env[name] = ty
    nodes = [0]
    def check(expr, depth=0):
        nodes[0] += 1
        if not isinstance(expr, Expr) or depth > 8 or nodes[0] > 1024 or type(expr.args) is not tuple:
            raise ValueError('invalid expression shape or budget')
        ty = expr.type
        if expr.op == 'literal':
            if expr.args or (ty == 'bool' and type(expr.value) is not bool):
                raise ValueError('invalid integer literal')
            if ty != 'bool':
                if type(expr.value) is not int:
                    raise ValueError('invalid integer literal')
                lo, hi = bounds(ty)
                if not lo <= expr.value <= hi:
                    raise ValueError('integer literal out of range')
        elif expr.op == 'local':
            if expr.args or type(expr.value) is not str or env.get(expr.value) != ty:
                raise ValueError('unknown or mistyped local')
        elif expr.op == 'as!':
            if len(expr.args) != 1 or expr.value is not None:
                raise ValueError('invalid cast')
            width(ty)
            check(expr.args[0], depth + 1)
        elif expr.op in ('neg', '~'):
            if len(expr.args) != 1 or expr.value is not None or expr.args[0].type != ty or (expr.op == 'neg' and not signed(ty)):
                raise ValueError('invalid unary operation')
            check(expr.args[0], depth + 1)
        elif expr.op in ('+', '-', '*', '/', '%', '&', '|', '^', '<<', '>>', '==', '!=', '<', '<=', '>', '>='):
            if len(expr.args) != 2 or expr.value is not None:
                raise ValueError('invalid binary operation')
            left, right = expr.args
            check(left, depth + 1); check(right, depth + 1)
            if expr.op in ('==', '!=', '<', '<=', '>', '>='):
                if expr.type != 'bool' or left.type != right.type:
                    raise ValueError('invalid comparison')
            elif expr.op in ('<<', '>>'):
                if ty != left.type:
                    raise ValueError('invalid shift type')
            elif left.type != ty or right.type != ty:
                raise ValueError('invalid operand type')
            if expr.type != 'bool':
                width(expr.type)
        else:
            raise ValueError('unknown operation')
    for output in program.outputs:
        check(output)


def _eval(expr, env):
    if expr.op == 'literal': return expr.value
    if expr.op == 'local': return env[expr.value]
    if expr.op == 'as!': return normalize(_eval(expr.args[0], env), expr.type)
    a = _eval(expr.args[0], env)
    if expr.op == 'neg': return normalize(-a, expr.type)
    if expr.op == '~': return normalize(~a, expr.type)
    b = _eval(expr.args[1], env)
    op = expr.op
    if op in ('==', '!=', '<', '<=', '>', '>='):
        return {'==': a == b, '!=': a != b, '<': a < b, '<=': a <= b, '>': a > b, '>=': a >= b}[op]
    if op == '+': return normalize(a + b, expr.type)
    if op == '-': return normalize(a - b, expr.type)
    if op == '*': return normalize(a * b, expr.type)
    if op == '&': return normalize(a & b, expr.type)
    if op == '|': return normalize(a | b, expr.type)
    if op == '^': return normalize(a ^ b, expr.type)
    if op == '<<': return normalize(a << (b & (width(expr.type) - 1)), expr.type)
    if op == '>>': return normalize(a >> (b & (width(expr.type) - 1)), expr.type)
    if op == '/':
        if b == 0 or (expr.type == 'i64' and a == -(1 << 63) and b == -1):
            raise ValueError('generator produced a trapping division')
        quotient = abs(a) // abs(b) * (-1 if (a < 0) != (b < 0) else 1) if signed(expr.type) else a // b
        return normalize(quotient, expr.type)
    if op == '%':
        if b == 0: raise ValueError('generator produced a trapping remainder')
        return a % abs(b) if signed(expr.type) else a % b
    raise ValueError('unknown operation')


def evaluate(program: Program) -> bytes:
    validate(program)
    env = {name: value for name, _, value in program.locals}
    return ''.join((str(value) if type(value) is int else ('true' if value else 'false')) + '\n'
                   for value in (_eval(expr, env) for expr in program.outputs)).encode('ascii')


def render(program: Program) -> str:
    validate(program)
    literals = []
    def expression(expr):
        if expr.op == 'literal':
            name = f'fuzz_literal_{len(literals)}'
            literals.append((name, expr.type, expr.value))
            return name
        if expr.op == 'local': return expr.value
        if expr.op == 'as!': return f'({expression(expr.args[0])} as! {expr.type})'
        if expr.op == 'neg': return f'(-{expression(expr.args[0])})'
        if expr.op == '~': return f'(~{expression(expr.args[0])})'
        return f'({expression(expr.args[0])} {expr.op} {expression(expr.args[1])})'
    lines = ['import std;', '', 'fn main() {']
    for name, ty, value in program.locals:
        lines.append(f'    var {name}: {ty} = {value};')
    rendered = [expression(expr) for expr in program.outputs]
    for name, ty, value in literals:
        literal = ('true' if value else 'false') if ty == 'bool' else str(value)
        lines.append(f'    var {name}: {ty} = {literal};')
    for expr in rendered:
        lines.append(f'    print({expr});')
    return '\n'.join(lines + ['}', ''])


def generate(seed: int) -> Program:
    if type(seed) is not int or not 0 <= seed < 1 << 64:
        raise ValueError('seed must be an unsigned 64-bit integer')
    rng = random.Random(seed)
    locals = []
    variables = {}
    for i, ty in enumerate(TYPES):
        lo, hi = bounds(ty)
        value = rng.choice((lo, hi, 0, 1 if hi else 0, lo + 1, rng.randint(lo, hi)))
        name = f'n{i}'
        locals.append((name, ty, value))
        variables[ty] = Expr('local', ty, name)
    outputs = []
    for ty in TYPES:
        x = variables[ty]
        lo, hi = bounds(ty)
        divisor = Expr('literal', ty, rng.randint(1, max(1, min(hi, 127))))
        count = Expr('literal', 'u8', rng.randrange(0, 256))
        outputs.extend((
            Expr('+', ty, args=(x, Expr('literal', ty, 1 if hi else 0))),
            Expr('-', ty, args=(x, Expr('literal', ty, 1 if hi else 0))),
            Expr('*', ty, args=(x, Expr('literal', ty, 3 if hi >= 3 else 1))),
            Expr('%', ty, args=(x, divisor)),
            Expr('/', ty, args=(x, divisor)),
            Expr('<<', ty, args=(x, count)),
            Expr('>>', ty, args=(x, count)),
            Expr('~', ty, args=(x,)),
            Expr('as!', ty, args=(Expr('literal', 'u64', rng.getrandbits(64)),)),
            Expr('<', 'bool', args=(x, Expr('literal', ty, 0 if lo < 0 else 1))),
            Expr('==', 'bool', args=(x, x)),
        ))
        if signed(ty):
            outputs.append(Expr('%', ty, args=(Expr('literal', ty, lo), Expr('literal', ty, -1))))
            if ty != 'i64':
                outputs.append(Expr('/', ty, args=(Expr('literal', ty, lo), Expr('literal', ty, -1))))
    program = Program(tuple(locals), tuple(outputs))
    validate(program)
    evaluate(program)
    return program


def reductions(program: Program) -> Iterator[Program]:
    validate(program)
    seen = {program}
    candidates = []
    for i, (name, ty, value) in enumerate(program.locals):
        if value:
            locals = program.locals[:i] + ((name, ty, 0),) + program.locals[i + 1:]
            candidates.append(replace(program, locals=locals))
    for i, expr in enumerate(program.outputs):
        if expr.op not in ('literal', 'local'):
            candidates.append(replace(program, outputs=program.outputs[:i] + (expr.args[0],) + program.outputs[i + 1:]))
        zero = False if expr.type == 'bool' else 0
        candidates.append(replace(program, outputs=program.outputs[:i] + (Expr('literal', expr.type, zero),) + program.outputs[i + 1:]))
        if len(program.outputs) > 1:
            candidates.append(replace(program, outputs=program.outputs[:i] + program.outputs[i + 1:]))
    for candidate in candidates:
        if candidate in seen: continue
        seen.add(candidate)
        try: evaluate(candidate)
        except ValueError: continue
        yield candidate
