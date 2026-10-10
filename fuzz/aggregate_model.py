"""Closed integer elementwise programs over arrays and nested structs."""

from dataclasses import dataclass, replace
import random
import re
from typing import Iterator

from fuzz.numeric_model import bounds, normalize, signed, width

OPS = ('+', '-', '*', '/', '%')
SHAPES = ('array_u8', 'mixed_nested', 'uniform_nested')
RESERVED = frozenset('import namespace struct enum type fn thread_fn export simd recursive let var extern const pad reusable if else while for in loop block guard match return break continue as true false null self bool varint i8 i16 i32 i64 u8 u16 u32 u64 f32 f64 print main'.split())


@dataclass(frozen=True)
class Operation:
    op: str
    compound: bool
    scalar: int | None = None
    scalar_left: bool = False


@dataclass(frozen=True)
class Program:
    shape: str
    left: tuple[int, ...]
    right: tuple[int, ...]
    operations: tuple[Operation, ...]

    def to_dict(self) -> dict:
        validate(self)
        return {'version': 1, 'lane': 'aggregate', 'expectation': 'MustCompileAndReturn',
                'shape': self.shape, 'left': list(self.left), 'right': list(self.right),
                'operations': [{'op': x.op, 'compound': x.compound, 'scalar': x.scalar,
                                'scalar_left': x.scalar_left} for x in self.operations]}

    @classmethod
    def from_dict(cls, recipe: dict) -> 'Program':
        def fields(value, expected):
            if type(value) is not dict or set(value) != set(expected):
                raise ValueError('invalid aggregate recipe fields')
        fields(recipe, ('version', 'lane', 'expectation', 'shape', 'left', 'right', 'operations'))
        if (type(recipe['version']) is not int or recipe['version'] != 1
                or recipe['lane'] != 'aggregate' or recipe['expectation'] != 'MustCompileAndReturn'):
            raise ValueError('unsupported aggregate recipe contract')
        for key in ('left', 'right', 'operations'):
            if type(recipe[key]) is not list or len(recipe[key]) > 32:
                raise ValueError('invalid aggregate recipe list')
        ops = []
        for item in recipe['operations']:
            fields(item, ('op', 'compound', 'scalar', 'scalar_left'))
            ops.append(Operation(item['op'], item['compound'], item['scalar'], item['scalar_left']))
        program = cls(recipe['shape'], tuple(recipe['left']), tuple(recipe['right']), tuple(ops))
        validate(program)
        return program


def _leaf_types(shape: str) -> tuple[str, ...]:
    if shape == 'array_u8':
        return ('u8',) * 3
    if shape == 'mixed_nested':
        return ('i32', 'i8', 'i16', 'i16', 'i64')
    if shape == 'uniform_nested':
        return ('i32',) * 4
    raise ValueError('unknown aggregate shape')


def _homogeneous(leaf_types: tuple[str, ...]) -> str | None:
    return leaf_types[0] if leaf_types and all(x == leaf_types[0] for x in leaf_types) else None


def validate(program: Program) -> None:
    if not isinstance(program, Program) or program.shape not in SHAPES:
        raise ValueError('invalid aggregate program')
    types = _leaf_types(program.shape)
    if type(program.left) is not tuple or type(program.right) is not tuple or len(program.left) != len(types) or len(program.right) != len(types):
        raise ValueError('aggregate leaf count mismatch')
    for ty, *values in zip(types, program.left, program.right):
        lo, hi = bounds(ty)
        if any(type(v) is not int or not lo <= v <= hi for v in values):
            raise ValueError('aggregate leaf out of range')
    if type(program.operations) is not tuple or not 1 <= len(program.operations) <= 32:
        raise ValueError('invalid aggregate operations')
    uniform = _homogeneous(types)
    current = list(program.left)
    for item in program.operations:
        if not isinstance(item, Operation) or item.op not in OPS or type(item.compound) is not bool or type(item.scalar_left) is not bool:
            raise ValueError('invalid aggregate operation')
        if item.scalar is None:
            if item.scalar_left:
                raise ValueError('scalar side without scalar')
        else:
            if item.op not in ('*', '/') or uniform is None or type(item.scalar) is not int:
                raise ValueError('scalar form is not legal for this aggregate')
            lo, hi = bounds(uniform)
            if not lo <= item.scalar <= hi or item.scalar == 0 and item.op == '/':
                raise ValueError('invalid scalar operand')
            if item.compound and item.scalar_left:
                raise ValueError('compound scalar must be on the right')
        lhs = list(current if item.compound else program.left)
        rhs = [item.scalar] * len(types) if item.scalar is not None else list(program.right)
        if item.scalar_left and not item.compound:
            lhs, rhs = rhs, lhs
        result = []
        for ty, a, b in zip(types, lhs, rhs):
            if item.op in ('/', '%') and b == 0:
                raise ValueError('division by zero is excluded')
            if item.op == '/' and ty == 'i64' and a == -(1 << 63) and b == -1:
                raise ValueError('signed division overflow is excluded')
            if item.op == '+': raw = a + b
            elif item.op == '-': raw = a - b
            elif item.op == '*': raw = a * b
            elif item.op == '/': raw = abs(a) // abs(b) * (-1 if (a < 0) != (b < 0) else 1)
            else: raw = None
            if raw is not None and signed(ty):
                lo, hi = bounds(ty)
                if not lo <= raw <= hi:
                    raise ValueError('signed overflow is excluded')
            result.append(_apply(a, b, item.op, ty))
        if item.compound:
            current = result


def _apply(a: int, b: int, op: str, ty: str) -> int:
    if op == '+': return normalize(a + b, ty)
    if op == '-': return normalize(a - b, ty)
    if op == '*': return normalize(a * b, ty)
    if op == '/':
        q = abs(a) // abs(b) * (-1 if (a < 0) != (b < 0) else 1) if signed(ty) else a // b
        return normalize(q, ty)
    if op == '%':
        return normalize(a % abs(b) if signed(ty) else a % b, ty)
    raise ValueError('unknown aggregate operation')


def evaluate(program: Program) -> bytes:
    validate(program)
    types = _leaf_types(program.shape)
    current = list(program.left)
    output = []
    for item in program.operations:
        lhs = list(current if item.compound else program.left)
        if item.scalar is None:
            rhs = list(program.right)
        else:
            rhs = [item.scalar] * len(types)
        if item.scalar_left and not item.compound:
            lhs, rhs = rhs, lhs
        result = [_apply(a, b, item.op, ty) for a, b, ty in zip(lhs, rhs, types)]
        if item.compound:
            current = result
        output.extend(map(str, result))
    return ''.join(x + '\n' for x in output).encode('ascii')


def _parts(shape: str):
    if shape == 'array_u8': return ('u8[3]', [('index', 0), ('index', 1), ('index', 2)])
    if shape == 'mixed_nested':
        return ('FuzzOuter', [('field', 'head'), ('field', 'inner.small'), ('field', 'inner.row[0]'), ('field', 'inner.row[1]'), ('field', 'tail')])
    return ('FuzzOuter', [('field', 'rows[0].values[0]'), ('field', 'rows[0].values[1]'), ('field', 'rows[1].values[0]'), ('field', 'rows[1].values[1]')])


def _literal(shape: str, values: tuple[int, ...]) -> str:
    if shape == 'array_u8': return '[' + ', '.join(map(str, values)) + ']'
    if shape == 'mixed_nested':
        return f'FuzzOuter {{ {values[0]}, FuzzInner {{ {values[1]}, [{values[2]}, {values[3]}] }}, {values[4]} }}'
    return f'FuzzOuter {{ [FuzzRow {{ [{values[0]}, {values[1]}] }}, FuzzRow {{ [{values[2]}, {values[3]}] }}] }}'


def render(program: Program) -> str:
    validate(program)
    ty, paths = _parts(program.shape)
    lines = ['import std;', '']
    if program.shape == 'mixed_nested':
        lines += ['struct FuzzInner { small: i8, row: i16[2] }', 'struct FuzzOuter { head: i32, inner: FuzzInner, tail: i64 }', '']
    elif program.shape == 'uniform_nested':
        lines += ['struct FuzzRow { values: i32[2] }', 'struct FuzzOuter { rows: FuzzRow[2] }', '']
    lines += ['fn main() {', f'    let fuzz_left: {ty} = {_literal(program.shape, program.left)};',
              f'    let fuzz_right: {ty} = {_literal(program.shape, program.right)};',
              f'    var fuzz_mut: {ty} = {_literal(program.shape, program.left)};']
    def print_value(expr):
        for path in paths:
            field = path[1]
            lines.append(f'    print({expr}[{field}]);' if path[0] == 'index' else f'    print({expr}.{field});')
    for i, item in enumerate(program.operations):
        if item.scalar is None:
            rhs, lhs = 'fuzz_right', 'fuzz_left'
        else:
            scalar_ty = _homogeneous(_leaf_types(program.shape))
            lines.append(f'    let fuzz_scalar_{i}: {scalar_ty} = {item.scalar};')
            rhs, lhs = f'fuzz_scalar_{i}', 'fuzz_left'
        if item.compound:
            lines.append(f'    fuzz_mut {item.op}= {rhs};')
            print_value('fuzz_mut')
        else:
            if item.scalar is None:
                expr = f'(fuzz_left {item.op} fuzz_right)'
            elif item.scalar_left:
                expr = f'(fuzz_scalar_{i} {item.op} fuzz_left)'
            else:
                expr = f'(fuzz_left {item.op} fuzz_scalar_{i})'
            lines.append(f'    let fuzz_result_{i}: {ty} = {expr};')
            print_value(f'fuzz_result_{i}')
    return '\n'.join(lines + ['}', ''])


def generate(seed: int) -> Program:
    if type(seed) is not int or not 0 <= seed < 1 << 64:
        raise ValueError('seed must be an unsigned 64-bit integer')
    rng = random.Random(seed)
    shape = SHAPES[seed % len(SHAPES)]
    types = _leaf_types(shape)
    left, right = [], []
    for ty in types:
        lo, hi = bounds(ty)
        choices = (-3, -2, -1, 0, 1, 2, 3) if signed(ty) else (0, 1, 2, 3, hi, hi - 1)
        a = rng.choice(choices)
        b = rng.choice(choices)
        if b == 0: b = 1
        left.append(a); right.append(b)
    uniform = _homogeneous(types)
    ops = [Operation(op, compound=(index % 2 == 1)) for index, op in enumerate(('+', '-', '*', '/', '%'))]
    if uniform is not None:
        lo, hi = bounds(uniform)
        scalar = 2 if hi >= 2 else 1
        left = [value or 1 for value in left]
        ops.extend((Operation('*', False, scalar, bool(seed & 1)),
                    Operation('/', False, scalar, True), Operation('/', True, scalar)))
    program = Program(shape, tuple(left), tuple(right), tuple(ops))
    validate(program)
    evaluate(program)
    return program


def reductions(program: Program) -> Iterator[Program]:
    validate(program)
    seen = {program}
    candidates = []
    for values_name in ('left', 'right'):
        values = getattr(program, values_name)
        for i, value in enumerate(values):
            if value:
                updated = values[:i] + (0,) + values[i + 1:]
                candidates.append(replace(program, **{values_name: updated}))
    if len(program.operations) > 1:
        for i in range(len(program.operations)):
            candidates.append(replace(program, operations=program.operations[:i] + program.operations[i + 1:]))
    for candidate in candidates:
        if candidate in seen: continue
        seen.add(candidate)
        try: evaluate(candidate)
        except ValueError: continue
        yield candidate
