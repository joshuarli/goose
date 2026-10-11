"""Deterministic valid programs whose specified result is a Goose runtime trap."""

from dataclasses import dataclass
import random
from typing import Iterator, Literal

TrapKind = Literal[
    'division_zero', 'division_overflow', 'index_bounds', 'slice_bounds',
    'resize_negative', 'pop_empty', 'pop_n_past_end', 'pop_n_negative',
    'capacity', 'evaluation_order',
]

TRAP_DIAGNOSTICS = {
    'division_zero': ('division by zero',),
    'division_overflow': ('integer overflow in division',),
    'index_bounds': ('index 2 out of bounds (length 2)',),
    'slice_bounds': ('slice bounds out of range',),
    'resize_negative': ('resize to a negative length',),
    'pop_empty': ('pop on empty array',),
    'pop_n_past_end': ("pop_n count negative or beyond the array's length",),
    'pop_n_negative': ("pop_n count negative or beyond the array's length",),
    'capacity': ('limited array capacity exceeded',),
    'evaluation_order': ('division by zero',),
}

TRAP_KINDS = tuple(TRAP_DIAGNOSTICS)
MAX_PREFIX = 8


@dataclass(frozen=True)
class TrapExpectation:
    """Observable output before the trap and stable diagnostic fragments."""

    stdout_prefix: bytes
    stderr_contains: tuple[str, ...]


@dataclass(frozen=True)
class TrapProgram:
    kind: TrapKind
    prefix: tuple[int, ...] = ()

    def to_dict(self) -> dict:
        validate(self)
        return {
            'version': 1,
            'lane': 'trap',
            'expectation': 'MustTrap',
            'kind': self.kind,
            'prefix': list(self.prefix),
        }

    @classmethod
    def from_dict(cls, recipe: dict) -> 'TrapProgram':
        if type(recipe) is not dict or set(recipe) != {
                'version', 'lane', 'expectation', 'kind', 'prefix'}:
            raise ValueError('invalid trap recipe fields')
        if (type(recipe['version']) is not int or recipe['version'] != 1
                or recipe['lane'] != 'trap' or recipe['expectation'] != 'MustTrap'):
            raise ValueError('unsupported trap recipe contract')
        prefix = recipe['prefix']
        if type(prefix) is not list or len(prefix) > MAX_PREFIX:
            raise ValueError('invalid trap prefix')
        program = cls(recipe['kind'], tuple(prefix))
        validate(program)
        return program


# Semantic lanes expose the same names as the return-valued program models.
Program = TrapProgram


def validate(program: TrapProgram) -> None:
    if not isinstance(program, TrapProgram) or program.kind not in TRAP_DIAGNOSTICS:
        raise ValueError('unknown trap program kind')
    if type(program.prefix) is not tuple or len(program.prefix) > MAX_PREFIX:
        raise ValueError('invalid trap prefix')
    if any(type(value) is not int or not -32 <= value <= 32 for value in program.prefix):
        raise ValueError('trap prefix values must be small integers')


def generate(seed: int) -> TrapProgram:
    """Choose one trap contract and a short observable prefix."""
    if type(seed) is not int or not 0 <= seed < 1 << 64:
        raise ValueError('seed must be an unsigned 64-bit integer')
    rng = random.Random(seed)
    kind = rng.choice(TRAP_KINDS)
    prefix = tuple(rng.randint(-8, 8) for _ in range(rng.randrange(0, 4)))
    return TrapProgram(kind, prefix)


def evaluate(program: TrapProgram) -> TrapExpectation:
    validate(program)
    prefix = ''.join(f'{value}\n' for value in program.prefix).encode('ascii')
    if program.kind == 'evaluation_order':
        # The two helper calls are the left and right operands. Goose evaluates
        # operands left to right, so both prints precede division-by-zero.
        prefix += b'41\n0\n'
    return TrapExpectation(prefix, TRAP_DIAGNOSTICS[program.kind])


def _trap_body(kind: str) -> list[str]:
    if kind == 'division_zero':
        return ['    var fuzz_divisor: i64 = 0;', '    print(19 / fuzz_divisor);']
    if kind == 'division_overflow':
        return ['    var fuzz_minimum: i64 = -9223372036854775807 - 1;',
                '    print(fuzz_minimum / -1);']
    if kind == 'index_bounds':
        return ['    var fuzz_values: i64[>..<] = [3, 5];',
                '    var fuzz_index: i64 = 2;',
                '    print(fuzz_values[fuzz_index]);']
    if kind == 'slice_bounds':
        return ['    var fuzz_values: i64[>..<] = [3, 5];',
                '    print(fuzz_values[0..fuzz_high()].len);']
    if kind == 'resize_negative':
        return ['    var fuzz_values: i64[>..<] = [3];',
                '    var fuzz_size: i64 = -1;',
                '    fuzz_values.resize(fuzz_size);']
    if kind == 'pop_empty':
        return ['    var fuzz_values: i64[>..<] = [];',
                '    print(fuzz_values.pop());']
    if kind == 'pop_n_past_end':
        return ['    var fuzz_values: i64[>..<] = [3];',
                '    fuzz_values.pop_n(2);']
    if kind == 'pop_n_negative':
        return ['    var fuzz_values: i64[>..<] = [3];',
                '    var fuzz_count: i64 = -1;',
                '    fuzz_values.pop_n(fuzz_count);']
    if kind == 'capacity':
        return ['    var fuzz_values: i64[..1] = [3];',
                '    fuzz_values.push(5);']
    if kind == 'evaluation_order':
        return ['    print(fuzz_left() / fuzz_right());']
    raise ValueError('unknown trap program kind')


def render(program: TrapProgram) -> str:
    validate(program)
    lines = ['import std;', '']
    if program.kind == 'slice_bounds':
        lines.extend(['fn fuzz_high() -> i64 { return 3; }', ''])
    elif program.kind == 'evaluation_order':
        lines.extend([
            'fn fuzz_left() -> i64 { print(41); return 1; }',
            'fn fuzz_right() -> i64 { print(0); return 0; }',
            '',
        ])
    lines.extend(['fn main() {'])
    lines.extend(f'    print({value});' for value in program.prefix)
    lines.extend(_trap_body(program.kind))
    lines.extend(['}', ''])
    return '\n'.join(lines)


def reductions(program: TrapProgram) -> Iterator[TrapProgram]:
    """Remove prior output and simplify values while preserving the trap kind."""
    validate(program)
    if program.prefix:
        for keep in range(len(program.prefix) - 1, -1, -1):
            yield TrapProgram(program.kind, program.prefix[:keep])
        for index, value in enumerate(program.prefix):
            if value:
                prefix = list(program.prefix)
                prefix[index] = 0
                yield TrapProgram(program.kind, tuple(prefix))
