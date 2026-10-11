"""Independent decimal cases for the standard library's parse_flt."""

from dataclasses import dataclass
import math
import random
import re
from typing import Iterator

DECIMAL = re.compile(r'[+-]?(?:(?:[0-9]+(?:\.[0-9]*)?)|(?:\.[0-9]+))(?:e[+-]?[0-9]+)?')
INPUT = re.compile(r'[+\-.0-9ex]+')
MAX_TEXT = 96


@dataclass(frozen=True)
class ParseFltProgram:
    text: str

    def to_dict(self) -> dict:
        validate(self)
        return {
            'version': 1,
            'lane': 'parse_flt',
            'expectation': 'MustCompileAndReturn',
            'text': self.text,
        }

    @classmethod
    def from_dict(cls, recipe: dict) -> 'ParseFltProgram':
        if type(recipe) is not dict or set(recipe) != {
                'version', 'lane', 'expectation', 'text'}:
            raise ValueError('invalid parse_flt recipe fields')
        if (type(recipe['version']) is not int or recipe['version'] != 1
                or recipe['lane'] != 'parse_flt'
                or recipe['expectation'] != 'MustCompileAndReturn'):
            raise ValueError('unsupported parse_flt recipe contract')
        program = cls(recipe['text'])
        validate(program)
        return program


Program = ParseFltProgram


def _expected(program: ParseFltProgram) -> tuple[bool, float]:
    valid = DECIMAL.fullmatch(program.text) is not None
    if not valid:
        return False, 0.0
    value = float(program.text)
    if not math.isfinite(value):
        raise ValueError('parse_flt model excludes overflow and non-finite values')
    return True, value


def validate(program: ParseFltProgram) -> None:
    if (not isinstance(program, ParseFltProgram) or type(program.text) is not str
            or not 1 <= len(program.text) <= MAX_TEXT
            or INPUT.fullmatch(program.text) is None):
        raise ValueError('parse_flt input is outside the closed decimal grammar')
    _expected(program)


def evaluate(program: ParseFltProgram) -> bytes:
    validate(program)
    return b'true\n'


def _literal(value: float) -> str:
    text = repr(value)
    if 'e' in text:
        mantissa, exponent = text.split('e')
        return f'{mantissa}e{int(exponent)}'
    return text


def render(program: ParseFltProgram) -> str:
    validate(program)
    valid, expected = _expected(program)
    lines = [
        'import std;',
        '',
        'fn main() {',
        f'    let fuzz_value, fuzz_ok = parse_flt("{program.text}");',
    ]
    if valid:
        lines.extend([
            f'    let fuzz_expected: f64 = {_literal(expected)};',
            '    var fuzz_matches = fuzz_ok && (fuzz_value == fuzz_expected ||',
            '        abs(fuzz_value - fuzz_expected) <= abs(fuzz_expected) * 1e-12 + 1e-300);',
        ])
        if expected == 0.0:
            lines.append('    fuzz_matches = fuzz_matches && '
                         '(1.0 / fuzz_value < 0.0) == (1.0 / fuzz_expected < 0.0);')
    else:
        lines.append('    let fuzz_matches = !fuzz_ok && fuzz_value == 0.0;')
    lines.extend(['    print(fuzz_matches);', '}', ''])
    return '\n'.join(lines)


def generate(seed: int) -> ParseFltProgram:
    if type(seed) is not int or not 0 <= seed < 1 << 64:
        raise ValueError('seed must be an unsigned 64-bit integer')
    if seed == 0:
        return ParseFltProgram('00000000000000000001')
    rng = random.Random(seed)
    zeroes = '0' * rng.randint(0, 40)
    sign = rng.choice(('', '', '-', '+'))
    digits = str(rng.randint(1, 999999))
    kind = seed % 7
    if kind == 0:
        text = sign + zeroes + digits
    elif kind == 1:
        text = sign + zeroes + digits + '.' + str(rng.randint(0, 9999))
    elif kind == 2:
        text = sign + ('0' * rng.randint(0, 20)) + '.' + zeroes + digits
    elif kind == 3:
        text = sign + zeroes + digits + 'e' + rng.choice(('', '+', '-')) + str(rng.randint(0, 12))
    elif kind == 4:
        text = sign + zeroes + '0.' + ('0' * rng.randint(0, 20)) + digits + 'e' + str(rng.randint(0, 12))
    elif kind == 5:
        text = sign + zeroes + digits + rng.choice(('x', 'e', 'e+'))
    else:
        text = rng.choice(('.', '+', '-', '.e1'))
    program = ParseFltProgram(text[:MAX_TEXT])
    validate(program)
    return program


def reductions(program: ParseFltProgram) -> Iterator[ParseFltProgram]:
    validate(program)
    candidates = []
    for index, char in enumerate(program.text):
        if char == '0' and len(program.text) > 1:
            candidates.append(ParseFltProgram(program.text[:index] + program.text[index + 1:]))
            break
    valid, _ = _expected(program)
    if valid and program.text not in ('0', '1'):
        candidates.append(ParseFltProgram('0'))
    seen = {program}
    for candidate in candidates:
        if candidate in seen:
            continue
        seen.add(candidate)
        try:
            validate(candidate)
        except ValueError:
            continue
        yield candidate
