"""Reference aliasing, recursive guards, and required lifetime rejections."""

from dataclasses import dataclass, replace
import random
from typing import Iterator, Literal

from fuzz.expectation import RejectExpectation

Expectation = Literal['MustCompileAndReturn', 'MustReject']
ReferenceKind = Literal[
    'recursive_alias', 'recursive_slice_alias', 'return_local_reference',
    'store_short_reference', 'shrink_live_alias',
]

REJECTION_DIAGNOSTICS = {
    'return_local_reference': ('dies with this function',),
    'store_short_reference': ('does not outlive the destination',),
    'shrink_live_alias': ('cannot clear', 'still used'),
}


@dataclass(frozen=True)
class ReferenceProgram:
    kind: ReferenceKind
    expectation: Expectation
    values: tuple[int, ...] = ()
    p_index: int = 0
    q_index: int = 0
    depth: int = 0
    delta: int = 0
    guard: str = 'positive'
    threshold: int = 0
    recurse_p: str = 'p'
    recurse_q: str = 'q'
    mutate_before_guard: bool = True
    storage: str = 'array'
    readonly_p: bool = False
    bind_references: bool = False

    def to_dict(self) -> dict:
        validate(self)
        return {
            'version': 2,
            'lane': 'reference',
            'expectation': self.expectation,
            'kind': self.kind,
            'values': list(self.values),
            'p_index': self.p_index,
            'q_index': self.q_index,
            'depth': self.depth,
            'delta': self.delta,
            'guard': self.guard,
            'threshold': self.threshold,
            'recurse_p': self.recurse_p,
            'recurse_q': self.recurse_q,
            'mutate_before_guard': self.mutate_before_guard,
            'storage': self.storage,
            'readonly_p': self.readonly_p,
            'bind_references': self.bind_references,
        }

    @classmethod
    def from_dict(cls, recipe: dict) -> 'ReferenceProgram':
        fields = {
            'version', 'lane', 'expectation', 'kind', 'values', 'p_index',
            'q_index', 'depth', 'delta', 'guard', 'threshold', 'recurse_p',
            'recurse_q', 'mutate_before_guard', 'storage',
            'readonly_p', 'bind_references',
        }
        if type(recipe) is not dict or set(recipe) != fields:
            raise ValueError('invalid reference recipe fields')
        if (type(recipe['version']) is not int or recipe['version'] != 2
                or recipe['lane'] != 'reference'):
            raise ValueError('unsupported reference recipe contract')
        if type(recipe['values']) is not list or len(recipe['values']) > 8:
            raise ValueError('invalid reference values')
        program = cls(
            recipe['kind'], recipe['expectation'], tuple(recipe['values']),
            recipe['p_index'], recipe['q_index'], recipe['depth'],
            recipe['delta'], recipe['guard'], recipe['threshold'],
            recipe['recurse_p'], recipe['recurse_q'],
            recipe['mutate_before_guard'], recipe['storage'],
            recipe['readonly_p'], recipe['bind_references'])
        validate(program)
        return program


Program = ReferenceProgram


def _is_i64(value) -> bool:
    return type(value) is int and -(1 << 63) <= value < 1 << 63


def validate(program: ReferenceProgram) -> None:
    if not isinstance(program, ReferenceProgram):
        raise ValueError('invalid reference program')
    if program.kind in REJECTION_DIAGNOSTICS:
        if program.expectation != 'MustReject':
            raise ValueError('lifetime violation must require rejection')
        defaults = ReferenceProgram(program.kind, 'MustReject')
        if program != defaults:
            raise ValueError('rejection recipes do not carry execution fields')
        return
    if (program.kind not in ('recursive_alias', 'recursive_slice_alias')
            or program.expectation != 'MustCompileAndReturn'):
        raise ValueError('unknown reference program kind or expectation')
    if type(program.values) is not tuple or not 2 <= len(program.values) <= 8:
        raise ValueError('reference execution needs two to eight locations')
    if any(not _is_i64(value) for value in program.values):
        raise ValueError('reference value is outside i64')
    if (type(program.p_index) is not int or type(program.q_index) is not int
            or not 0 <= program.p_index < len(program.values)
            or not 0 <= program.q_index < len(program.values)):
        raise ValueError('reference index is outside storage')
    if type(program.depth) is not int or not 0 <= program.depth <= 8:
        raise ValueError('invalid recursion depth')
    if not _is_i64(program.delta) or not _is_i64(program.threshold):
        raise ValueError('invalid reference arithmetic value')
    if program.guard not in ('positive', 'equal', 'at_least'):
        raise ValueError('unknown reference guard')
    if program.recurse_p not in ('p', 'q') or program.recurse_q not in ('p', 'q'):
        raise ValueError('unknown recursive alias mapping')
    if (type(program.mutate_before_guard) is not bool
            or program.storage not in ('array', 'struct', 'locals')
            or type(program.readonly_p) is not bool
            or type(program.bind_references) is not bool):
        raise ValueError('invalid reference execution shape')
    if program.kind == 'recursive_slice_alias' and (
            program.storage != 'array' or program.bind_references):
        raise ValueError('slice aliases require array storage and direct slice arguments')
    if program.readonly_p and program.recurse_q == 'p':
        raise ValueError('a read-only reference cannot become the mutable recursive argument')
    _execute(program)


def _execute(program: ReferenceProgram) -> tuple[tuple[int, ...], int]:
    values = list(program.values)
    visits = 0

    def guard(value: int) -> bool:
        if program.guard == 'positive':
            return value > program.threshold
        if program.guard == 'equal':
            return value == program.threshold
        return value >= program.threshold

    def mutate(location: int) -> None:
        value = values[location] + program.delta
        if not _is_i64(value):
            raise ValueError('reference mutation can overflow i64')
        values[location] = value

    def descend(p: int, q: int, depth: int) -> None:
        nonlocal visits
        if program.mutate_before_guard:
            mutate(q)
        if guard(values[p]) and depth > 0:
            locations = {'p': p, 'q': q}
            descend(locations[program.recurse_p], locations[program.recurse_q], depth - 1)
        if not program.mutate_before_guard:
            mutate(q)
        visits += 1

    descend(program.p_index, program.q_index, program.depth)
    return tuple(values), visits


def evaluate(program: ReferenceProgram) -> bytes | RejectExpectation:
    validate(program)
    if program.expectation == 'MustReject':
        return RejectExpectation(REJECTION_DIAGNOSTICS[program.kind])
    values, visits = _execute(program)
    return ''.join(f'{value}\n' for value in (*values, visits)).encode('ascii')


def _rejection_source(kind: str) -> str:
    if kind == 'return_local_reference':
        return '''import std;

fn fuzz_bad() -> i64[:] {
    var fuzz_local: i64[1] = [42];
    return fuzz_local[..];
}

fn main() { print(fuzz_bad()[0]); }
'''
    if kind == 'store_short_reference':
        return '''import std;

var fuzz_saved: const u8[:] = "start";

fn fuzz_store() {
    var fuzz_local: u8[..8] = "local";
    fuzz_saved = fuzz_local;
}

fn main() { fuzz_store(); print(fuzz_saved); }
'''
    if kind == 'shrink_live_alias':
        return '''import std;

fn fuzz_shrink(fuzz_values: i64[>..]&, fuzz_alias: i64&) {
    fuzz_values.clear();
    print(fuzz_alias);
}

fn main() {
    var fuzz_values: i64[>..] = [7, 9];
    fuzz_shrink(fuzz_values, fuzz_values[0]);
}
'''
    raise ValueError('unknown rejection kind')


def render(program: ReferenceProgram) -> str:
    validate(program)
    if program.expectation == 'MustReject':
        return _rejection_source(program.kind)
    read = 'p[0]' if program.kind == 'recursive_slice_alias' else 'p'
    comparison = {
        'positive': f'{read} > {program.threshold}',
        'equal': f'{read} == {program.threshold}',
        'at_least': f'{read} >= {program.threshold}',
    }[program.guard]
    mutation = f'    {"q[0]" if program.kind == "recursive_slice_alias" else "q"} += {program.delta};'
    body = []
    if program.mutate_before_guard:
        body.append(mutation)
    body.extend([
        f'    if {comparison} && n > 0 {{',
        f'        fuzz_descend({program.recurse_p}, {program.recurse_q}, n - 1);',
        '    }',
    ])
    if not program.mutate_before_guard:
        body.append(mutation)
    body.append('    fuzz_visits += 1;')
    lines = ['import std;', '', 'var fuzz_visits = 0;', '']
    if program.storage == 'struct':
        fields = ', '.join(f'v{i}: i64' for i in range(len(program.values)))
        lines.extend([f'struct FuzzCells {{ {fields} }}', ''])
    if program.kind == 'recursive_slice_alias':
        p_type = 'const i64[:]' if program.readonly_p else 'i64[:]'
        signature = f'recursive fn fuzz_descend(p: {p_type}, q: i64[:], n: i64) {{'
    else:
        p_type = 'const i64&' if program.readonly_p else 'i64&'
        signature = f'recursive fn fuzz_descend(p: {p_type}, q: i64&, n: i64) {{'
    lines.extend([
        signature,
        *body,
        '}',
        '',
        'fn main() {',
    ])
    if program.storage == 'array':
        values = ', '.join(map(str, program.values))
        lines.append(f'    var fuzz_values: i64[{len(program.values)}] = [{values}];')
        paths = [f'fuzz_values[{index}]' for index in range(len(program.values))]
    elif program.storage == 'struct':
        values = ', '.join(f'v{i}: {value}' for i, value in enumerate(program.values))
        lines.append(f'    var fuzz_values = FuzzCells {{ {values} }};')
        paths = [f'fuzz_values.v{index}' for index in range(len(program.values))]
    else:
        for index, value in enumerate(program.values):
            lines.append(f'    var fuzz_v{index}: i64 = {value};')
        paths = [f'fuzz_v{index}' for index in range(len(program.values))]
    if program.kind == 'recursive_slice_alias':
        p = f'fuzz_values[{program.p_index}..{program.p_index + 1}]'
        q = f'fuzz_values[{program.q_index}..{program.q_index + 1}]'
    elif program.bind_references:
        initial = 0 if program.q_index != 0 else 1
        lines.extend([
            f'    var fuzz_p: {p_type} = {paths[program.p_index]};',
            f'    var fuzz_q: i64& = {paths[initial]};',
            f'    fuzz_q .= {paths[program.q_index]};',
        ])
        p, q = 'fuzz_p', 'fuzz_q'
    else:
        p, q = paths[program.p_index], paths[program.q_index]
    lines.append(f'    fuzz_descend({p}, {q}, {program.depth});')
    lines.extend(f'    print({path});' for path in paths)
    lines.extend(['    print(fuzz_visits);', '}', ''])
    return '\n'.join(lines)


def generate(seed: int) -> ReferenceProgram:
    if type(seed) is not int or not 0 <= seed < 1 << 64:
        raise ValueError('seed must be an unsigned 64-bit integer')
    if seed == 0:
        return ReferenceProgram(
            'recursive_alias', 'MustCompileAndReturn', (1, -1), 0, 1, 2, 1,
            'positive', 0, 'q', 'q', True, 'array')
    selector = seed % 10
    if selector >= 7:
        kind = tuple(REJECTION_DIAGNOSTICS)[selector - 7]
        return ReferenceProgram(kind, 'MustReject')
    rng = random.Random(seed)
    count = rng.randint(2, 5)
    values = tuple(rng.randint(-4, 4) for _ in range(count))
    kind = 'recursive_slice_alias' if selector == 6 else 'recursive_alias'
    storage = 'array' if kind == 'recursive_slice_alias' else rng.choice(('array', 'struct', 'locals'))
    program = ReferenceProgram(
        kind, 'MustCompileAndReturn', values,
        rng.randrange(count), rng.randrange(count), rng.randint(0, 5),
        rng.choice((-2, -1, 1, 2)), rng.choice(('positive', 'equal', 'at_least')),
        rng.randint(-2, 2), rng.choice(('p', 'q')), rng.choice(('p', 'q')),
        bool(rng.randrange(2)), storage, bool(rng.randrange(2)),
        kind == 'recursive_alias' and bool(rng.randrange(2)))
    if program.readonly_p and program.recurse_q == 'p':
        program = replace(program, recurse_q='q')
    validate(program)
    return program


def reductions(program: ReferenceProgram) -> Iterator[ReferenceProgram]:
    validate(program)
    if program.expectation == 'MustReject':
        return
    candidates = []
    if program.storage == 'struct':
        candidates.append(replace(program, storage='array'))
    if program.depth > 1:
        candidates.append(replace(program, depth=1))
    if abs(program.delta) > 1:
        candidates.append(replace(program, delta=1 if program.delta > 0 else -1))
    for index, value in enumerate(program.values):
        if value:
            values = program.values[:index] + (0,) + program.values[index + 1:]
            candidates.append(replace(program, values=values))
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
