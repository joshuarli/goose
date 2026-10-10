"""Closed Goose programs that exercise fixed-size elements in resizable arrays."""

from dataclasses import dataclass, replace
import random
from typing import Iterator, Literal

from fuzz.model import MAX_I64, MIN_I64, RESERVED_NAMES

ResizeOp = Literal['push', 'pop', 'pop_n', 'resize', 'append', 'clear',
                   'print_len', 'print_at', 'print_slice']
MAX_LENGTH = 12
MAX_VALUE = 32


@dataclass(frozen=True)
class ResizeStep:
    op: ResizeOp
    values: tuple[int, ...] = ()
    count: int | None = None
    fill: int | None = None
    lo: int | None = None
    hi: int | None = None


@dataclass(frozen=True)
class ResizeProgram:
    initial: tuple[int, ...]
    steps: tuple[ResizeStep, ...]

    def to_dict(self) -> dict:
        validate(self)
        return {
            'version': 1,
            'lane': 'resize',
            'expectation': 'MustCompileAndReturn',
            'initial': list(self.initial),
            'steps': [
                {'op': step.op, 'values': list(step.values), 'count': step.count,
                 'fill': step.fill, 'lo': step.lo, 'hi': step.hi}
                for step in self.steps
            ],
        }

    @classmethod
    def from_dict(cls, recipe: dict) -> 'ResizeProgram':
        def fields(value, keys):
            if type(value) is not dict or set(value) != set(keys):
                raise ValueError('invalid resize recipe fields')

        def integer_list(value):
            if type(value) is not list or len(value) > MAX_LENGTH:
                raise ValueError('invalid resize integer list')
            if any(type(item) is not int for item in value):
                raise ValueError('resize values must be integers')
            return tuple(value)

        fields(recipe, ('version', 'lane', 'expectation', 'initial', 'steps'))
        if (type(recipe['version']) is not int or recipe['version'] != 1
                or recipe['lane'] != 'resize'
                or recipe['expectation'] != 'MustCompileAndReturn'):
            raise ValueError('unsupported resize recipe contract')
        raw_steps = recipe['steps']
        if type(raw_steps) is not list or len(raw_steps) > 64:
            raise ValueError('invalid resize step list')
        steps = []
        for raw in raw_steps:
            fields(raw, ('op', 'values', 'count', 'fill', 'lo', 'hi'))
            steps.append(ResizeStep(raw['op'], integer_list(raw['values']), raw['count'],
                                    raw['fill'], raw['lo'], raw['hi']))
        program = cls(integer_list(recipe['initial']), tuple(steps))
        validate(program)
        return program


# The fuzz driver can call each semantic lane through the same names.
Program = ResizeProgram


def _check_int(value: object, what: str) -> int:
    if type(value) is not int or not MIN_I64 <= value <= MAX_I64:
        raise ValueError(f'invalid {what}')
    return value


def _apply(state: list[int], step: ResizeStep, output: list[str] | None = None) -> None:
    if step.op == 'push':
        state.append(step.values[0])
    elif step.op == 'pop':
        value = state.pop()
        if output is not None:
            output.append(str(value))
    elif step.op == 'pop_n':
        if step.count:
            del state[-step.count:]
    elif step.op == 'resize':
        count = step.count
        if count < len(state):
            del state[count:]
        else:
            state.extend([step.fill] * (count - len(state)))
    elif step.op == 'append':
        state.extend(step.values)
    elif step.op == 'clear':
        state.clear()
    elif step.op == 'print_len':
        if output is not None:
            output.append(str(len(state)))
    elif step.op == 'print_at':
        if output is not None:
            output.append(str(state[step.lo]))
    elif step.op == 'print_slice':
        if output is not None:
            output.append(str(step.hi - step.lo))
            output.extend(str(value) for value in state[step.lo:step.hi])
    else:
        raise ValueError('unknown resize operation')


def validate(program: ResizeProgram) -> None:
    """Prove each fixed index and slice bound against the state at that step."""
    if not isinstance(program, ResizeProgram):
        raise ValueError('invalid resize program')
    if type(program.initial) is not tuple or type(program.steps) is not tuple or len(program.steps) > 64:
        raise ValueError('invalid resize program shape')
    if len(program.initial) > MAX_LENGTH:
        raise ValueError('initial array exceeds size budget')
    state = []
    for value in program.initial:
        state.append(_check_int(value, 'initial array value'))
    for step in program.steps:
        if not isinstance(step, ResizeStep) or step.op not in (
                'push', 'pop', 'pop_n', 'resize', 'append', 'clear',
                'print_len', 'print_at', 'print_slice'):
            raise ValueError('invalid resize step')
        if type(step.values) is not tuple:
            raise ValueError('invalid resize values')
        if any(type(value) is not int or not -MAX_VALUE <= value <= MAX_VALUE for value in step.values):
            raise ValueError('resize values exceed the small literal range')
        if step.op == 'push':
            if len(step.values) != 1 or any(x is not None for x in (step.count, step.fill, step.lo, step.hi)):
                raise ValueError('invalid push step')
        elif step.op == 'pop':
            if step.values or any(x is not None for x in (step.count, step.fill, step.lo, step.hi)) or not state:
                raise ValueError('invalid pop step')
        elif step.op == 'pop_n':
            if (step.values or type(step.count) is not int or not 0 <= step.count <= len(state)
                    or any(x is not None for x in (step.fill, step.lo, step.hi))):
                raise ValueError('invalid pop_n step')
        elif step.op == 'resize':
            if step.values or type(step.count) is not int or not 0 <= step.count <= MAX_LENGTH or step.lo is not None or step.hi is not None:
                raise ValueError('invalid resize step')
            if step.count > len(state):
                if type(step.fill) is not int or not -MAX_VALUE <= step.fill <= MAX_VALUE:
                    raise ValueError('growing resize needs a small fill value')
            elif step.fill is not None:
                raise ValueError('shrinking resize cannot have a fill value')
        elif step.op == 'append':
            if not step.values or any(x is not None for x in (step.count, step.fill, step.lo, step.hi)):
                raise ValueError('invalid append step')
        elif step.op == 'clear':
            if step.values or any(x is not None for x in (step.count, step.fill, step.lo, step.hi)):
                raise ValueError('invalid clear step')
        elif step.op == 'print_len':
            if step.values or any(x is not None for x in (step.count, step.fill, step.lo, step.hi)):
                raise ValueError('invalid length observation')
        elif step.op == 'print_at':
            if (step.values or step.count is not None or step.fill is not None
                    or type(step.lo) is not int or step.hi is not None or not 0 <= step.lo < len(state)):
                raise ValueError('index is not proven in bounds')
        else:
            if (step.values or step.count is not None or step.fill is not None
                    or type(step.lo) is not int or type(step.hi) is not int
                    or not 0 <= step.lo <= step.hi <= len(state)):
                raise ValueError('slice is not proven in bounds')
        _apply(state, step)
        if len(state) > MAX_LENGTH:
            raise ValueError('resize execution exceeds length budget')


def evaluate(program: ResizeProgram) -> bytes:
    validate(program)
    state = list(program.initial)
    output = []
    for step in program.steps:
        _apply(state, step, output)
    return ''.join(line + '\n' for line in output).encode('ascii')


def render(program: ResizeProgram) -> str:
    validate(program)
    initial = ', '.join(f'({value})' for value in program.initial)
    lines = ['import std;', '', 'fn main() {', f'    var fuzz_values: i64[>..<] = [{initial}];']
    for step in program.steps:
        if step.op == 'push':
            lines.append(f'    fuzz_values.push(({step.values[0]}));')
        elif step.op == 'pop':
            lines.append('    print(fuzz_values.pop());')
        elif step.op == 'pop_n':
            lines.append(f'    fuzz_values.pop_n({step.count});')
        elif step.op == 'resize':
            if step.fill is None:
                lines.append(f'    fuzz_values.resize({step.count});')
            else:
                lines.append(f'    fuzz_values.resize({step.count}, ({step.fill}));')
        elif step.op == 'append':
            values = ', '.join(f'({value})' for value in step.values)
            lines.append(f'    fuzz_values.append([{values}]);')
        elif step.op == 'clear':
            lines.append('    fuzz_values.clear();')
        elif step.op == 'print_len':
            lines.append('    print(fuzz_values.len);')
        elif step.op == 'print_at':
            lines.append(f'    print(fuzz_values[{step.lo}]);')
        else:
            lines.append(f'    print(fuzz_values[{step.lo}..{step.hi}].len);')
            for index in range(step.lo, step.hi):
                lines.append(f'    print(fuzz_values[{index}]);')
    return '\n'.join(lines + ['}', ''])


def generate(seed: int) -> ResizeProgram:
    if type(seed) is not int or not 0 <= seed < 1 << 64:
        raise ValueError('seed must be an unsigned 64-bit integer')
    rng = random.Random(seed)
    initial = tuple(rng.randint(-8, 8) for _ in range(rng.randint(0, 4)))
    state = list(initial)
    steps = []
    for _ in range(rng.randint(12, 26)):
        choices = ['push', 'resize', 'append', 'print_len']
        if state:
            choices.extend(('pop', 'pop_n', 'clear', 'print_at', 'print_slice'))
        if len(state) >= MAX_LENGTH:
            choices = [choice for choice in choices if choice in (
                'pop', 'pop_n', 'resize', 'clear', 'print_len', 'print_at', 'print_slice')]
        op = rng.choice(choices)
        if op == 'push':
            step = ResizeStep('push', (rng.randint(-MAX_VALUE, MAX_VALUE),))
        elif op == 'pop':
            step = ResizeStep('pop')
        elif op == 'pop_n':
            step = ResizeStep('pop_n', count=rng.randrange(len(state) + 1))
        elif op == 'resize':
            count = rng.randint(0, min(MAX_LENGTH, len(state) + 3))
            fill = rng.randint(-MAX_VALUE, MAX_VALUE) if count > len(state) else None
            step = ResizeStep('resize', count=count, fill=fill)
        elif op == 'append':
            available = MAX_LENGTH - len(state)
            values = tuple(rng.randint(-MAX_VALUE, MAX_VALUE) for _ in range(rng.randint(1, min(3, available))))
            step = ResizeStep('append', values)
        elif op == 'clear':
            step = ResizeStep('clear')
        elif op == 'print_len':
            step = ResizeStep('print_len')
        elif op == 'print_at':
            step = ResizeStep('print_at', lo=rng.randrange(len(state)))
        else:
            lo = rng.randrange(len(state) + 1)
            hi = rng.randrange(lo, len(state) + 1)
            step = ResizeStep('print_slice', lo=lo, hi=hi)
        steps.append(step)
        _apply(state, step)
    program = ResizeProgram(initial, tuple(steps))
    validate(program)
    return program


def reductions(program: ResizeProgram) -> Iterator[ResizeProgram]:
    """Yield valid smaller operation sequences and smaller element literals."""
    validate(program)
    seen = {program}
    candidates = []
    for index in range(len(program.steps)):
        candidates.append(replace(program, steps=program.steps[:index] + program.steps[index + 1:]))
    for index, step in enumerate(program.steps):
        smaller_steps = []
        if step.op == 'push' and step.values[0] != 0:
            smaller_steps.append(replace(step, values=(0,)))
        elif step.op == 'append':
            if len(step.values) > 1:
                smaller_steps.append(replace(step, values=step.values[:1]))
            if any(step.values):
                smaller_steps.append(replace(step, values=tuple(0 for _ in step.values)))
        elif step.op == 'resize' and step.fill is not None and step.fill != 0:
            smaller_steps.append(replace(step, fill=0))
        elif step.op == 'pop_n' and step.count != 0:
            smaller_steps.append(replace(step, count=0))
        elif step.op == 'print_slice' and step.lo < step.hi:
            smaller_steps.append(replace(step, hi=step.lo))
        elif step.op == 'print_at' and step.lo != 0:
            smaller_steps.append(replace(step, lo=0))
        for smaller in smaller_steps:
            candidates.append(replace(program, steps=program.steps[:index] + (smaller,) + program.steps[index + 1:]))
    for index, value in enumerate(program.initial):
        if value:
            candidates.append(replace(program, initial=program.initial[:index] + (0,) + program.initial[index + 1:]))
    for candidate in candidates:
        if candidate in seen:
            continue
        seen.add(candidate)
        try:
            evaluate(candidate)
        except ValueError:
            continue
        yield candidate
