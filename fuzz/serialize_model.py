"""Independent typed models for valid and hostile serialized byte images."""

from dataclasses import dataclass
import random
from typing import Iterator

SHAPES = ('node_u8', 'node_u16', 'node_u32', 'node_u64',
          'enum', 'limited', 'text')
MAX_IMAGE_SIZE = 128
DIGEST_MODULUS = 1_000_000_007


@dataclass(frozen=True)
class SerializeProgram:
    image: tuple[int, ...]
    shape: str = 'node_u64'

    def to_dict(self) -> dict:
        validate(self)
        return {
            'version': 2,
            'lane': 'serialize',
            'expectation': 'MustCompileAndReturn',
            'shape': self.shape,
            'image': list(self.image),
        }

    @classmethod
    def from_dict(cls, recipe: dict) -> 'SerializeProgram':
        if type(recipe) is not dict or set(recipe) != {
                'version', 'lane', 'expectation', 'shape', 'image'}:
            raise ValueError('invalid serialize recipe fields')
        if (type(recipe['version']) is not int or recipe['version'] != 2
                or recipe['lane'] != 'serialize'
                or recipe['expectation'] != 'MustCompileAndReturn'):
            raise ValueError('unsupported serialize recipe contract')
        if type(recipe['image']) is not list or len(recipe['image']) > MAX_IMAGE_SIZE:
            raise ValueError('invalid serialized image')
        program = cls(tuple(recipe['image']), recipe['shape'])
        validate(program)
        return program


Program = SerializeProgram


def validate(program: SerializeProgram) -> None:
    if (not isinstance(program, SerializeProgram) or program.shape not in SHAPES
            or type(program.image) is not tuple or len(program.image) > MAX_IMAGE_SIZE
            or any(type(byte) is not int or not 0 <= byte <= 255 for byte in program.image)):
        raise ValueError('serialized image is outside the closed typed model')


def _uleb(value: int) -> tuple[int, ...]:
    if type(value) is not int or value < 0:
        raise ValueError('ULEB value must be nonnegative')
    result = []
    while True:
        byte = value & 0x7f
        value >>= 7
        result.append(byte | (0x80 if value else 0))
        if not value:
            return tuple(result)


def _read_uleb(data: tuple[int, ...], cursor: int) -> tuple[int, int] | None:
    value = 0
    shift = 0
    for index in range(cursor, min(len(data), cursor + 10)):
        byte = data[index]
        payload = byte & 0x7f
        if shift == 63 and payload > 1:
            return None
        value |= payload << shift
        if byte < 0x80:
            return value, index + 1
        shift += 7
    return None


def _payload(image: tuple[int, ...]) -> tuple[int, ...] | None:
    prefix = _read_uleb(image, 0)
    if prefix is None:
        return None
    size, cursor = prefix
    rest = image[cursor:]
    return rest if size == len(rest) else None


def _node_width(shape: str) -> int:
    if shape.startswith('node_u'):
        return int(shape[6:]) // 8
    raise ValueError('shape is not a node')


def _decode(program: SerializeProgram) -> tuple[tuple, bool]:
    payload = _payload(program.image)
    if payload is None:
        return (), False
    if program.shape.startswith('node_'):
        width = _node_width(program.shape)
        element_size = width + 1
        if len(payload) % element_size:
            return (), False
        nodes = []
        for start in range(0, len(payload), element_size):
            field = start + 1
            offset = int.from_bytes(bytes(payload[field:field + width]), 'little', signed=True)
            target = None
            if offset:
                target = field + offset
                if not 0 <= target < len(payload) or target % element_size:
                    return (), False
            nodes.append((payload[start], target))
        return tuple(nodes), True
    if program.shape == 'enum':
        if len(payload) % 2:
            return (), False
        values = tuple((payload[index], payload[index + 1])
                       for index in range(0, len(payload), 2))
        return (values, True) if all(tag < 3 for tag, _ in values) else ((), False)
    if program.shape == 'limited':
        if len(payload) % 4:
            return (), False
        values = []
        for index in range(0, len(payload), 4):
            length = payload[index]
            if length > 3:
                return (), False
            values.append((length, tuple(payload[index + 1:index + 4])))
        return tuple(values), True
    values = []
    cursor = 0
    while cursor < len(payload):
        prefix = _read_uleb(payload, cursor)
        if prefix is None:
            return (), False
        length, cursor = prefix
        if length > len(payload) - cursor:
            return (), False
        values.append(tuple(payload[cursor:cursor + length]))
        cursor += length
    return tuple(values), True


def _payload_bytes(shape: str, values: tuple) -> tuple[int, ...]:
    payload = []
    if shape.startswith('node_'):
        width = _node_width(shape)
        element_size = width + 1
        for index, (tag, target) in enumerate(values):
            field = index * element_size + 1
            offset = 0 if target is None else target - field
            payload.append(tag)
            payload.extend(offset.to_bytes(width, 'little', signed=True))
    elif shape == 'enum':
        for tag, value in values:
            payload.extend((tag, value))
    elif shape == 'limited':
        for length, slots in values:
            payload.append(length)
            payload.extend(slots)
    else:
        for text in values:
            payload.extend(_uleb(len(text)))
            payload.extend(text)
    return tuple(payload)


def _canonical(shape: str, values: tuple) -> tuple[int, ...]:
    payload = _payload_bytes(shape, values)
    return (*_uleb(len(payload)), *payload)


def _digest(shape: str, values: tuple) -> int:
    digest = 0
    def mix(value):
        nonlocal digest
        digest = (digest * 31 + value) % DIGEST_MODULUS
    if shape.startswith('node_'):
        element_size = _node_width(shape) + 1
        for tag, target in values:
            mix(tag)
            if target is not None:
                mix(values[target // element_size][0])
    elif shape == 'enum':
        for tag, value in values:
            mix(tag)
            mix(value)
    elif shape == 'limited':
        for length, slots in values:
            mix(length)
            for value in slots[:length]:
                mix(value)
    else:
        for text in values:
            mix(len(text))
            for byte in text:
                mix(byte)
    return digest


def evaluate(program: SerializeProgram) -> bytes:
    validate(program)
    values, accepted = _decode(program)
    digest = _digest(program.shape, values) if accepted else 0
    canonical = accepted and _canonical(program.shape, values) == program.image
    return (f'{str(accepted).lower()}\n{len(values) if accepted else 0}\n'
            f'{digest}\n{str(canonical).lower()}\n').encode('ascii')


def _goose_type(shape: str) -> tuple[list[str], str, list[str]]:
    if shape.startswith('node_'):
        width = shape[5:]
        declarations = [f'struct FuzzNode {{ tag: u8, next: FuzzNode&<{width}>? }}']
        digest = [
            '        for &fuzz_node in fuzz_nodes {',
            '            fuzz_digest = (fuzz_digest * 31 + fuzz_node.tag) % 1000000007;',
            '            let fuzz_next = fuzz_node.next;',
            '            if fuzz_next { fuzz_digest = (fuzz_digest * 31 + fuzz_next.tag) % 1000000007; }',
            '        }',
        ]
        return declarations, 'FuzzNode', digest
    if shape == 'enum':
        declarations = ['enum FuzzChoice { A { value: u8 }, B { value: u8 }, C { value: u8 } }']
        digest = [
            '        for &fuzz_choice in fuzz_nodes {',
            '            match fuzz_choice {',
            '                A fuzz_value => { fuzz_digest = (fuzz_digest * 31) % 1000000007; fuzz_digest = (fuzz_digest * 31 + fuzz_value.value) % 1000000007; },',
            '                B fuzz_value => { fuzz_digest = (fuzz_digest * 31 + 1) % 1000000007; fuzz_digest = (fuzz_digest * 31 + fuzz_value.value) % 1000000007; },',
            '                C fuzz_value => { fuzz_digest = (fuzz_digest * 31 + 2) % 1000000007; fuzz_digest = (fuzz_digest * 31 + fuzz_value.value) % 1000000007; },',
            '            }',
            '        }',
        ]
        return declarations, 'FuzzChoice', digest
    if shape == 'limited':
        declarations = ['struct FuzzBucket { items: u8[..3] }']
        digest = [
            '        for &fuzz_bucket in fuzz_nodes {',
            '            fuzz_digest = (fuzz_digest * 31 + fuzz_bucket.items.len) % 1000000007;',
            '            for &fuzz_item in fuzz_bucket.items {',
            '                fuzz_digest = (fuzz_digest * 31 + fuzz_item) % 1000000007;',
            '            }',
            '        }',
        ]
        return declarations, 'FuzzBucket', digest
    declarations = ['struct FuzzText { bytes: u8[varint] }']
    digest = [
        '        for &fuzz_text in fuzz_nodes {',
        '            fuzz_digest = (fuzz_digest * 31 + fuzz_text.bytes.len) % 1000000007;',
        '            for &fuzz_byte in fuzz_text.bytes {',
        '                fuzz_digest = (fuzz_digest * 31 + fuzz_byte) % 1000000007;',
        '            }',
        '        }',
    ]
    return declarations, 'FuzzText', digest


def render(program: SerializeProgram) -> str:
    validate(program)
    declarations, element, digest = _goose_type(program.shape)
    image = ', '.join(map(str, program.image))
    lines = [
        'import std;',
        '',
        *declarations,
        '',
        'fn main() {',
        f'    let fuzz_image: u8[{len(program.image)}] = [{image}];',
        f'    let fuzz_nodes, fuzz_ok = from_bytes<{element}[>..]>(fuzz_image);',
        '    var fuzz_digest: i64 = 0;',
        '    if fuzz_ok {',
        *digest,
        '    }',
        '    var fuzz_same = false;',
        '    if fuzz_ok {',
        '        let fuzz_encoded = fuzz_nodes.to_bytes();',
        '        fuzz_same = fuzz_encoded.len == fuzz_image.len;',
        '        if fuzz_same {',
        '            for fuzz_byte, fuzz_index in fuzz_encoded {',
        '                if fuzz_byte != fuzz_image[fuzz_index] { fuzz_same = false; }',
        '            }',
        '        }',
        '    }',
        '    print(fuzz_ok);',
        '    print(fuzz_nodes.len);',
        '    print(fuzz_digest);',
        '    print(fuzz_same);',
        '}',
        '',
    ]
    return '\n'.join(lines)


def _valid_values(shape: str, rng: random.Random) -> tuple:
    count = rng.randint(1, 5)
    if shape.startswith('node_'):
        element_size = _node_width(shape) + 1
        return tuple((rng.randrange(32), None if rng.randrange(3) == 0
                      else rng.randrange(count) * element_size)
                     for _ in range(count))
    if shape == 'enum':
        return tuple((rng.randrange(3), rng.randrange(32)) for _ in range(count))
    if shape == 'limited':
        return tuple((rng.randrange(4), tuple(rng.randrange(32) for _ in range(3)))
                     for _ in range(count))
    return tuple(tuple(rng.randrange(32, 127) for _ in range(rng.randrange(0, 8)))
                 for _ in range(count))


def generate(seed: int) -> SerializeProgram:
    if type(seed) is not int or not 0 <= seed < 1 << 64:
        raise ValueError('seed must be an unsigned 64-bit integer')
    if seed == 0:
        # The reference field contains INT64_MAX. Adding it to field offset 1
        # must be bounded before arithmetic can overflow.
        return SerializeProgram(
            (9, 9, 255, 255, 255, 255, 255, 255, 255, 127), 'node_u64')
    rng = random.Random(seed)
    shape = SHAPES[seed % len(SHAPES)]
    image = list(_canonical(shape, _valid_values(shape, rng)))
    mutation = (seed // len(SHAPES)) % 8
    if mutation == 0:
        pass
    elif mutation == 1:
        image[-1] ^= rng.randrange(1, 32)  # Often valid data, sometimes structural.
    elif mutation == 2:
        image.pop()
    elif mutation == 3:
        image.append(rng.randrange(256))
    elif mutation == 4:
        image[0] = (image[0] + 1) & 0x7f
    elif shape.startswith('node_'):
        width = _node_width(shape)
        value = (1 if mutation == 5 else -(1 << (width * 8 - 1))
                 if mutation == 6 else (1 << (width * 8 - 1)) - 1)
        image[2:2 + width] = value.to_bytes(width, 'little', signed=True)
    elif shape == 'enum':
        image[1] = 9
    elif shape == 'limited':
        image[1] = 4
    else:
        image[1] = 127 if mutation != 7 else 0x80
    program = SerializeProgram(tuple(image), shape)
    validate(program)
    return program


def reductions(program: SerializeProgram) -> Iterator[SerializeProgram]:
    validate(program)
    seen = {program}
    candidates = []
    for index, byte in enumerate(program.image):
        if byte:
            image = program.image[:index] + (0,) + program.image[index + 1:]
            candidates.append(SerializeProgram(image, program.shape))
    if program.image:
        candidates.append(SerializeProgram(program.image[:-1], program.shape))
    for candidate in candidates:
        if candidate in seen:
            continue
        seen.add(candidate)
        validate(candidate)
        yield candidate
