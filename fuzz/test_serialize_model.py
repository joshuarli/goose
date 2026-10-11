import copy
import json
import unittest

from fuzz.serialize_model import (SerializeProgram, evaluate, generate,
                                  reductions, render)


class SerializeModelTests(unittest.TestCase):
    def test_valid_links_round_trip(self):
        # Two 9-byte nodes. The first reference field is at payload offset 1
        # and points to the second element at offset 9.
        image = (18, 7, 8, 0, 0, 0, 0, 0, 0, 0,
                 11, 0, 0, 0, 0, 0, 0, 0, 0)
        program = SerializeProgram(image)
        self.assertEqual(evaluate(program), b'true\n2\n7079\ntrue\n')
        self.assertIn('from_bytes<FuzzNode[>..]>', render(program))

    def test_hostile_offsets_are_rejected(self):
        for offset in ((1 << 63) - 1, -(1 << 63), 1, 9, -9):
            raw = offset.to_bytes(8, 'little', signed=True)
            program = SerializeProgram((9, 9, *raw))
            self.assertEqual(evaluate(program), b'false\n0\n0\nfalse\n')

    def test_mutated_payload_can_still_be_valid(self):
        original = generate(1)
        image = list(original.image)
        image[1] ^= 0xff
        mutated = SerializeProgram(tuple(image), original.shape)
        self.assertTrue(evaluate(mutated).startswith(b'true\n'))

    def test_relative_offset_widths_enums_limited_arrays_and_variable_fields(self):
        for shape in ('node_u8', 'node_u16', 'node_u32', 'node_u64',
                      'enum', 'limited', 'text'):
            matches = [generate(seed) for seed in range(1, 512)
                       if generate(seed).shape == shape]
            self.assertTrue(matches)
            source = render(matches[0])
            self.assertIn('from_bytes<', source)
            self.assertIn('to_bytes()', source)
        self.assertIn('enum FuzzChoice', render(SerializeProgram((0,), 'enum')))
        self.assertIn('u8[..3]', render(SerializeProgram((0,), 'limited')))
        self.assertIn('u8[varint]', render(SerializeProgram((0,), 'text')))

    def test_generation_roundtrips_and_reduces(self):
        outcomes = set()
        for seed in range(128):
            program = generate(seed)
            self.assertEqual(program, generate(seed))
            rebuilt = SerializeProgram.from_dict(json.loads(json.dumps(program.to_dict())))
            self.assertEqual(program, rebuilt)
            self.assertEqual(evaluate(program), evaluate(rebuilt))
            self.assertEqual(render(program), render(rebuilt))
            outcomes.add(evaluate(program).splitlines()[0])
            for candidate in reductions(program):
                self.assertNotEqual(candidate, program)
                evaluate(candidate)
                render(candidate)
        self.assertEqual(outcomes, {b'true', b'false'})

    def test_exact_overflow_calibration_is_seed_zero(self):
        self.assertEqual(generate(0).image,
                         (9, 9, 255, 255, 255, 255, 255, 255, 255, 127))

    def test_strict_recipe_validation(self):
        original = generate(0).to_dict()
        for key, value in (('lane', 'scalar'), ('version', True),
                           ('expectation', 'MustTrap'), ('source', 'fn main() {}')):
            recipe = copy.deepcopy(original)
            recipe[key] = value
            with self.assertRaises(ValueError):
                SerializeProgram.from_dict(recipe)
        for seed in (True, -1, 1 << 64):
            with self.assertRaises(ValueError):
                generate(seed)


if __name__ == '__main__':
    unittest.main()
