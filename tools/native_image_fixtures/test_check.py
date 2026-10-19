"""Fail-closed regression controls for the image evidence gate, not authority."""
import json
import re
import ast
import unittest
from pathlib import Path
import check
import render_lean_fixtures as render


class AuditControls(unittest.TestCase):
    def test_exact_reports(self):
        for output in ["'good' does not depend on any axioms\n",
                       "'good' depends on axioms: [propext,\n Quot.sound]\n"]:
            check.audit_reports(output, ['good'])

    def test_bad_reports(self):
        good = "'good' depends on axioms: [propext, Quot.sound]\n"
        for output in ['', good + good, good.replace('Quot.sound', 'sorryAx'),
                       good.replace('Quot.sound', 'Lean.ofReduceBool'),
                       good + "'extra' does not depend on any axioms\n",
                       good[:-2], 'success\n', good+'success\n']:
            with self.subTest(output=output), self.assertRaises(SystemExit):
                check.audit_reports(output, ['good'])

    def test_exact_pinned_inventories(self):
        for kind, path, count in [('model', 'Oak/NativeBitwiseImage.lean', 7),
                                  ('fixtures', 'NativeBitwiseImageFixtures.lean', 738)]:
            values = list(check.inventory((check.LEAN/path).read_text().splitlines()).values())
            self.assertEqual(len(values), count)
            check.require_inventory(kind, values)
            for changed in [[], values[:-1], values+[values[0]], list(reversed(values))]:
                with self.subTest(kind=kind), self.assertRaises(SystemExit):
                    check.require_inventory(kind, changed)

    def test_shard_preserves_exact_inputs_and_admission_dependency(self):
        lines = (check.LEAN/'NativeBitwiseImageFixtures.lean').read_text().splitlines()
        inv = check.inventory(lines)
        selected = {i for i, n in inv.items() if n == 'Oak.NativeBitwiseImageFixtures.arm64_mix_and.loaded'}
        source = check.fixture_source(lines, inv, selected)
        self.assertIn('def header : Bytes :=', source)
        self.assertIn('def suffix : Bytes :=', source)
        self.assertIn('def image : Bytes := header ++ (List.replicate 3976 0 ++ suffix)', source)
        self.assertIn('theorem admitted :', source)
        self.assertIn('theorem loaded :', source)
        self.assertNotIn('namespace riscv64_mix_and', source)

    def test_lossless_gap_precondition(self):
        data = bytes(range(120)) + bytes(3976) + b'payload'
        representation = render.image_literal(data)
        self.assertIn('List.replicate 3976 0', representation)
        for bad in [data[:4095]] + [data[:offset]+b'X'+data[offset+1:] for offset in [120, 121, 2048, 4095]]:
            with self.assertRaises(ValueError):
                render.image_literal(bad)

    def test_byte_literal_roundtrip(self):
        def decode(expression):
            parts = re.findall(r'List.replicate (\d+) 0|\[([^]]*)\]', expression)
            return b''.join(bytes(int(count)) if count else bytes(ast.literal_eval('['+values+']'))
                            for count, values in parts)
        for raw in [b'', bytes(range(256)), bytes(8000), b'abc'+bytes(3976)+bytes(range(256)),
                    bytes(range(120))+bytes(3976)+bytes(range(200))]:
            self.assertEqual(decode(render.literal(raw)), raw)
            self.assertEqual(render.expand_literal(render.literal(raw)), raw)
        raw = bytes(range(120))+bytes(3976)+bytes(range(200))
        self.assertEqual(decode(render.image_literal(raw)), raw)

    def test_input_pins_reject_silent_rewrite(self):
        lines = (check.LEAN/'NativeBitwiseImageFixtures.lean').read_text().splitlines()
        check.verify_inputs(lines)
        for old, new in [('def header : Bytes := ([127,', 'def header : Bytes := ([126,'),
                         ('def suffix : Bytes := ([3,', 'def suffix : Bytes := ([4,'),
                         ('def nameBytes : Bytes := ([109,', 'def nameBytes : Bytes := ([108,'),
                         ('def image : Bytes := header ++ (List.replicate 3976 0 ++ suffix)', 'def image : Bytes := header ++ (List.replicate 3976 1 ++ suffix)')]:
            changed = '\n'.join(lines).replace(old, new, 1).splitlines()
            with self.subTest(change=new), self.assertRaises(SystemExit):
                check.verify_inputs(changed)

    def test_statements_reject_weakened_claim(self):
        lines = (check.LEAN/'NativeBitwiseImageFixtures.lean').read_text().splitlines()
        inventory = check.inventory(lines)
        check.require_statements(lines, inventory, 'fixtures')
        index = next(iter(inventory))
        lines[index] = 'theorem admitted : True := by trivial'
        with self.assertRaises(SystemExit):
            check.require_statements(lines, inventory, 'fixtures')

    def test_fixed_image_inventory(self):
        pins = json.loads((Path(__file__).parent/'evidence.json').read_text())
        self.assertEqual(len(pins), 18)
        for target, size, maximum in [('arm64', 4648, 4896), ('riscv64', 4680, 4928)]:
            self.assertEqual(pins[f'{target}_mix_and']['length'], size)
            self.assertEqual(pins[f'{target}_max256_and']['length'], maximum)
            self.assertEqual(pins[f'{target}_over257_and']['length'], maximum)
            for op in ['and', 'or', 'xor']:
                self.assertEqual(len(pins[f'{target}_mix_{op}']['sha256']), 64)


if __name__ == '__main__':
    unittest.main()
