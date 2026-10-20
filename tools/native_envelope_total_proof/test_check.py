"""Negative controls for the exact native-envelope total-outcome axiom/build gate."""
import importlib.util
from pathlib import Path
import tempfile
import unittest

SPEC = importlib.util.spec_from_file_location('native_envelope_check', Path(__file__).with_name('check.py'))
CHECK = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CHECK)


class AuditTests(unittest.TestCase):
    def test_standard_and_axiom_free(self):
        CHECK.audit_reports("'a' does not depend on any axioms\n'b' depends on axioms: [propext,\nQuot.sound, Classical.choice]\n", ('a', 'b'))

    def test_refusals(self):
        for text, names in (
            ("'a' depends on axioms: [sorryAx]\n", ('a',)),
            ("'a' depends on axioms: [Lean.ofReduceBool]\n", ('a',)),
            ("'a' depends on axioms: [Oak.BitwiseELFProducer.packed_read_octets._native.bv_decide.ax_1_5]\n", ('a',)),
            ("'a' depends on axioms: [assumedWriter]\n", ('a',)),
            ("'a' depends on axioms: []\n", ('a', 'missing')),
            ("'a' depends on axioms: []\n'a' depends on axioms: []\n", ('a',)),
            ("'unexpected' depends on axioms: []\n", ('a',)),
            ("warning\n'a' depends on axioms: []\n", ('a',)),
            ("'a' depends on axioms: []\ntrailing\n", ('a',)),
            ('', ()),
            ("'a' depends on axioms: []\n", ('a', 'a')),
        ):
            with self.subTest(text=text, names=names), self.assertRaises(ValueError):
                CHECK.audit_reports(text, names)

    def test_missing_local_import_refused(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / 'Oak').mkdir()
            (root / 'Oak' / 'Root.lean').write_text('import Oak.Missing\n')
            with self.assertRaisesRegex(ValueError, 'missing local source'):
                CHECK.dependency_order('Oak.Root', root)

    def test_current_source_closure(self):
        order = CHECK.dependency_order(CHECK.MODULE)
        self.assertEqual(order[-1][0], CHECK.MODULE)
        names = {name for name, _ in order}
        self.assertIn('Oak.NativeBitwiseEnvelopeExtracted', names)
        self.assertIn('Oak.NativeBitwiseEnvelopeProfile', names)
        self.assertIn('Oak.NativeBitwiseImage', names)
        self.assertIn('Oak.NativeBitwiseEnvelopeTotalSpec', names)
        self.assertIn('Oak.NativeBitwiseEnvelopeTotalPrimitives', names)
        self.assertIn('Oak.NativeBitwiseEnvelopeTotal', names)
        self.assertEqual(len(names), len(order))


if __name__ == '__main__':
    unittest.main()
