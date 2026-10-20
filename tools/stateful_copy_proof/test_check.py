"""Fail-closed controls for the stateful adapter proof gate."""
import importlib.util
from pathlib import Path
import re
import tempfile
import unittest

SPEC = importlib.util.spec_from_file_location('stateful_copy_check', Path(__file__).with_name('check.py'))
CHECK = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CHECK)


class StatefulCopyGateTests(unittest.TestCase):
    def test_exact_public_roots_and_committed_audit(self):
        expected = []
        for module in ('StatefulCopy', 'StatefulCopyControls'):
            source = (CHECK.SOURCE / 'Oak' / (module + '.lean')).read_text()
            names = re.findall(r'^(?:@\[simp\] )?theorem ([A-Za-z0-9_]+)', source, re.M)
            namespace = 'Oak.StatefulCopy.' + ('Controls.' if module.endswith('Controls') else '')
            expected.extend(namespace + name for name in names)
        self.assertEqual(tuple(expected), CHECK.THEOREMS)
        self.assertEqual((CHECK.SOURCE / 'Oak' / 'StatefulCopyAudit.lean').read_text(), CHECK.audit_source())

    def test_exact_fresh_source_closure(self):
        self.assertEqual([name for name, _ in CHECK.dependency_order(CHECK.MODULE, CHECK.SOURCE)], [
            'Oak.Stdlib.BytesExtracted', 'Oak.Stdlib.BytesLaws', 'Oak.ViewRefinement',
            'Oak.StatefulCopy', 'Oak.StatefulCopyControls'])

    def test_frozen_bindings_and_mutations(self):
        CHECK.check_bindings()
        self.assertEqual(len(CHECK.SOURCE_BINDINGS), 5)
        for rel, digest in CHECK.SOURCE_BINDINGS.items():
            with self.subTest(path=rel), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                path = root / rel
                path.parent.mkdir(parents=True)
                path.write_bytes((CHECK.ROOT / rel).read_bytes() + b'\n')
                with self.assertRaisesRegex(ValueError, 'binding changed'):
                    CHECK.check_bindings(root, {rel: digest})

    def test_axiom_reports_are_exact(self):
        valid = ''.join("'" + name + "' depends on axioms: [propext, Quot.sound, Classical.choice]\n"
                        for name in CHECK.THEOREMS)
        CHECK.audit_reports(valid, CHECK.THEOREMS)
        for bad in (valid.replace('propext', 'sorryAx', 1),
                    valid.replace('propext', 'Lean.ofReduceBool', 1),
                    valid.replace('propext', 'assumedCopy', 1),
                    '\n'.join(valid.splitlines()[1:]), valid + valid.splitlines()[0] + '\n',
                    'warning\n' + valid, valid + 'unexpected\n', ''):
            with self.subTest(output=bad[:90]), self.assertRaises(ValueError):
                CHECK.audit_reports(bad, CHECK.THEOREMS)


if __name__ == '__main__':
    unittest.main()
