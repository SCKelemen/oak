"""Fail-closed and coverage-preservation controls for the total proof gate."""
import importlib.util
from pathlib import Path
import unittest
from unittest.mock import patch

SPEC = importlib.util.spec_from_file_location('wasm_module_total_check', Path(__file__).with_name('check.py'))
CHECK = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CHECK)


class TotalGateTests(unittest.TestCase):
    def test_retains_exact_inventory_and_controls(self):
        audits = CHECK.checked_audits()
        self.assertEqual(audits[0], (CHECK.EXACT_AUDIT, CHECK.EXACT.MODULE, CHECK.EXACT.THEOREMS))
        self.assertEqual(audits[1], (CHECK.AUDIT, CHECK.MODULE, CHECK.THEOREMS))
        self.assertEqual(len(CHECK.EXACT.THEOREMS), 16)
        self.assertEqual(len(CHECK.THEOREMS), 10)
        self.assertTrue(CHECK.EXACT.CONTROLS.is_file())
        self.assertTrue(CHECK.CONTROLS.is_file())

    def test_superset_source_closure(self):
        order = CHECK.checked_order()
        names = [name for name, _ in order]
        previous = {name for name, _ in CHECK.EXACT.dependency_order(CHECK.EXACT.MODULE)}
        self.assertEqual(set(names), previous | {CHECK.MODULE})
        self.assertEqual(names[-1], CHECK.MODULE)
        self.assertEqual(len(names), 20)

    def test_lost_exact_dependency_refused(self):
        def dependency_order(module):
            if module == CHECK.MODULE:
                return [(CHECK.MODULE, CHECK.SOURCE / 'Oak/WasmBitwiseModuleTotal.lean')]
            return [(CHECK.EXACT.MODULE, CHECK.SOURCE / 'Oak/WasmBitwiseModuleExact.lean')]
        with patch.object(CHECK.EXACT, 'dependency_order', dependency_order):
            with self.assertRaisesRegex(RuntimeError, 'lost successful-domain'):
                CHECK.checked_order()

    def test_missing_or_changed_committed_inventory_refused(self):
        for target in (CHECK.AUDIT, CHECK.EXACT_AUDIT):
            original = Path.read_text
            for bad in ('', 'import Oak.WasmBitwiseModuleTotal\n#print axioms bogus\n'):
                def read_text(path, *args, **kwargs):
                    return bad if path == target else original(path, *args, **kwargs)
                with patch.object(Path, 'read_text', read_text):
                    with self.assertRaisesRegex(RuntimeError, 'differs from required roots'):
                        CHECK.checked_audits()

    def test_wrong_missing_duplicate_and_forbidden_roots_refused(self):
        for names in (CHECK.EXACT.THEOREMS, CHECK.THEOREMS):
            good = ''.join("'" + name + "' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
                           for name in names)
            CHECK.EXACT.audit_reports(good, names)
            for bad in (
                good.replace(names[0], 'Oak.Unexpected', 1),
                '\n'.join(good.splitlines()[1:]) + '\n',
                good + good.splitlines()[0] + '\n',
                good.replace('propext', 'sorryAx', 1),
                good.replace('propext', 'Lean.ofReduceBool', 1),
                good.replace('propext', 'assumedWriter', 1),
            ):
                with self.subTest(names=names, bad=bad), self.assertRaises(ValueError):
                    CHECK.EXACT.audit_reports(bad, names)

    def test_wrong_toolchain_refused(self):
        CHECK.require_version('Lean (version 4.33.1, x86_64-unknown-linux-gnu, commit release, Release)')
        for bad in ('', 'Lean (version 4.33.0, release)', 'Lean (version 4.33.10, release)',
                    'Lean (version 4.33.1-nightly, release)', 'other tool 4.33.1'):
            with self.subTest(version=bad), self.assertRaisesRegex(RuntimeError, 'pinned Lean 4.33.1'):
                CHECK.require_version(bad)


if __name__ == '__main__':
    unittest.main()
