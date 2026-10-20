import copy
import importlib.util
import json
import os
from pathlib import Path
import unittest
from unittest.mock import patch

SPEC = importlib.util.spec_from_file_location('raw_copy_gate', Path(__file__).with_name('check.py'))
gate = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(gate)


class GateControls(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        # The equipped parent supplies its *fresh* ordinary checked artifact.
        # Missing inputs are a failure, not a skip or a stale-snapshot fallback.
        cls.generated = Path(os.environ['OAK_RAW_GATE_TEST_GENERATED']).read_text()
        cls.export = json.loads(Path(os.environ['OAK_RAW_GATE_TEST_JSON']).read_text())

    def test_fresh_full_reification(self):
        self.assertTrue(gate.validate_export(self.generated, self.export).is_absolute())

    def test_reification_changes_fail(self):
        for before, after in [
            ('code := "memory.byte-store"', 'code := "memory.region-store"'),
            ('code := "compare.less"', 'code := "compare.equal"'),
            ('value := "bytes__copy_uinto"', 'value := "counterfeit"'),
            ('value := "Result_u32_bytes__CopyError.Ok"', 'value := "Result_u32_bytes__CopyError.Err"'),
            ('effects := ["Memory.Write", "Control.Trap"]', 'effects := []'),
            ('operands := [6, 3]', 'operands := [6, 6]'),
        ]:
            with self.subTest(before=before):
                self.assertIn(before, self.generated)
                with self.assertRaises(ValueError):
                    gate.validate_export(self.generated.replace(before, after, 1), self.export)

    def test_missing_custody_data_fails(self):
        with self.assertRaises((ValueError, KeyError)):
            gate.validate_export(self.generated.replace('def custodyJSON', 'def missing'), self.export)

    def test_changed_full_artifact_fails(self):
        for field in ('Types', 'Accesses', 'Calls', 'ProjectedAccesses', 'Sources', 'IndexProofs'):
            changed = copy.deepcopy(self.export)
            changed[field] = []
            with self.subTest(field=field), self.assertRaises(ValueError):
                gate.validate_export(self.generated, changed)

    def test_unknown_closure_fails(self):
        changed = copy.deepcopy(self.export)
        changed['Functions'][0]['CFG']['Name'] = 'other'
        with self.assertRaises(ValueError):
            gate.validate_export(self.generated, changed)

    def test_changed_root_source_file_fails(self):
        original = Path.read_text
        root = Path(self.export['Sources'][1]['Path'])
        def read(path, *args, **kwargs):
            return 'changed' if path == root else original(path, *args, **kwargs)
        with patch.object(Path, 'read_text', read), self.assertRaises(ValueError):
            gate.validate_export(self.generated, self.export)

    def test_empty_inventory_refuses(self):
        with patch.object(gate, 'THEOREMS', ()), self.assertRaises(ValueError):
            gate.audit_source()


class ValidatorFailureControls(unittest.TestCase):
    def test_only_exact_false_acceptance_counts(self):
        diagnostics = "file/OptIRStatefulCopyValidation.lean:42:2: error: Tactic `decide` proved that the proposition is false\n"
        gate.require_validator_refusal(diagnostics, 1, {41, 42, 43})
        for changed, code, lines in (
                (diagnostics, 0, {42}),
                (diagnostics, -9, {42}),
                (diagnostics, 2, {42}),
                (diagnostics, 1, {40}),
                (diagnostics.replace('decide', 'simp'), 1, {42}),
                (diagnostics.replace('false', 'unknown'), 1, {42}),
                (diagnostics + 'other.lean:2:1: error: unrelated\n', 1, {42})):
            with self.subTest(diagnostics=changed, code=code, lines=lines), self.assertRaises(RuntimeError):
                gate.require_validator_refusal(changed, code, lines)

    def test_resources_and_imports_never_count(self):
        base = "OptIRStatefulCopyValidation.lean:42:2: error: decide false\n"
        for failure in ('heartbeat', 'maxRecDepth', 'out of memory', 'timeout',
                        'unknown module prefix', 'object file', 'failed to open file',
                        'interrupted', 'maximum recursion', 'deep recursion'):
            with self.subTest(failure=failure), self.assertRaises(RuntimeError):
                gate.require_validator_refusal(base + failure, 1, {42})

    def test_acceptance_theorem_is_unique_and_named(self):
        source = "def checker := true\ntheorem generated_projection_accepted : checker = true := by\n  decide\ntheorem sound := True\n"
        self.assertEqual(gate.acceptance_lines(source), {2, 3})
        for changed in ('', source + source, source.replace('generated_projection_accepted', 'fake')):
            with self.subTest(source=changed), self.assertRaises(ValueError):
                gate.acceptance_lines(changed)


if __name__ == '__main__':
    unittest.main()
