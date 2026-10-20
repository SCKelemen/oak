"""Cheap fail-closed unit tests; these do not assert a Sail kernel build."""
import importlib.util
import json
import os
import sys
import tempfile
from pathlib import Path
import unittest
from unittest.mock import patch

PATH = Path(__file__).with_name("strict-entry-audit.py")
spec = importlib.util.spec_from_file_location("strict_entry_audit", PATH)
audit = importlib.util.module_from_spec(spec)
spec.loader.exec_module(audit)
PURE_PATH = PATH.parent.parent / "lean/check-strict-image-entry-contract.py"
pure_spec = importlib.util.spec_from_file_location("pure_entry_diagnostic", PURE_PATH)
pure = importlib.util.module_from_spec(pure_spec)
pure_spec.loader.exec_module(pure)


class StrictEntryAuditTests(unittest.TestCase):
    def test_model_proof_inventory(self):
        audit.model_inventory()
        self.assertEqual(sum(map(len, audit.MODEL_ROOTS.values())), 13)
        self.assertEqual(len(audit.FIXTURE_PURE | audit.FIXTURE_EXECUTION), 48)
        self.assertEqual(len(audit.EXECUTION), 77)

    def test_execution_signature_is_unchanged(self):
        audit.require_execution_signatures()

    def test_model_execution_guard_rejects_added_premise(self):
        files = ("OakSailEntrySource.lean", "OakSailEntryChecks.lean",
                 "OakSailStrictImageEntryExecution.lean", "OakSailStrictImageEntryChecks.lean")
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            for file in files:
                (root / file).write_text((PATH.parent / file).read_text())
            for file in files[2:]:
                original = (root / file).read_text()
                (root / file).write_text(original.replace(
                    "(layout : OakSailImageLoad.ImageLayout image sp)",
                    "(layout : OakSailImageLoad.ImageLayout image sp) (extra : False)"))
                with patch.object(audit, "ROOT", root), self.assertRaisesRegex(RuntimeError, "Changed actual execution signature"):
                    audit.require_execution_signatures()
                (root / file).write_text(original)

    def test_fixture_execution_requires_exact_closed_application(self):
        source = "\n".join(
            f"noncomputable def execution_{op} :=\n"
            f"  OakSailStrictImageEntryChecks.initialized_strict_entry_clocked_prefix checked_{op} layout_{op}\n"
            for op in ("and", "or", "xor"))
        audit.require_fixture_execution(source)
        for mutated in (
            source.replace("execution_and :=", "execution_and (extra : False) :="),
            source.replace("execution_and :=", "execution_and (success : True) :="),
            source.replace("initialized_strict_entry_clocked_prefix checked_and", "unrelated_same_closure_theorem checked_and"),
            source.replace("checked_and layout_and", "checked_or layout_or"),
        ):
            with self.subTest(mutated=mutated), self.assertRaisesRegex(RuntimeError, "fixture execution application"):
                audit.require_fixture_execution(mutated)

    def test_version_pin_rejects_other_kernels(self):
        audit.require_version("Lean (version 4.29.0, release)")
        for version in ("Lean (version 4.33.1, release)", "Lean (version 4.29.1, release)", "", "4.29.0"):
            with self.subTest(version=version), self.assertRaises(RuntimeError):
                audit.require_version(version)

    def test_subprocess_uses_project_cwd_and_pin_despite_override(self):
        # Execute a real cheap subprocess, not a model or theorem stand-in.
        # The proof path is deliberately outside the selected project.
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            proof = base / "TemporaryProof.lean"
            proof.write_text("-- process-selection control only\n")
            for module, conflicting in ((audit, pure.TOOLCHAIN), (pure, audit.TOOLCHAIN)):
                root = base / module.TOOLCHAIN.rsplit(":", 1)[1]
                root.mkdir()
                (root / "lean-toolchain").write_text(module.TOOLCHAIN + "\n")
                with patch.object(module, "ROOT", root), patch.dict(os.environ, {"ELAN_TOOLCHAIN": conflicting}):
                    command = [sys.executable, "-c",
                               "import json, os, sys; print(json.dumps([os.getcwd(), os.environ['ELAN_TOOLCHAIN'], sys.argv[1]]))",
                               str(proof)]
                    result = module.run(command)
                    output = result.stdout if module is audit else result
                    self.assertEqual(json.loads(output), [str(root), module.TOOLCHAIN, str(proof)])
                    self.assertEqual(os.environ["ELAN_TOOLCHAIN"], conflicting)

    def test_changed_project_pin_is_rejected_before_subprocess(self):
        for module in (audit, pure):
            with tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                (root / "lean-toolchain").write_text("leanprover/lean4:v0.0.0\n")
                with patch.object(module, "ROOT", root), patch.object(module.subprocess, "run") as run:
                    with self.assertRaisesRegex(RuntimeError, "Unexpected .* project toolchain"):
                        module.run(["lake", "env", "lean", "--version"])
                    run.assert_not_called()

    def test_inventory_rejects_missing_extra_and_duplicate(self):
        audit.require_inventory("theorem a : True := True.intro\n", {"a"}, "test")
        for text in ("", "theorem b : True := True.intro\n",
                     "theorem a : True := True.intro\ntheorem a : True := True.intro\n",
                     "theorem a : True := True.intro\nprivate theorem helper : True := True.intro\n"):
            with self.subTest(text=text), self.assertRaises(RuntimeError):
                audit.require_inventory(text, {"a"}, "test")

    def test_axiom_report_inventory(self):
        good = "'a' depends on axioms: [propext, Quot.sound]\n'b' does not depend on any axioms\n"
        self.assertEqual(audit.parse_axioms(good, {"a", "b"}), {"a": {"propext", "Quot.sound"}, "b": set()})
        for text in ("", good + "'a' does not depend on any axioms\n", good + "'extra' does not depend on any axioms\n"):
            with self.subTest(text=text), self.assertRaises(RuntimeError):
                audit.parse_axioms(text, {"a", "b"})

    def test_external_closure_never_applies_to_pure_roots(self):
        actual = {audit.BASELINE: set(audit.EXECUTION), "pure": set(audit.STANDARD), "execution": set(audit.EXECUTION)}
        audit.validate_closures(actual, {"execution"})
        for axiom in ("sorryAx", "Lean.ofReduceBool", "valid_reservation"):
            changed = {**actual, "pure": set(audit.STANDARD) | {axiom}}
            with self.subTest(axiom=axiom), self.assertRaises(RuntimeError):
                audit.validate_closures(changed, {"execution"})

    def test_strict_admission_roots_retain_exact_standard_closure(self):
        root = "OakSailStrictImageEntry.strict_source_entry_admitted_of_layout"
        with self.assertRaises(RuntimeError):
            audit.validate_closures({audit.BASELINE: set(audit.EXECUTION), root: {"propext"}}, set())
        audit.validate_closures({audit.BASELINE: set(audit.EXECUTION), root: set(audit.STANDARD)}, set())

    def test_execution_requires_exact_baseline_not_subset(self):
        for baseline, execution in ((audit.EXECUTION, audit.STANDARD),
                                    (audit.EXECUTION, audit.EXECUTION | {"sorryAx"}),
                                    (audit.STANDARD, audit.STANDARD)):
            with self.subTest(baseline=baseline, execution=execution), self.assertRaises(RuntimeError):
                audit.validate_closures({audit.BASELINE: set(baseline), "execution": set(execution)}, {"execution"})


if __name__ == "__main__":
    unittest.main()
