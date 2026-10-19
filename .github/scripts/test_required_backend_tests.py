"""Regression checks for equipped-lane selection and fail-closed reporting."""
import contextlib
import io
from pathlib import Path
import re
import unittest
from unittest.mock import MagicMock, patch

import required_backend_tests as required


class RequiredBackendTests(unittest.TestCase):
    def setUp(self):
        self.suite = required.Suite("./compiler", "10m", ("TestRequired", "TestRequired/Lean"))
        self.results = required.RequiredResults(self.suite)

    def event(self, action, name=""):
        return {"Action": action, "Package": self.suite.import_path, "Test": name}

    def passed(self, name):
        self.results.accept(self.event("run", name))
        self.results.accept(self.event("pass", name))

    def test_requires_every_named_root_and_child(self):
        self.passed("TestRequired")
        self.results.accept(self.event("pass"))
        with self.assertRaisesRegex(ValueError, "TestRequired/Lean"):
            self.results.finish(0)
        self.passed("TestRequired/Lean")
        self.results.finish(0)

    def test_rejects_nested_skips_even_under_passing_root(self):
        self.passed("TestRequired")
        self.passed("TestRequired/Lean")
        self.results.accept(self.event("run", "TestRequired/UnlistedChild"))
        self.results.accept(self.event("skip", "TestRequired/UnlistedChild"))
        self.results.accept(self.event("pass"))
        with self.assertRaisesRegex(ValueError, "UnlistedChild: skip"):
            self.results.finish(0)

    def test_rejects_test_and_package_failures(self):
        for name in ("", "TestRequired/Lean"):
            with self.subTest(name=name):
                results = required.RequiredResults(self.suite)
                if name:
                    results.accept(self.event("run", name))
                results.accept(self.event("fail", name))
                with self.assertRaisesRegex(ValueError, "fail"):
                    results.finish(0)

    def test_rejects_empty_truncated_and_process_failure(self):
        with self.assertRaisesRegex(ValueError, "required tests did not pass"):
            self.results.finish(0)
        self.passed("TestRequired")
        self.passed("TestRequired/Lean")
        with self.assertRaisesRegex(ValueError, "package did not pass"):
            self.results.finish(0)
        self.results.accept(self.event("pass"))
        with self.assertRaisesRegex(ValueError, "exited 7"):
            self.results.finish(7)
        self.results.accept(self.event("run", "TestRequired/Incomplete"))
        with self.assertRaisesRegex(ValueError, "did not finish"):
            self.results.finish(0)

    def test_rejects_wrong_package_selector_and_malformed_events(self):
        invalid = [
            None, [], {}, {"Action": "invented"},
            {**self.event("run", "TestRequired"), "Package": "wrong"},
            self.event("run", "TestUnrelated"), self.event("run", 7),
            {**self.event("output"), "Output": []},
            self.event("pass", "TestRequired"),
        ]
        for event in invalid:
            with self.subTest(event=event), self.assertRaises(ValueError):
                required.RequiredResults(self.suite).accept(event)

    def test_rejects_duplicate_test_run(self):
        self.results.accept(self.event("run", "TestRequired"))
        with self.assertRaisesRegex(ValueError, "duplicate"):
            self.results.accept(self.event("run", "TestRequired"))

    def test_exact_inventory_and_go_regex_arguments(self):
        with patch.object(required.subprocess, "check_output", return_value="TestRequired\nok package\n") as call:
            required.check_inventory(self.suite)
            self.assertEqual(call.call_args.args[0], ["go", "test", "./compiler", "-list", "^(TestRequired)$"])
        for inventory in ("", "ok package\n", "TestRenamed\n", "TestRequired\nTestExtra\n", "TestRequired\nTestRequired\n"):
            with self.subTest(inventory=inventory):
                with patch.object(required.subprocess, "check_output", return_value=inventory):
                    with self.assertRaises(ValueError):
                        required.check_inventory(self.suite)

    def test_runner_rejects_non_json_and_terminates_child(self):
        process = MagicMock()
        process.stdout = iter(["compiler error, not JSON\n"])
        process.__enter__.return_value = process
        with patch.object(required.subprocess, "Popen", return_value=process):
            with contextlib.redirect_stdout(io.StringIO()), self.assertRaisesRegex(ValueError, "invalid Go test JSON"):
                required.run_suite(self.suite)
        process.terminate.assert_called_once()
        process.wait.assert_called_once()

    def test_runner_preserves_test_timeout_and_process_failure(self):
        process = MagicMock()
        process.stdout = iter([])
        process.wait.return_value = 9
        process.__enter__.return_value = process
        with patch.object(required.subprocess, "Popen", return_value=process) as call:
            with contextlib.redirect_stdout(io.StringIO()), self.assertRaisesRegex(ValueError, "exited 9"):
                required.run_suite(self.suite)
        self.assertEqual(call.call_args.args[0], ["go", "test", "-json", "-count=1", "-timeout=10m", "./compiler", "-run", "^(TestRequired)$"])

    def test_cli_reports_inventory_process_and_output_errors(self):
        for error in (OSError("cannot launch"), UnicodeError("invalid output"), required.subprocess.CalledProcessError(2, ["go"])):
            with self.subTest(error=error), patch.object(required, "run_suite", side_effect=error):
                with contextlib.redirect_stderr(io.StringIO()):
                    self.assertEqual(required.main(["llvm"]), 1)

    def test_audited_suite_manifest(self):
        expected_roots = {
            "cross-compiler": {"TestE2EInferredValueNativeRV64UnderQEMU", "TestE2EDispatchSelectsSVEUnderQEMU", "TestE2EFreestandingPartialLink", "TestE2ENativeConstantTablesExecutable", "TestRingsCrossTargets"},
            "cross-testrunner": {"TestForeignTargetRunsUnderEmulator", "TestTargetFlagBuildsWithoutRunning"},
            "lean-compiler": {"TestLeanFloatBitsAgreeWithHost", "TestE2ELeanFunctionArguments", "TestE2ELeanReduceLanesFunctionArgument", "TestE2ELeanNestedAssignment"},
            "lean-cli": {"TestBuildLeanNamespace"},
            "sail-source": {"TestSailArmBRKDispatchSource", "TestSailArmCBZ32DispatchSource", "TestScalarADDPPinnedSailContract"},
            "llvm": {"TestEncoderAgainstLLVM", "TestEncoderFuzzAgainstLLVM", "TestEncodeFunctionAgainstLLVM", "TestObjectsAgainstLLVMTools", "TestSMEAgainstLLVM", "TestSystemRegistersAgainstLLVM"},
        }
        self.assertEqual(set(required.SUITES), set(expected_roots))
        for name, suite in required.SUITES.items():
            self.assertEqual(set(suite.roots), expected_roots[name])
            self.assertEqual(len(suite.tests), len(set(suite.tests)))
            for root in suite.roots:
                self.assertRegex(root, suite.pattern)
                self.assertIsNone(re.search(suite.pattern, root + "Other"))
                self.assertIsNone(re.search(suite.pattern, "Other" + root))
        expected_children = {
            "cross-compiler": {"TestE2ENativeConstantTablesExecutable/freestanding/riscv64", "TestE2ENativeConstantTablesExecutable/freestanding/arm64", "TestRingsCrossTargets/linux/riscv64", "TestRingsCrossTargets/linux/arm64"},
            "lean-compiler": {"TestE2ELeanFunctionArguments/Lean", "TestE2ELeanReduceLanesFunctionArgument/Lean", "TestE2ELeanNestedAssignment/Lean"},
            "lean-cli": {"TestBuildLeanNamespace/LeanImports"},
            "sail-source": {"TestScalarADDPPinnedSailContract/vector_reduce_add_sisd_decode", "TestScalarADDPPinnedSailContract/vector_reduce_add_sisd", "TestScalarADDPPinnedSailContract/Reduce", "TestScalarADDPPinnedSailContract/aset_V"},
            "llvm": {"TestObjectsAgainstLLVMTools/macho", "TestObjectsAgainstLLVMTools/elf"},
        }
        for name, children in expected_children.items():
            self.assertEqual({test for test in required.SUITES[name].tests if "/" in test}, children)

    def test_workflows_select_every_suite_in_equipped_lane(self):
        root = Path(__file__).resolve().parents[1]
        lanes = {
            "ci.yml": ("cross-compiler", "cross-testrunner"),
            "formal.yml": ("lean-compiler", "lean-cli"),
            "formal-sail.yml": ("sail-source", "llvm"),
        }
        for file, suites in lanes.items():
            source = (root / "workflows" / file).read_text()
            for suite in suites:
                self.assertEqual(source.count("run: python3 .github/scripts/required_backend_tests.py " + suite + "\n"), 1)


if __name__ == "__main__":
    unittest.main()
