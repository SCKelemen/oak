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

    def test_runner_forwards_required_race_and_environment(self):
        process = MagicMock()
        process.stdout = iter([])
        process.wait.return_value = 0
        process.__enter__.return_value = process
        env = {"OAK_REQUIRE_ROR_TWIN": "1", "OAK_ROR_TWIN_RECEIPT": "/fresh/receipt.json"}
        with patch.object(required.subprocess, "Popen", return_value=process) as call:
            with contextlib.redirect_stdout(io.StringIO()), self.assertRaisesRegex(ValueError, "required tests did not pass"):
                required.run_suite(self.suite, race=True, env=env)
        self.assertEqual(call.call_args.args[0], ["go", "test", "-json", "-count=1", "-race", "-timeout=10m", "./compiler", "-run", "^(TestRequired)$"])
        self.assertIs(call.call_args.kwargs["env"], env)

    def test_cli_reports_inventory_process_and_output_errors(self):
        for error in (OSError("cannot launch"), UnicodeError("invalid output"), required.subprocess.CalledProcessError(2, ["go"])):
            with self.subTest(error=error), patch.object(required, "run_suite", side_effect=error):
                with contextlib.redirect_stderr(io.StringIO()):
                    self.assertEqual(required.main(["llvm"]), 1)

    def test_audited_suite_manifest(self):
        expected_roots = {
            "asm-memory-markers": {'TestDecideSpansRejectsDifferentMemoryMarkerGuards', 'TestFrameSpanAccessRetainsFillAfterGuardedZero', 'TestMemoryAtGuardedZeroPreservesHistoryAndPruning', 'TestMergeWritesPreservesGuardedZeroMemory', 'TestWriteLogsEqualUnderChecksMemoryMarkerGuards', 'TestWriteLogsEqualUnderMarkerGuardUnknownFailsClosed'},
            "c-symbol-compiler": {'TestCDispatchTemporariesAvoidCallableShadowing', 'TestCReservedExplicitABISymbolsRejected', 'TestCRuntimeHostHooksRemainExternOnly', 'TestE2CLaunchTemporariesAvoidCallableShadowing', 'TestE2ECCallablesAvoidRuntimeSymbols', 'TestE2EEscapedCallableHeaderAndABI'},
            "c-symbol-typechecker": {'TestCFunctionRuntimeEscapesAreInjective', 'TestCFunctionRuntimeFamilies', 'TestCFunctionSymbolsPreserveCompatibleABI'},
            "reader-apdu": {"TestE2EStdlibBoundedReader", "TestE2EStdlibCommandAPDUMatrix", "TestE2EStdlibCommandAPDUMaximumAndPayloads", "TestE2EStdlibCommandAPDUBufferNonMutation", "TestE2EStdlibCommandAPDUGuardPages"},
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
            "asm-memory-markers": {'TestDecideSpansRejectsDifferentMemoryMarkerGuards/different', 'TestDecideSpansRejectsDifferentMemoryMarkerGuards/equal', 'TestFrameSpanAccessRetainsFillAfterGuardedZero/conditional', 'TestFrameSpanAccessRetainsFillAfterGuardedZero/unconditional', 'TestMergeWritesPreservesGuardedZeroMemory/zero_fallthrough', 'TestMergeWritesPreservesGuardedZeroMemory/zero_taken', 'TestWriteLogsEqualUnderChecksMemoryMarkerGuards/conditional_and_unconditional', 'TestWriteLogsEqualUnderChecksMemoryMarkerGuards/different_markers', 'TestWriteLogsEqualUnderChecksMemoryMarkerGuards/equivalent_conjunctions', 'TestWriteLogsEqualUnderChecksMemoryMarkerGuards/guard_implied_by_premise', 'TestWriteLogsEqualUnderChecksMemoryMarkerGuards/independent_guards', 'TestWriteLogsEqualUnderChecksMemoryMarkerGuards/opposite_guards', 'TestWriteLogsEqualUnderChecksMemoryMarkerGuards/opposite_zero-fill_guards', 'TestWriteLogsEqualUnderChecksMemoryMarkerGuards/same_conditional_zero_fill', 'TestWriteLogsEqualUnderChecksMemoryMarkerGuards/same_guard', 'TestWriteLogsEqualUnderChecksMemoryMarkerGuards/same_unconditional_marker', 'TestWriteLogsEqualUnderChecksMemoryMarkerGuards/same_unconditional_zero_fill'},
            "c-symbol-compiler": {'TestCDispatchTemporariesAvoidCallableShadowing/-O0', 'TestCDispatchTemporariesAvoidCallableShadowing/-O2', 'TestCReservedExplicitABISymbolsRejected/export/OAK_INLINE', 'TestCReservedExplicitABISymbolsRejected/export/__oak_cas_u32_seq_cst', 'TestCReservedExplicitABISymbolsRejected/export/core_slice', 'TestCReservedExplicitABISymbolsRejected/export/oak_0f_p0__nstore', 'TestCReservedExplicitABISymbolsRejected/export/oak_add_u32', 'TestCReservedExplicitABISymbolsRejected/export/oak_store', 'TestCReservedExplicitABISymbolsRejected/export/oak_view_u8', 'TestCReservedExplicitABISymbolsRejected/extern/OAK_INLINE', 'TestCReservedExplicitABISymbolsRejected/extern/__oak_cas_u32_seq_cst', 'TestCReservedExplicitABISymbolsRejected/extern/core_slice', 'TestCReservedExplicitABISymbolsRejected/extern/oak_0f_p0__nstore', 'TestCReservedExplicitABISymbolsRejected/extern/oak_add_u32', 'TestCReservedExplicitABISymbolsRejected/extern/oak_store', 'TestCReservedExplicitABISymbolsRejected/extern/oak_view_u8', 'TestCRuntimeHostHooksRemainExternOnly/oak_host_write', 'TestCRuntimeHostHooksRemainExternOnly/oak_host_write_call', 'TestCRuntimeHostHooksRemainExternOnly/oak_measured_value', 'TestCRuntimeHostHooksRemainExternOnly/oak_test_host_launch_begin', 'TestE2CLaunchTemporariesAvoidCallableShadowing/-O0', 'TestE2CLaunchTemporariesAvoidCallableShadowing/-O2', 'TestE2ECCallablesAvoidRuntimeSymbols/-O0', 'TestE2ECCallablesAvoidRuntimeSymbols/-O2', 'TestE2EEscapedCallableHeaderAndABI/option', 'TestE2EEscapedCallableHeaderAndABI/root', 'TestE2EEscapedCallableHeaderAndABI/source'},
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
            "ci.yml": ("cross-compiler", "cross-testrunner", "c-symbol-compiler", "c-symbol-typechecker", "asm-memory-markers"),
            "formal.yml": ("lean-compiler", "lean-cli", "reader-apdu"),
            "formal-sail.yml": ("sail-source", "llvm"),
        }
        for file, suites in lanes.items():
            source = (root / "workflows" / file).read_text()
            for suite in suites:
                self.assertEqual(source.count("run: python3 .github/scripts/required_backend_tests.py " + suite + "\n"), 1)



class RequiredReaderAPDUTests(unittest.TestCase):
    def results(self, omit=None):
        suite = required.SUITES["reader-apdu"]
        result = required.RequiredResults(suite)
        for root in suite.roots:
            if root != omit:
                result.accept({"Action": "run", "Package": suite.import_path, "Test": root})
                result.accept({"Action": "pass", "Package": suite.import_path, "Test": root})
        result.accept({"Action": "pass", "Package": suite.import_path})
        return suite, result

    def test_reader_apdu_all_five_are_required(self):
        suite, result = self.results()
        self.assertEqual(len(suite.roots), 5)
        self.assertEqual(suite.package, "./compiler")
        self.assertEqual(suite.timeout, "10m")
        result.finish(0)

    def test_reader_apdu_absent_root_refused(self):
        for root in required.SUITES["reader-apdu"].roots:
            with self.subTest(root=root):
                _, result = self.results(omit=root)
                with self.assertRaisesRegex(ValueError, "required tests did not pass"):
                    result.finish(0)

    def test_reader_apdu_duplicate_root_refused(self):
        for root in required.SUITES["reader-apdu"].roots:
            with self.subTest(root=root):
                suite, result = self.results()
                with self.assertRaisesRegex(ValueError, "duplicate"):
                    result.accept({"Action": "run", "Package": suite.import_path, "Test": root})

    def test_reader_apdu_skipped_root_refused(self):
        for root in required.SUITES["reader-apdu"].roots:
            with self.subTest(root=root):
                suite, result = self.results(omit=root)
                result.accept({"Action": "run", "Package": suite.import_path, "Test": root})
                result.accept({"Action": "skip", "Package": suite.import_path, "Test": root})
                with self.assertRaisesRegex(ValueError, "skip"):
                    result.finish(0)

    def test_reader_apdu_selected_subtest_skip_refused(self):
        for root in required.SUITES["reader-apdu"].roots:
            with self.subTest(root=root):
                suite, result = self.results()
                child = root + "/FutureChild"
                result.accept({"Action": "run", "Package": suite.import_path, "Test": child})
                result.accept({"Action": "skip", "Package": suite.import_path, "Test": child})
                with self.assertRaisesRegex(ValueError, "skip"):
                    result.finish(0)


class RequiredMemoryMarkerTests(unittest.TestCase):
    def results(self, omit=None, terminal="pass"):
        suite = required.SUITES["asm-memory-markers"]
        result = required.RequiredResults(suite)
        for name in suite.tests:
            if name == omit:
                continue
            result.accept({"Action": "run", "Package": suite.import_path, "Test": name})
            result.accept({"Action": "pass", "Package": suite.import_path, "Test": name})
        result.accept({"Action": terminal, "Package": suite.import_path})
        return suite, result

    def test_all_six_roots_and_seventeen_children_required(self):
        suite, result = self.results()
        self.assertEqual(suite.package, "./asm")
        self.assertEqual(suite.timeout, "10m")
        self.assertEqual(len(suite.roots), 6)
        self.assertEqual(len(suite.tests), 23)
        self.assertEqual(len([name for name in suite.tests if "/" in name]), 17)
        result.finish(0)

    def test_every_missing_identity_refused(self):
        for name in required.SUITES["asm-memory-markers"].tests:
            with self.subTest(name=name):
                _, result = self.results(omit=name)
                with self.assertRaisesRegex(ValueError, "required tests did not pass"):
                    result.finish(0)

    def test_every_skipped_or_failed_identity_refused(self):
        for name in required.SUITES["asm-memory-markers"].tests:
            for action in ("skip", "fail"):
                with self.subTest(name=name, action=action):
                    suite, result = self.results(omit=name)
                    result.accept({"Action": "run", "Package": suite.import_path, "Test": name})
                    result.accept({"Action": action, "Package": suite.import_path, "Test": name})
                    with self.assertRaisesRegex(ValueError, action):
                        result.finish(0)

    def test_every_duplicate_identity_refused(self):
        for name in required.SUITES["asm-memory-markers"].tests:
            with self.subTest(name=name):
                suite, result = self.results()
                with self.assertRaisesRegex(ValueError, "duplicate"):
                    result.accept({"Action": "run", "Package": suite.import_path, "Test": name})

    def test_unlisted_nested_skip_under_each_root_refused(self):
        for root in required.SUITES["asm-memory-markers"].roots:
            with self.subTest(root=root):
                suite, result = self.results()
                child = root + "/FutureChild"
                result.accept({"Action": "run", "Package": suite.import_path, "Test": child})
                result.accept({"Action": "skip", "Package": suite.import_path, "Test": child})
                with self.assertRaisesRegex(ValueError, "skip"):
                    result.finish(0)

    def test_package_and_process_failure_refused(self):
        for action, exit_code in (("fail", 0), ("pass", 1)):
            with self.subTest(action=action, exit_code=exit_code):
                _, result = self.results(terminal=action)
                with self.assertRaises(ValueError):
                    result.finish(exit_code)

    def test_cli_selects_race_for_memory_markers(self):
        with patch.object(required, "run_suite") as call:
            self.assertEqual(required.main(["asm-memory-markers"]), 0)
        call.assert_called_once_with(required.SUITES["asm-memory-markers"], race=True)


if __name__ == "__main__":
    unittest.main()
