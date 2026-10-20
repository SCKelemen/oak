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

    def test_equipped_race_suites_use_race_for_inventory_and_execution(self):
        self.assertEqual({n for n, s in required.SUITES.items() if s.race},
                         {"checked-image-runtime", "selfhost-image-producers", "selfhost-image-admission"})
        suite = required.Suite("./compiler", "10m", ("TestRequired",), race=True)
        with patch.object(required.subprocess, "check_output", return_value="TestRequired\n") as call:
            required.check_inventory(suite)
            self.assertEqual(call.call_args.args[0], ["go", "test", "-race", "./compiler", "-list", "^(TestRequired)$"])
        process = MagicMock()
        process.stdout = iter([])
        process.wait.return_value = 9
        process.__enter__.return_value = process
        with patch.object(required.subprocess, "Popen", return_value=process) as call:
            with contextlib.redirect_stdout(io.StringIO()), self.assertRaisesRegex(ValueError, "exited 9"):
                required.run_suite(suite)
        self.assertEqual(call.call_args.args[0], ["go", "test", "-race", "-json", "-count=1", "-timeout=10m", "./compiler", "-run", "^(TestRequired)$"])

    def test_exact_child_inventory_rejects_unlisted_image_cases(self):
        suite = required.Suite("./compiler", "10m", ("TestRequired",), exact_children=True)
        results = required.RequiredResults(suite)
        with self.assertRaisesRegex(ValueError, "unexpected unlisted test"):
            results.accept({"Action": "run", "Package": suite.import_path, "Test": "TestRequired/Unexpected"})

    def test_image_suites_require_every_named_check(self):
        for key in ("checked-image-sources", "checked-image-runtime", "checked-image-bundle", "selfhost-image-producers", "selfhost-image-admission"):
            suite = required.SUITES[key]
            self.assertTrue(suite.exact_children)
            for omitted in suite.tests:
                results = required.RequiredResults(suite)
                for name in suite.tests:
                    if name != omitted:
                        for action in ("run", "pass"):
                            results.accept({"Action": action, "Package": suite.import_path, "Test": name})
                results.accept({"Action": "pass", "Package": suite.import_path})
                with self.assertRaisesRegex(ValueError, omitted):
                    results.finish(0)
        required_runtime = {"MaximumNameAndSource", "DropContract/arm", "DropContract/rv", "ActualSuccessfulRefusalProof", "ValidRecordThenFailure", "CanceledGlobalQueue", "CloseActiveRequest"}
        self.assertTrue({"TestImagePinnedRuntime/" + n for n in required_runtime} <= set(required.SUITES["checked-image-runtime"].tests))

    def test_strict_entry_gate_is_fail_closed(self):
        workflow = (Path(__file__).resolve().parents[1] / "workflows/formal-sail.yml").read_text()
        self.assertEqual(workflow.count("          python3 .github/scripts/required_backend_tests.py strict-entry\n"), 1)
        suite = required.SUITES["strict-entry"]
        self.assertTrue(suite.exact_children)
        for omitted in suite.tests:
            results = required.RequiredResults(suite)
            for name in suite.tests:
                if name != omitted:
                    for action in ("run", "pass"):
                        results.accept({"Action": action, "Package": suite.import_path, "Test": name})
            results.accept({"Action": "pass", "Package": suite.import_path})
            with self.subTest(omitted=omitted), self.assertRaisesRegex(ValueError, omitted):
                results.finish(0)
        for skipped in suite.tests:
            results = required.RequiredResults(suite)
            for name in suite.tests:
                results.accept({"Action": "run", "Package": suite.import_path, "Test": name})
                results.accept({"Action": "skip" if name == skipped else "pass",
                                "Package": suite.import_path, "Test": name})
            results.accept({"Action": "pass", "Package": suite.import_path})
            with self.subTest(skipped=skipped), self.assertRaisesRegex(ValueError, "skip"):
                results.finish(0)
        with patch.object(required.subprocess, "check_output", return_value="ok package [no tests to run]\n"):
            with self.assertRaises(ValueError):
                required.check_inventory(suite)

    def test_stateful_copy_gate_is_fail_closed(self):
        suite = required.SUITES['stateful-copy']
        self.assertTrue(suite.exact_children)
        self.assertEqual(len(suite.tests), 7)
        for omitted in suite.tests:
            results = required.RequiredResults(suite)
            for name in suite.tests:
                if name != omitted:
                    for action in ('run', 'pass'):
                        results.accept({'Action': action, 'Package': suite.import_path, 'Test': name})
            results.accept({'Action': 'pass', 'Package': suite.import_path})
            with self.subTest(omitted=omitted), self.assertRaisesRegex(ValueError, omitted):
                results.finish(0)
        for skipped in suite.tests:
            results = required.RequiredResults(suite)
            for name in suite.tests:
                results.accept({'Action': 'run', 'Package': suite.import_path, 'Test': name})
                results.accept({'Action': 'skip' if name == skipped else 'pass',
                                'Package': suite.import_path, 'Test': name})
            results.accept({'Action': 'pass', 'Package': suite.import_path})
            with self.subTest(skipped=skipped), self.assertRaisesRegex(ValueError, 'skip'):
                results.finish(0)
        workflow = (Path(__file__).resolve().parents[1] / 'workflows/formal.yml').read_text()
        self.assertIn("OAK_REQUIRE_STATEFUL_COPY_LEAN: '1'", workflow)
        self.assertNotIn('continue-on-error:', workflow)

    def test_audited_suite_manifest(self):
        expected_roots = {
            'stateful-copy': {'TestLeanStatefulCopyProof', 'TestStatefulCopySourceClosure',
                              'TestStatefulCopyConcreteLayoutAndNativeCall',
                              'TestStatefulCopyCurrentOptIRAndWasmRefusals',
                              'TestStatefulCopyCallerMemoryFixtures'},
            'selfhost-image-producers': {'TestE2ESelfHostedBitwiseELF', 'TestE2ESelfHostedBitwiseELFExtract', 'TestLeanNativeBitwiseEnvelopeExtract', 'TestLeanNativeBitwiseEnvelopeProof', 'TestLeanNativeBitwiseEnvelopeTotalProof', 'TestE2ESelfHostedWasmBitwiseModule', 'TestE2ESelfHostedWasmBitwiseModuleRefusal', 'TestLeanWasmBitwiseModuleExtract', 'TestLeanWasmBitwiseModuleFaithful', 'TestE2ESelfHostedBitwiseImageBytes'},
            'selfhost-image-admission': {'TestSelfHostedBitwiseImageBundleReal'},
            'checked-image-sources': {'TestEmbeddedClosureCustody', 'TestImageEmbeddedClosureCustody'},
            'checked-image-runtime': {'TestImageClosedInstallationProfile', 'TestImagePinnedRuntime', 'TestProcessRefusal', 'TestExtractionBoundaries', 'TestInstallRefusesUntrustedArchive', 'TestArchiveDigestMismatch', 'TestImageProtocolFieldLimits', 'TestImageMaximumProtocolSize', 'TestArchiveFIFORefusesWithoutBlocking', 'TestImageZeroAuthority', 'TestImageSnapshotAndRenderer', 'TestImageStrictProtocol'},
            'checked-image-bundle': {'TestEmitKernelCheckedBitwiseImageBundleReal', 'TestEmitKernelCheckedBitwiseImageBundleRefusesInvalidInstallation', 'TestCheckedImageProposedSymbolBoundaries', 'TestCheckedImageProposalOwnsCopyWithoutClaimingBodyAuthority', 'TestCheckedImageProposalProduction', 'TestCheckedImageProposalRefusesMalformedObjects', 'TestEmitKernelCheckedBitwiseImageBundleRefusesCanceledContext', 'TestKernelCheckedBitwiseImageBundleDoesNotPromoteLegacyAuthority'},
            "checked-bitwise-sources": {"TestEmbeddedClosureCustody"},
            "checked-bitwise-runtime": {
                "TestArchiveFIFORefusesWithoutBlocking", "TestArchiveDigestMismatch", "TestExtractionBoundaries",
                "TestStrictProtocol", "TestProcessRefusal", "TestZeroAuthority",
                "TestSnapshotsAndDriver", "TestInstallRefusesUntrustedArchive", "TestRealKernelAdmission",
            },
            "checked-bitwise-bundle": {
                "TestEmitKernelCheckedBitwiseBundleRefusesInvalidInstallation",
                "TestEmitKernelCheckedBitwiseBundleRefusesCanceledContext",
                "TestKernelCheckedBitwiseBundleDoesNotPromoteLegacyAuthority",
                "TestEmitKernelCheckedBitwiseBundleReal",
                "TestVerifiedProfileClosesOverCallees",
                "TestVerdictCacheRoundTripsDependencies",
                "TestVerdictCacheRejectsMalformedDependencyRecords",
                "TestVerdictCacheKeyIncludesMachineOnlyCalleeBodies",
                "TestVerdictCacheMachineCalleesAgreeWithStrictResolver",
            },
            "native-object": {"TestNativeBitwiseObjectLean"},
            "native-image": {"TestNativeBitwiseImageLean"},
            "strict-entry": {"TestRV64StrictEntryBitwiseCompilerMatchesLean", "TestRV64StrictEntryToolchainSelection"},
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
            'stateful-copy': {'TestStatefulCopyConcreteLayoutAndNativeCall/arm64',
                              'TestStatefulCopyConcreteLayoutAndNativeCall/rv64'},
            "strict-entry": {"TestRV64StrictEntryBitwiseCompilerMatchesLean/" + child
                             for child in ("interfaces", "pins", "audit")},
            "cross-compiler": {"TestE2ENativeConstantTablesExecutable/freestanding/riscv64", "TestE2ENativeConstantTablesExecutable/freestanding/arm64", "TestRingsCrossTargets/linux/riscv64", "TestRingsCrossTargets/linux/arm64"},
            "lean-compiler": {"TestE2ELeanFunctionArguments/Lean", "TestE2ELeanReduceLanesFunctionArgument/Lean", "TestE2ELeanNestedAssignment/Lean"},
            "lean-cli": {"TestBuildLeanNamespace/LeanImports"},
            "sail-source": {"TestScalarADDPPinnedSailContract/vector_reduce_add_sisd_decode", "TestScalarADDPPinnedSailContract/vector_reduce_add_sisd", "TestScalarADDPPinnedSailContract/Reduce", "TestScalarADDPPinnedSailContract/aset_V"},
            "llvm": {"TestObjectsAgainstLLVMTools/macho", "TestObjectsAgainstLLVMTools/elf"},
        }
        for name, children in expected_children.items():
            self.assertEqual({test for test in required.SUITES[name].tests if "/" in test}, children)

    def test_checked_bundle_requires_all_six_production_bundles(self):
        suite = required.SUITES["checked-bitwise-bundle"]
        matrix = {
            "TestEmitKernelCheckedBitwiseBundleReal/Canonical/" + family + "/" + op
            for family in ("bitwise", "Mix9") for op in ("and", "or", "xor")
        }
        self.assertEqual({name for name in suite.tests if "/Canonical/" in name}, matrix)
        for omitted in matrix:
            results = required.RequiredResults(suite)
            for name in suite.tests:
                if name == omitted:
                    continue
                for action in ("run", "pass"):
                    results.accept({"Action": action, "Package": suite.import_path, "Test": name})
            results.accept({"Action": "pass", "Package": suite.import_path})
            with self.assertRaisesRegex(ValueError, omitted):
                results.finish(0)
        children = {name.rsplit("/", 1)[-1] for name in suite.tests if "/" in name}
        self.assertTrue({"CopyCustody", "RenamedParametersFreshAdmission", "Canceled", "Closed",
                         "source_operation", "source_name", "wasm_trailing", "arm_body", "rv_abi"} <= children)

    def test_raw_producer_gates_are_exact_and_fail_closed(self):
        producers = required.SUITES["selfhost-image-producers"]
        admissions = required.SUITES["selfhost-image-admission"]
        self.assertEqual(len(producers.tests), 218)
        self.assertEqual(len(admissions.tests), 35)
        self.assertEqual(sum(n.startswith("TestE2ESelfHostedBitwiseELF/") for n in producers.tests), 145)
        self.assertEqual(sum(n.startswith("TestE2ESelfHostedWasmBitwiseModule/") for n in producers.tests), 24)
        self.assertEqual(sum(n.startswith("TestE2ESelfHostedWasmBitwiseModuleRefusal/") for n in producers.tests), 33)
        self.assertEqual(sum(n.startswith("TestSelfHostedBitwiseImageBundleReal/Refusals/") for n in admissions.tests), 26)
        self.assertTrue({"TestLeanWasmBitwiseModuleExtract", "TestLeanWasmBitwiseModuleFaithful",
                         "TestLeanNativeBitwiseEnvelopeExtract", "TestLeanNativeBitwiseEnvelopeProof", "TestLeanNativeBitwiseEnvelopeTotalProof"} <= set(producers.tests))
        matrix = {"TestSelfHostedBitwiseImageBundleReal/Canonical/" + family + "/" + op
                  for family in ("bitwise", "Mix9") for op in ("and", "or", "xor")}
        self.assertEqual({n for n in admissions.tests if "/Canonical/" in n}, matrix)
        for suite in (producers, admissions):
            self.assertTrue(suite.exact_children)
            self.assertTrue(suite.race)
            for skipped in suite.tests:
                results = required.RequiredResults(suite)
                for name in suite.tests:
                    results.accept({"Action": "run", "Package": suite.import_path, "Test": name})
                    results.accept({"Action": "skip" if name == skipped else "pass",
                                    "Package": suite.import_path, "Test": name})
                results.accept({"Action": "pass", "Package": suite.import_path})
                with self.subTest(skipped=skipped), self.assertRaisesRegex(ValueError, "skip"):
                    results.finish(0)
            with patch.object(required.subprocess, "check_output", return_value="ok package [no tests to run]\n"):
                with self.assertRaises(ValueError):
                    required.check_inventory(suite)
        root = Path(__file__).resolve().parents[2]
        for name in ("e2e_selfhost_bitwise_wasm_module_test.go", "lean_selfhost_bitwise_wasm_module_test.go"):
            self.assertTrue((root / "compiler" / name).is_file())
            self.assertFalse(name.endswith("_wasm_test.go"))
        job = (root / ".github/workflows/checked-image-bundle.yml").read_text().split("  selfhost-complete-images:\n", 1)[1]
        for flag in ("OAK_REQUIRE_SELFHOST_IMAGE_PRODUCERS", "OAK_REQUIRE_WASM_LEAN", "OAK_REQUIRE_BITWISE_IMAGECHECK"):
            self.assertIn(flag + ": '1'", job)
        self.assertNotIn("continue-on-error:", job)
        self.assertIn("command -v cc", job)
        self.assertIn("sha256sum --check --strict", job)
        self.assertIn("lean-4.33.1-linux/bin", job)

    def test_native_image_gates_run_in_complete_isolated_matrix(self):
        source = (Path(__file__).resolve().parents[1] / "workflows" / "formal.yml").read_text()
        job = source.split("  native-bitwise-images:\n", 1)[1].split("  lean:\n", 1)[0]
        self.assertIn("gate: [fixtures, production]", job)
        self.assertIn("fail-fast: false", job)
        self.assertIn("if: matrix.gate == 'fixtures'", job)
        self.assertIn("if: matrix.gate == 'production'", job)
        self.assertEqual(job.count("python3 tools/native_image_fixtures/check.py"), 1)
        self.assertEqual(job.count("python3 .github/scripts/required_backend_tests.py native-image"), 1)
        self.assertIn("OAK_REQUIRE_NATIVE_IMAGE_LEAN: '1'", job)
        self.assertEqual(required.SUITES["native-image"].timeout, "30m")

    def test_image_workflow_preserves_protected_branches_and_reruns(self):
        source = (Path(__file__).resolve().parents[1] / "workflows" / "checked-image-bundle.yml").read_text()
        self.assertEqual(source.count("branches: [main, specification, consolidation]"), 2)
        self.assertIn("permissions:\n  contents: read", source)
        self.assertIn("format('run-{0}-{1}', github.run_id, github.run_attempt)", source)
        self.assertIn("OAK_REQUIRE_BITWISE_IMAGECHECK: '1'", source)
        self.assertIn("CGO_ENABLED: '1'", source)
        self.assertNotIn("Oak.CheckedBundleAudit", source)
        self.assertNotIn("tools/checked_bundle/test_request.py", source)

    def test_workflows_select_every_suite_in_equipped_lane(self):
        root = Path(__file__).resolve().parents[1]
        lanes = {
            "checked-image-bundle.yml": ("checked-image-sources", "checked-image-runtime", "checked-image-bundle", "selfhost-image-producers", "selfhost-image-admission"),
            "ci.yml": ("cross-compiler", "cross-testrunner"),
            "formal.yml": ("lean-compiler", "lean-cli", "native-object", "native-image", "stateful-copy"),
            "formal-sail.yml": ("sail-source", "llvm"),
            "checked-bitwise-bundle.yml": ("checked-bitwise-sources", "checked-bitwise-runtime", "checked-bitwise-bundle"),
        }
        for file, suites in lanes.items():
            source = (root / "workflows" / file).read_text()
            for suite in suites:
                self.assertEqual(source.count("run: python3 .github/scripts/required_backend_tests.py " + suite + "\n"), 1)


if __name__ == "__main__":
    unittest.main()
