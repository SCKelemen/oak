#!/usr/bin/env python3
"""Run equipped-lane backend checks, rejecting missing tests and nested skips.

Ordinary development tests can still skip unavailable tools. These focused CI
suites require every named root and audited child to pass, and reject any skip
or failure in the selected tests. Keep the names here synchronized with the
Go tests; --check compares the exact selectors with Go's live test inventory.
"""
import argparse
from dataclasses import dataclass
import json
import subprocess
import sys


@dataclass(frozen=True)
class Suite:
    package: str
    timeout: str
    tests: tuple[str, ...]

    @property
    def roots(self):
        return sorted({name.split("/", 1)[0] for name in self.tests})

    @property
    def pattern(self):
        return "^(" + "|".join(self.roots) + ")$"

    @property
    def import_path(self):
        return "github.com/SCKelemen/oak" + self.package[1:]


SUITES = {
    "asm-memory-markers": Suite("./asm", "10m", (
        "TestWriteLogsEqualUnderChecksMemoryMarkerGuards",
        "TestWriteLogsEqualUnderChecksMemoryMarkerGuards/opposite_guards",
        "TestWriteLogsEqualUnderChecksMemoryMarkerGuards/conditional_and_unconditional",
        "TestWriteLogsEqualUnderChecksMemoryMarkerGuards/independent_guards",
        "TestWriteLogsEqualUnderChecksMemoryMarkerGuards/same_guard",
        "TestWriteLogsEqualUnderChecksMemoryMarkerGuards/same_unconditional_marker",
        "TestWriteLogsEqualUnderChecksMemoryMarkerGuards/equivalent_conjunctions",
        "TestWriteLogsEqualUnderChecksMemoryMarkerGuards/guard_implied_by_premise",
        "TestWriteLogsEqualUnderChecksMemoryMarkerGuards/different_markers",
        "TestWriteLogsEqualUnderChecksMemoryMarkerGuards/opposite_zero-fill_guards",
        "TestWriteLogsEqualUnderChecksMemoryMarkerGuards/same_conditional_zero_fill",
        "TestWriteLogsEqualUnderChecksMemoryMarkerGuards/same_unconditional_zero_fill",
        "TestWriteLogsEqualUnderMarkerGuardUnknownFailsClosed",
        "TestDecideSpansRejectsDifferentMemoryMarkerGuards",
        "TestDecideSpansRejectsDifferentMemoryMarkerGuards/different",
        "TestDecideSpansRejectsDifferentMemoryMarkerGuards/equal",
        "TestMergeWritesPreservesGuardedZeroMemory",
        "TestMergeWritesPreservesGuardedZeroMemory/zero_fallthrough",
        "TestMergeWritesPreservesGuardedZeroMemory/zero_taken",
        "TestMemoryAtGuardedZeroPreservesHistoryAndPruning",
        "TestFrameSpanAccessRetainsFillAfterGuardedZero",
        "TestFrameSpanAccessRetainsFillAfterGuardedZero/unconditional",
        "TestFrameSpanAccessRetainsFillAfterGuardedZero/conditional",
        "TestZeroTestOfRequiresBooleanNonzero",
        "TestZeroTestOfRequiresBooleanNonzero/eq_width_1",
        "TestZeroTestOfRequiresBooleanNonzero/ne_width_1",
        "TestZeroTestOfRequiresBooleanNonzero/eq_width_2",
        "TestZeroTestOfRequiresBooleanNonzero/ne_width_2",
        "TestZeroTestOfRequiresBooleanNonzero/eq_width_8",
        "TestZeroTestOfRequiresBooleanNonzero/ne_width_8",
        "TestZeroTestOfRequiresBooleanNonzero/eq_width_32",
        "TestZeroTestOfRequiresBooleanNonzero/ne_width_32",
        "TestZeroTestOfRequiresBooleanNonzero/eq_width_64",
        "TestZeroTestOfRequiresBooleanNonzero/ne_width_64",
        "TestZeroTestOfRequiresBooleanNonzero/comparison",
        "TestZeroTestOfRequiresBooleanNonzero/Boolean_ite",
        "TestZeroTestOfRequiresBooleanNonzero/masked_bit",
        "TestPruneUnderDirectNonzeroPreservesLowBit",
        "TestPruneUnderDirectNonzeroPreservesLowBit/width_2",
        "TestPruneUnderDirectNonzeroPreservesLowBit/width_8",
        "TestPruneUnderDirectNonzeroPreservesLowBit/width_32",
        "TestPruneUnderDirectNonzeroPreservesLowBit/width_64",
        "TestImpliesEqualRefutesNonzeroLowBit",
    )),
    "c-symbol-compiler": Suite("./compiler", "10m", (
        "TestAsmAddSymbolLowering",
        "TestE2ECCallablesAvoidRuntimeSymbols",
        "TestE2ECCallablesAvoidRuntimeSymbols/-O0",
        "TestE2ECCallablesAvoidRuntimeSymbols/-O2",
        "TestE2EEscapedCallableHeaderAndABI",
        "TestE2EEscapedCallableHeaderAndABI/root",
        "TestE2EEscapedCallableHeaderAndABI/option",
        "TestE2EEscapedCallableHeaderAndABI/source",
        "TestCReservedExplicitABISymbolsRejected",
        "TestCReservedExplicitABISymbolsRejected/extern/oak_store",
        "TestCReservedExplicitABISymbolsRejected/export/oak_store",
        "TestCReservedExplicitABISymbolsRejected/extern/oak_add_u32",
        "TestCReservedExplicitABISymbolsRejected/export/oak_add_u32",
        "TestCReservedExplicitABISymbolsRejected/extern/oak_view_u8",
        "TestCReservedExplicitABISymbolsRejected/export/oak_view_u8",
        "TestCReservedExplicitABISymbolsRejected/extern/oak_0f_p0__nstore",
        "TestCReservedExplicitABISymbolsRejected/export/oak_0f_p0__nstore",
        "TestCReservedExplicitABISymbolsRejected/extern/__oak_cas_u32_seq_cst",
        "TestCReservedExplicitABISymbolsRejected/export/__oak_cas_u32_seq_cst",
        "TestCReservedExplicitABISymbolsRejected/extern/OAK_INLINE",
        "TestCReservedExplicitABISymbolsRejected/export/OAK_INLINE",
        "TestCReservedExplicitABISymbolsRejected/extern/core_slice",
        "TestCReservedExplicitABISymbolsRejected/export/core_slice",
        "TestCReservedExplicitABISymbolsRejected/extern/oak_test_host_unknown",
        "TestCReservedExplicitABISymbolsRejected/export/oak_test_host_unknown",
        "TestCReservedExplicitABISymbolsRejected/extern/oak_test_host_fail_extra",
        "TestCReservedExplicitABISymbolsRejected/export/oak_test_host_fail_extra",
        "TestCReservedExplicitABISymbolsRejected/extern/oak_test_host_command_limits",
        "TestCReservedExplicitABISymbolsRejected/export/oak_test_host_command_limits",
        "TestCReservedExplicitABISymbolsRejected/extern/oak_host_read",
        "TestCReservedExplicitABISymbolsRejected/export/oak_host_read",
        "TestCRuntimeHostHooksRemainExternOnly",
        "TestCRuntimeHostHooksRemainExternOnly/oak_host_write_call",
        "TestCRuntimeHostHooksRemainExternOnly/oak_host_write",
        "TestCRuntimeHostHooksRemainExternOnly/oak_measured_value",
        "TestCRuntimeHostHooksRemainExternOnly/oak_test_host_launch_begin",
        "TestCRuntimeHostHooksRemainExternOnly/oak_test_host_launch_arg",
        "TestCRuntimeHostHooksRemainExternOnly/oak_test_host_launch_out",
        "TestCRuntimeHostHooksRemainExternOnly/oak_test_host_launch_end",
        "TestCRuntimeHostHooksRemainExternOnly/oak_test_host_dispatch_divergence",
        "TestCRuntimeHostHooksRemainExternOnly/oak_test_host_fail",
        "TestCRuntimeHostHooksRemainExternOnly/oak_test_host_fail_values",
        "TestCRuntimeHostHooksRemainExternOnly/oak_test_host_discard",
        "TestCRuntimeHostHooksRemainExternOnly/oak_test_host_classify",
        "TestCRuntimeHostHooksRemainExternOnly/oak_test_host_liveness",
        "TestCRuntimeHostHooksRemainExternOnly/oak_test_host_trace",
        "TestCRuntimeHostHooksRemainExternOnly/oak_test_host_command",
        "TestCRuntimeHostHooksRemainExternOnly/oak_test_host_command_limit",
        "TestE2ETestingHostRuntimeSymbolsPreserveABI",
        "TestE2ETestingHostRuntimeSymbolsPreserveABI/simulation=false",
        "TestE2ETestingHostRuntimeSymbolsPreserveABI/simulation=true",
        "TestCDispatchTemporariesAvoidCallableShadowing",
        "TestCDispatchTemporariesAvoidCallableShadowing/-O0",
        "TestCDispatchTemporariesAvoidCallableShadowing/-O2",
        "TestE2CLaunchTemporariesAvoidCallableShadowing",
        "TestE2CLaunchTemporariesAvoidCallableShadowing/-O0",
        "TestE2CLaunchTemporariesAvoidCallableShadowing/-O2",
        "TestCFunctionDefinitionLookup",
    )),
    "c-symbol-typechecker": Suite("./typechecker", "10m", (
        "TestCFunctionSymbolsPreserveCompatibleABI",
        "TestCFunctionRuntimeEscapesAreInjective",
        "TestCFunctionRuntimeFamilies",
    )),
    "reader-apdu": Suite("./compiler", "10m", (
        "TestE2EStdlibBoundedReader",
        "TestE2EStdlibCommandAPDUMatrix",
        "TestE2EStdlibCommandAPDUMaximumAndPayloads",
        "TestE2EStdlibCommandAPDUBufferNonMutation",
        "TestE2EStdlibCommandAPDUGuardPages",
    )),
    "cross-compiler": Suite("./compiler", "15m", (
        "TestE2EInferredValueNativeRV64UnderQEMU",
        "TestE2EDispatchSelectsSVEUnderQEMU",
        "TestE2EFreestandingPartialLink",
        "TestE2ENativeConstantTablesExecutable",
        "TestE2ENativeConstantTablesExecutable/freestanding/riscv64",
        "TestE2ENativeConstantTablesExecutable/freestanding/arm64",
        "TestRingsCrossTargets",
        "TestRingsCrossTargets/linux/riscv64",
        "TestRingsCrossTargets/linux/arm64",
    )),
    "cross-testrunner": Suite("./testrunner", "10m", (
        "TestForeignTargetRunsUnderEmulator",
        "TestTargetFlagBuildsWithoutRunning",
    )),
    "lean-compiler": Suite("./compiler", "10m", (
        "TestLeanFloatBitsAgreeWithHost",
        "TestE2ELeanFunctionArguments",
        "TestE2ELeanFunctionArguments/Lean",
        "TestE2ELeanReduceLanesFunctionArgument",
        "TestE2ELeanReduceLanesFunctionArgument/Lean",
        "TestE2ELeanNestedAssignment",
        "TestE2ELeanNestedAssignment/Lean",
    )),
    "lean-cli": Suite(".", "10m", (
        "TestBuildLeanNamespace",
        "TestBuildLeanNamespace/LeanImports",
    )),
    "sail-source": Suite("./asm", "10m", (
        "TestSailArmBRKDispatchSource",
        "TestSailArmCBZ32DispatchSource",
        "TestScalarADDPPinnedSailContract",
        "TestScalarADDPPinnedSailContract/vector_reduce_add_sisd_decode",
        "TestScalarADDPPinnedSailContract/vector_reduce_add_sisd",
        "TestScalarADDPPinnedSailContract/Reduce",
        "TestScalarADDPPinnedSailContract/aset_V",
    )),
    "llvm": Suite("./asm", "10m", (
        "TestEncoderAgainstLLVM",
        "TestEncoderFuzzAgainstLLVM",
        "TestEncodeFunctionAgainstLLVM",
        "TestObjectsAgainstLLVMTools",
        "TestObjectsAgainstLLVMTools/macho",
        "TestObjectsAgainstLLVMTools/elf",
        "TestSMEAgainstLLVM",
        "TestSystemRegistersAgainstLLVM",
    )),
}


class RequiredResults:
    def __init__(self, suite):
        self.suite = suite
        self.passed = set()
        self.running = set()
        self.package_passed = False
        self.errors = []

    def accept(self, event):
        if not isinstance(event, dict):
            raise ValueError("Go test JSON event is not an object")
        action = event.get("Action")
        if action not in {"start", "run", "pause", "cont", "pass", "bench", "fail", "output", "skip"}:
            raise ValueError(f"unknown Go test action: {action!r}")
        if event.get("Package") != self.suite.import_path:
            raise ValueError(f"unexpected Go test package: {event.get('Package')!r}")
        name = event.get("Test", "")
        if not isinstance(name, str):
            raise ValueError("invalid Go test name")
        if name and name.split("/", 1)[0] not in self.suite.roots:
            raise ValueError(f"unexpected selected test: {name}")
        if action == "run" and name:
            if name in self.running or name in self.passed:
                raise ValueError(f"duplicate test run: {name}")
            self.running.add(name)
        if action in {"pass", "skip", "fail"} and name:
            if name not in self.running:
                raise ValueError(f"test finished without a run event: {name}")
            self.running.remove(name)
        if action in {"skip", "fail"}:
            self.errors.append(f"{name or self.suite.package}: {action}")
        elif action == "pass":
            if name:
                self.passed.add(name)
            else:
                self.package_passed = True
        if "Output" in event and not isinstance(event["Output"], str):
            raise ValueError("invalid Go test output")

    def finish(self, returncode):
        errors = list(self.errors)
        if returncode != 0:
            errors.append(f"go test exited {returncode}")
        if self.running:
            errors.append("tests did not finish: " + ", ".join(sorted(self.running)))
        missing = set(self.suite.tests) - self.passed
        if missing:
            errors.append("required tests did not pass: " + ", ".join(sorted(missing)))
        if not self.package_passed:
            errors.append("package did not pass")
        if errors:
            raise ValueError("\n".join(errors))


def check_inventory(suite):
    # Go itself evaluates this regex; renames/removals must not silently turn
    # a required command into a successful no-tests run.
    output = subprocess.check_output(
        ["go", "test", suite.package, "-list", suite.pattern], text=True,
    )
    names = [line for line in output.splitlines() if line.startswith("Test")]
    if sorted(names) != suite.roots:
        raise ValueError(f"{suite.package}: expected {suite.roots}, selected {names}")


def run_suite(suite, *, race=False, env=None):
    command = ["go", "test", "-json", "-count=1", *(["-race"] if race else []), "-timeout=" + suite.timeout,
               suite.package, "-run", suite.pattern]
    print("Required backend checks: " + " ".join(command), flush=True)
    results = RequiredResults(suite)
    # Merge stderr so compiler/process errors cannot escape JSON validation.
    with subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                          text=True, encoding="utf-8", env=env) as process:
        try:
            for line in process.stdout:
                try:
                    event = json.loads(line)
                except ValueError as error:
                    raise ValueError(f"invalid Go test JSON: {line.rstrip()}") from error
                results.accept(event)
                if "Output" in event:
                    print(event["Output"], end="", flush=True)
            returncode = process.wait()
        except BaseException:
            process.terminate()
            process.wait()
            raise
    results.finish(returncode)
    print(f"Required backend checks passed: {len(suite.tests)} named checks; no skips", flush=True)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("suite", choices=SUITES, nargs="?")
    parser.add_argument("--check", action="store_true", help="validate all selectors against Go")
    args = parser.parse_args(argv)
    if not args.check and args.suite is None:
        parser.error("choose a suite or --check")
    try:
        if args.check:
            for name, suite in SUITES.items():
                check_inventory(suite)
                print(f"{name}: {len(suite.roots)} roots selected exactly", flush=True)
        else:
            run_suite(SUITES[args.suite],
                      race=args.suite in {"c-symbol-compiler", "c-symbol-typechecker", "asm-memory-markers"})
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        print(f"Required backend checks FAILED: {error}", file=sys.stderr, flush=True)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
