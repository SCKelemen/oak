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


def run_suite(suite):
    command = ["go", "test", "-json", "-count=1", "-timeout=" + suite.timeout,
               suite.package, "-run", suite.pattern]
    print("Required backend checks: " + " ".join(command), flush=True)
    results = RequiredResults(suite)
    # Merge stderr so compiler/process errors cannot escape JSON validation.
    with subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                          text=True, encoding="utf-8") as process:
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
            run_suite(SUITES[args.suite])
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        print(f"Required backend checks FAILED: {error}", file=sys.stderr, flush=True)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
