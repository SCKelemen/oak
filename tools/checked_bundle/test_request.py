#!/usr/bin/env python3
"""Bounded, single-threaded adversarial regression for the fixed Lean auditor.

Run from anywhere with the pinned Lean 4.33.1 toolchain on PATH. Requires the
trusted model/auditor to have been built; does not authenticate reused imports.
"""
from pathlib import Path
import json
import os
import signal
import subprocess
import sys
import tempfile
import time
import unittest

from request import LIMITS, render

ROOT = Path(__file__).resolve().parents[2]
LEAN = ROOT / "spec" / "lean"
FIXTURES = Path(__file__).resolve().parent / "fixtures"
NAMES = ["source.oak", "module.wasm", "arm.o", "rv.o"]
ROOTS = ["Oak.CheckedBundleRequest." + n for n in ("admitted", "binding", "all_inputs")]
ALLOWED = {"propext", "Quot.sound", "Classical.choice"}
EXPECTED_METHODS = {
    "LeanAuditTests.test_kernel_policy_guards",
    "LeanAuditTests.test_mismatched_source_and_artifacts",
    "LeanAuditTests.test_missing_roots",
    "LeanAuditTests.test_positive_real_production_bundle",
    "LeanAuditTests.test_sorry_and_forbidden_axiom",
    "LeanAuditTests.test_valid_record_followed_by_failure_is_not_accepted",
    "LeanAuditTests.test_wrong_kind_and_universe",
    "LeanAuditTests.test_wrong_types_and_false_antecedent",
    "RendererTests.test_bounds_and_immutable_input",
    "RendererTests.test_no_code_interpolation",
}
EXPECTED_CASES = {
    "skip_kernel", "trust_nonzero", "mismatch_source", "mismatch_wasm", "mismatch_arm", "mismatch_rv",
    "semantic_refusal_source", "semantic_refusal_wasm", "semantic_refusal_arm", "semantic_refusal_rv",
    "missing_admitted", "missing_binding", "missing_all_inputs", "positive", "sorry", "forbidden_axiom",
    "native_decide", "late_failure", "wrong_kind", "unexpected_universe", "wrong_type_binding",
    "false_antecedent_binding", "wrong_type_all_inputs", "false_antecedent_all_inputs",
}
SCHEMA = {"schema", "profile", "proof_package", "lean_version", "source", "wasm", "arm", "rv", "declaration", "roots"}


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError("duplicate JSON key")
        result[key] = value
    return result


def admitted_record(proc, inputs):
    """Test consumer only. Exit and full output both participate in acceptance."""
    if proc.returncode != 0:
        raise ValueError("Lean process did not exit successfully")
    data = json.loads(proc.stdout, object_pairs_hook=unique_object)
    if type(data) is not dict or set(data) != SCHEMA:
        raise ValueError("wrong record schema")
    if (data["schema"], data["profile"], data["proof_package"], data["lean_version"]) != (
        "oak.checked-bundle.v1", "bitwise-source-wasm-arm64-rv64-v1",
        "698f6a7b013df508a831d391fe425f4f27cf4581", "4.33.1"):
        raise ValueError("wrong record identity")
    for name, raw in zip(LIMITS, inputs, strict=True):
        if type(data[name]) is not list or any(type(n) is not int or not 0 <= n <= 255 for n in data[name]):
            raise ValueError("wrong byte type")
        if data[name] != list(raw):
            raise ValueError("byte replay/mismatch")
    if type(data["roots"]) is not list or len(data["roots"]) != 3:
        raise ValueError("missing root")
    for root, name in zip(data["roots"], ROOTS, strict=True):
        if type(root) is not dict or set(root) != {"name", "axioms"} or root["name"] != name:
            raise ValueError("wrong root inventory")
        axioms = root["axioms"]
        if type(axioms) is not list or any(type(a) is not str for a in axioms):
            raise ValueError("wrong axiom inventory")
        if len(set(axioms)) != len(axioms) or not set(axioms) <= ALLOWED:
            raise ValueError("forbidden/duplicate axiom")
    if data["declaration"] != {"name": list(b"bitwise"), "first": [120], "second": [121], "op": "and"}:
        raise ValueError("wrong checked declaration")
    return data


class RendererTests(unittest.TestCase):
    def test_no_code_interpolation(self):
        attack = b'"\nend Oak.CheckedBundleRequest\naxiom nope : False\n'
        text = render(attack, b"x", b"y", b"z")
        self.assertNotIn("axiom nope", text)
        self.assertIn(",".join(map(str, attack)), text)

    def test_bounds_and_immutable_input(self):
        for index, limit in enumerate(LIMITS.values()):
            for bad in (b"", b"x" * (limit + 1), bytearray(b"x")):
                data = [b"x"] * 4
                data[index] = bad
                with self.assertRaises((ValueError, TypeError)):
                    render(*data)


class LeanAuditTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.inputs = [(FIXTURES / name).read_bytes() for name in NAMES]
        cls.driver = render(*cls.inputs)
        cls.temp = tempfile.TemporaryDirectory(prefix="oak-fixed-audit-")
        cls.results = []

    @classmethod
    def tearDownClass(cls):
        report = os.environ.get("OAK_AUDIT_TEST_REPORT")
        if report:
            Path(report).write_text(json.dumps(cls.results, indent=2) + "\n")
        cls.temp.cleanup()

    def run_lean(self, case, driver=None, trust="0"):
        path = Path(self.temp.name) / (case + ".lean")
        path.write_text(self.driver if driver is None else driver)
        start = time.monotonic()
        command = ["lake", "env", "lean", "-j1", "-M4096", "--trust=" + trust, str(path)]
        child = subprocess.Popen(command, cwd=LEAN, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                 text=True, start_new_session=True)
        try:
            stdout, stderr = child.communicate(timeout=240)
        except BaseException:
            # The Lake wrapper must not leave a Lean grandchild running after a
            # timeout or cancellation of this serial resource-bounded gate.
            try:
                os.killpg(child.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            child.wait()
            raise
        proc = subprocess.CompletedProcess(command, child.returncode, stdout, stderr)
        self.results.append({"case": case, "exit_code": proc.returncode,
                             "seconds": round(time.monotonic() - start, 3),
                             "stdout": proc.stdout, "stderr": proc.stderr})
        return proc

    def refuse(self, case, driver, expected=None, trust="0"):
        proc = self.run_lean(case, driver, trust)
        self.assertNotEqual(proc.returncode, 0, proc.stdout)
        self.assertNotIn('"schema":"oak.checked-bundle.v1"', proc.stdout)
        if expected:
            self.assertIn(expected, proc.stdout + proc.stderr)

    def test_positive_real_production_bundle(self):
        admitted_record(self.run_lean("positive"), self.inputs)

    def test_wrong_types_and_false_antecedent(self):
        for root in ("binding", "all_inputs"):
            old = next(line for line in self.driver.splitlines() if line.startswith("theorem " + root))
            self.refuse("wrong_type_" + root,
                        self.driver.replace(old, "theorem " + root + " : True := True.intro"),
                        "wrong exact type")
            self.refuse("false_antecedent_" + root,
                        self.driver.replace("theorem " + root + " : type_of%", "theorem " + root + " (impossible : False) : type_of%"),
                        "wrong exact type")

    def test_missing_roots(self):
        for root in ("admitted", "binding", "all_inputs"):
            old = next(line for line in self.driver.splitlines() if line.startswith("theorem " + root))
            self.refuse("missing_" + root, self.driver.replace(old, ""), "missing theorem root")

    def test_sorry_and_forbidden_axiom(self):
        self.refuse("sorry", self.driver.replace("by decide +kernel", "by sorry"), "forbidden axiom sorryAx")
        admission = next(line for line in self.driver.splitlines() if line.startswith("theorem admitted"))
        proposition = admission.split(" : ", 1)[1].split(" := ", 1)[0]
        forged = "axiom forbiddenAuthority : " + proposition + "\ntheorem admitted : " + proposition + " := forbiddenAuthority"
        self.refuse("forbidden_axiom", self.driver.replace(admission, forged), "forbidden axiom Oak.CheckedBundleRequest.forbiddenAuthority")
        self.refuse("native_decide", self.driver.replace("by decide +kernel", "by native_decide"), "forbidden axiom")

    def test_wrong_kind_and_universe(self):
        self.refuse("wrong_kind", self.driver.replace("theorem all_inputs", "def all_inputs"), "missing theorem root")
        self.refuse("unexpected_universe", self.driver.replace("theorem all_inputs", "theorem all_inputs.{u} (α : Sort u)"), "unexpected universe")

    def test_mismatched_source_and_artifacts(self):
        for index in range(4):
            data = self.inputs.copy()
            changed = bytearray(data[index])
            if index == 0:
                changed[35] = ord("|")  # valid source, a different operation
            else:
                changed[(35, 43, 64, 80)[index]] ^= 1
            data[index] = bytes(changed)
            mutated = render(*data)
            self.refuse("mismatch_" + list(LIMITS)[index], mutated)
            # A failed admission alone could be timeout/resource failure. Prove
            # the actual semantic refusal independently, in a successful process.
            negative = mutated.split("theorem admitted", 1)[0] + """theorem refused :
    Oak.BitwiseSourceObjectParity.check source wasm arm rv = none := by decide +kernel
end Oak.CheckedBundleRequest
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let some (.thmInfo _) := env.toKernelEnv.find? ``Oak.CheckedBundleRequest.refused
    | throwError "missing checked semantic refusal"
  let axioms ← collectAxioms ``Oak.CheckedBundleRequest.refused
  for axiomName in axioms do
    unless [``propext, ``Quot.sound, ``Classical.choice].contains axiomName do
      throwError "forbidden semantic-refusal axiom {axiomName}"
"""
            proc = self.run_lean("semantic_refusal_" + list(LIMITS)[index], negative)
            self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
            self.assertEqual(proc.stdout.strip(), "")

    def test_kernel_policy_guards(self):
        self.refuse("skip_kernel", self.driver.replace("set_option autoImplicit false", "set_option autoImplicit false\nset_option debug.skipKernelTC true"), "kernel checking is disabled")
        self.refuse("trust_nonzero", self.driver, "trust level must be zero", trust="1")

    def test_valid_record_followed_by_failure_is_not_accepted(self):
        proc = self.run_lean("late_failure", self.driver + "example : False := by decide\n")
        self.assertNotEqual(proc.returncode, 0)
        self.assertIn('"schema":"oak.checked-bundle.v1"', proc.stdout)
        with self.assertRaises(ValueError):
            admitted_record(proc, self.inputs)


if __name__ == "__main__":
    actual_methods = {
        cls.__name__ + "." + name
        for cls in (LeanAuditTests, RendererTests)
        for name in unittest.defaultTestLoader.getTestCaseNames(cls)
    }
    if actual_methods != EXPECTED_METHODS:
        raise SystemExit("Changed or missing fixed auditor test-method inventory")
    program = unittest.main(exit=False)
    result = program.result
    cases = [entry["case"] for entry in getattr(LeanAuditTests, "results", [])]
    complete = (result.testsRun == len(EXPECTED_METHODS)
                and len(cases) == len(EXPECTED_CASES) and set(cases) == EXPECTED_CASES
                and not result.skipped and not result.expectedFailures
                and not result.unexpectedSuccesses)
    if not result.wasSuccessful() or not complete:
        if not complete:
            print("Incomplete, duplicate, or skipped fixed auditor test coverage", file=sys.stderr)
        raise SystemExit(1)
    print(f"PASS: {len(EXPECTED_METHODS)} methods, {len(EXPECTED_CASES)} exact Lean cases, no skips")
