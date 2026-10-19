#!/usr/bin/env python3
"""Require exact source/full-artifact proof inventories and kernel trust reports.

This small gate shares the native-object gate's strict report parser without
changing that gate or its pinned fixture inventory. It grants no production
verification authority.
"""
from pathlib import Path
import re

from native_object_fixtures import check as native


ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / "spec" / "lean"
MODEL = tuple("Oak.BitwiseSourceObjectParity." + name for name in (
    "check_sound",
    "accepts_iff",
    "refuses_unsupported",
    "refuses_outside_grammar",
    "refuses_source_replay",
    "accepted_source_object_binding",
    "accepted_all_input_success",
))
FIXTURES = tuple("Oak.BitwiseSourceObjectParityFixtures." + name for name in (
    "accepted_and",
    "accepted_or",
    "accepted_xor",
    "refuses_wrong_source_operation",
    "refuses_wrong_source_name",
    "refuses_wrong_wasm_operation",
    "refuses_wrong_arm_operation",
    "refuses_wrong_rv_operation",
    "refuses_wrong_arm_symbol",
    "refuses_wrong_rv_symbol",
    "refuses_swapped_architectures",
    "refuses_extra_arm_byte",
    "refuses_extra_rv_byte",
    "refuses_extra_wasm_byte",
    "refuses_unsupported_type",
    "refuses_unsupported_parameter_reference",
    "refuses_unsupported_second_declaration",
    "refuses_unsupported_comment",
    "accepted_consistent_rename",
))
EXPECTED = MODEL + FIXTURES


def require_inventory(kind, actual, expected):
    actual = tuple(actual)
    if not expected or len(expected) != len(set(expected)) or actual != expected:
        raise SystemExit("Changed, missing, or duplicate source-object " + kind + " inventory")


def validate_inventories():
    for kind, filename, expected in (
        ("model", "BitwiseSourceObjectParity.lean", MODEL),
        ("fixtures", "BitwiseSourceObjectParityFixtures.lean", FIXTURES),
    ):
        lines = (LEAN / "Oak" / filename).read_text().splitlines()
        require_inventory(kind, native.inventory(lines).values(), expected)
    queries = re.findall(r"^#print axioms (\S+)$",
                         (LEAN / "Oak" / "BitwiseSourceObjectParityAudit.lean").read_text(),
                         re.M)
    require_inventory("audit queries", queries, EXPECTED)


def main():
    validate_inventories()
    native.run(["lake", "build", "Oak.BitwiseSourceObjectParityFixtures"])
    output = native.run(["lake", "env", "lean", "-j1",
                         "Oak/BitwiseSourceObjectParityAudit.lean"])
    native.audit_reports(output, EXPECTED)
    print("PASS: 7 source-object composition theorems, 4 admissions, 15 refusals; "
          "26 exact theorem-closure reports; allowed axioms only.")


if __name__ == "__main__":
    main()
