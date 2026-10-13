"""Finite synthetic controls for the fixed hosted refinement audit consumer.

SOURCE ONLY: this file has not been imported, compiled, parsed, or executed.
Run only under separate execution authorization. This harness imports the
actual refinement_audit_consumer and support modules, never check.py or Lean.
Subprocess entry points are patched to refuse throughout imports and tests.
The supplied contract is read as bounded JSON; no source-contract generation
or target evaluation occurs. Fixtures are protocol data, not Lean evidence.

Ordinary fixtures: 1,628 records, 756 nodes, 123 edge occurrences, <=2 MiB
encoded diagnostics. Explicit limit probes are capped at 2,001 candidates,
10,001 nodes, 100,001 names in one array, 100,118 combined edge occurrences,
12,120 lines, or 12 MiB + 1 bytes. No filesystem fixture trees are created.
"""
import argparse
import copy
from contextlib import ExitStack
import importlib
import json
import os
from pathlib import Path
import subprocess
import sys
import unittest
from unittest import mock


ADAPTER = None
CONSUMER = None
SUPPORT = None
CONTRACT = None
DEADLINE = 20.0
HELPER_PREFIX = "RefinementControl.helper"


def encode(value):
    return json.dumps(value, separators=(",", ":"), ensure_ascii=True).encode("utf-8")


def fixture(contract):
    """756 nodes; shared cycles and repeated edges are intentionally valid."""
    allowed = sorted(CONSUMER.ALLOWED)
    helpers = [HELPER_PREFIX + str(i) for i in range(636)]
    theorems = []
    candidates = []
    for row in contract["expected"]["theorems"]:
        common = {
            "owner": row["module"], "user_name": row["qualified_name"],
            "actual_name": row["qualified_name"], "axioms": list(allowed),
            "direct_dependencies": [helpers[0]],
        }
        theorems.append(dict(common, record="expected_theorem", private=row["private"]))
        candidates.append(dict(common, record="candidate_declaration", kind="theorem"))
    for i, name in enumerate(helpers):
        deps = allowed + [helpers[1], allowed[0]] if i == 0 else [helpers[0]] if i == 1 else []
        candidates.append({
            "record": "candidate_declaration", "owner": "Oak.Stdlib.BoundedReaderExtracted",
            "actual_name": name, "user_name": name, "kind": "definition",
            "axioms": list(allowed) if i < 2 else [], "direct_dependencies": deps,
        })
    nodes = [
        {"record": "dependency", "actual_name": r["actual_name"],
         "kind": r["kind"], "direct_dependencies": list(r["direct_dependencies"])}
        for r in candidates
    ]
    nodes.extend({"record": "dependency", "actual_name": n, "kind": "axiom",
                  "direct_dependencies": []} for n in allowed)
    complete = {
        "record": "complete", "expected_theorems": 117,
        "candidate_declarations": 753, "dependency_nodes": len(nodes),
        "dependency_edges": sum(len(n["direct_dependencies"]) for n in nodes),
        "anonymous_examples_persisted": False,
        "anonymous_examples_accounted_by_exact_source_compile": 0,
    }
    imports = list(contract["distribution_modules"]) + sorted(CONSUMER.MODULES)
    return [{"record": "imports", "modules": imports}] + theorems + candidates + nodes + [complete]


def select(records, kind):
    return [r for r in records if r["record"] == kind]


def reconcile_counts(records):
    """Adjust counters after a structural mutation, exposing deeper checks."""
    complete = records[-1]
    nodes = select(records, "dependency")
    complete["candidate_declarations"] = len(select(records, "candidate_declaration"))
    complete["dependency_nodes"] = len(nodes)
    complete["dependency_edges"] = sum(len(r["direct_dependencies"]) for r in nodes)


def diagnostic(record):
    return {
        "fileName": str(ADAPTER / "RefinementAuditDriver.lean"),
        "pos": {"line": 1, "column": 0}, "endPos": {"line": 1, "column": 0},
        "keepFullRange": False, "severity": "information", "isSilent": False,
        "caption": "", "data": CONSUMER.PREFIX + encode(record).decode("utf-8"),
        "kind": "[anonymous]",
    }


def stream(records):
    result = b"".join(encode(diagnostic(r)) + b"\n" for r in records)
    if len(result) > 2 * 1024**2:
        raise AssertionError("synthetic diagnostic fixture exceeds 2 MiB")
    return result


class RefinementConsumerControls(unittest.TestCase):
    def setUp(self):
        self.records = fixture(CONTRACT)
        self.clock = mock.patch.object(CONSUMER.time, "monotonic", return_value=10.0)
        self.clock.start()
        self.addCleanup(self.clock.stop)

    def accept(self, records=None, contract=None):
        return CONSUMER.audit_records(self.records if records is None else records,
                                      DEADLINE, CONTRACT if contract is None else contract)

    def reject(self, message, records=None, contract=None):
        with self.assertRaisesRegex(RuntimeError, message):
            self.accept(records, contract)

    def diagnostics(self, stdout, stderr=b"", phase="audit"):
        return CONSUMER.diagnostics(stdout, stderr, phase, DEADLINE,
                                    ADAPTER / "RefinementAuditDriver.lean", CONTRACT)

    def test_valid_complete_shared_cyclic_graph_and_duplicate_edges(self):
        result = self.accept()
        self.assertIs(result["accepted"], True)
        self.assertEqual(result["schema"], "oak-reader-refinement-formal-audit-acceptance-v1")
        self.assertEqual((result["named_theorems"], result["source_examples"],
                          result["named_controls"], result["candidate_declarations"],
                          result["actual_imports"]), (117, 0, 18, 753, 1050))
        self.assertEqual((result["dependency_nodes"], result["dependency_edges"]), (756, 123))
        self.assertEqual((result["independent_processed_nodes"],
                          result["independent_edge_occurrences"]), (1458, 942))
        self.assertIs(result["generated_definition_refinement_established"], True)
        self.assertIs(result["oak_implementation_refinement_established"], False)
        self.assertIs(result["implementation_refinement_established"], False)
        self.assertIs(result["anonymous_examples_persisted"], False)

    def test_fixed_contextual_identity(self):
        self.assertEqual(CONSUMER.PREFIX, "OAK_READER_REFINEMENT_AUDIT ")
        self.assertEqual(CONSUMER.MODULES, {
            "Oak.Stdlib.BoundedReaderModel", "Oak.Stdlib.BoundedReaderExtracted",
            "Oak.Stdlib.BoundedReaderRefinement"})
        rows = CONTRACT["expected"]["theorems"]
        self.assertEqual(len(rows), 117)
        self.assertTrue(all(r["private"] is False for r in rows))
        self.assertEqual(sum(r["module"] == "Oak.Stdlib.BoundedReaderModel" for r in rows), 18)
        controls = "Oak.Stdlib.BoundedReaderRefinement.Controls."
        self.assertEqual(sum(r["qualified_name"].startswith(controls) for r in rows), 18)
        self.assertEqual(sum(r["module"] == "Oak.Stdlib.BoundedReaderRefinement" and
                             not r["qualified_name"].startswith(controls) for r in rows), 81)
        self.assertEqual(CONTRACT["expected"]["anonymous_controls"], [])

    def test_valid_complete_diagnostics_and_empty_compiles(self):
        self.assertIs(self.diagnostics(stream(self.records))["accepted"], True)
        for phase in ("reader", "extracted", "refinement"):
            with self.subTest(phase=phase):
                self.assertIsNone(self.diagnostics(b"", phase=phase))

    def test_contract_inventory_drift(self):
        for mutation in ("missing-theorem", "duplicate-theorem", "anonymous-control",
                         "missing-distribution", "extra-distribution"):
            with self.subTest(mutation=mutation):
                contract = copy.deepcopy(CONTRACT)
                if mutation == "missing-theorem":
                    contract["expected"]["theorems"].pop()
                elif mutation == "duplicate-theorem":
                    contract["expected"]["theorems"][1] = contract["expected"]["theorems"][0]
                elif mutation == "anonymous-control":
                    contract["expected"]["anonymous_controls"].append({"synthetic": True})
                elif mutation == "missing-distribution":
                    contract["distribution_modules"].pop()
                else:
                    contract["distribution_modules"].append("Unexpected.Module")
                reason = "exact distribution module graph" if "distribution" in mutation else "117 exact theorems and0 source examples"
                self.reject(reason, contract=contract)

    def test_wrong_candidate_inventory_even_with_reconciled_counts(self):
        for delta in (-1, 1):
            with self.subTest(delta=delta):
                rows = copy.deepcopy(self.records)
                if delta < 0:
                    name = select(rows, "candidate_declaration")[-1]["actual_name"]
                    rows = [r for r in rows if r.get("actual_name") != name]
                else:
                    extra = copy.deepcopy(select(rows, "candidate_declaration")[-1])
                    extra["actual_name"] = extra["user_name"] = "RefinementControl.extra"
                    rows.insert(871, extra)
                    rows.insert(-1, {"record": "dependency", "actual_name": "RefinementControl.extra",
                                     "kind": "definition", "direct_dependencies": []})
                reconcile_counts(rows)
                self.reject("complete inventories", rows)

    def test_missing_and_replaced_import(self):
        for replacement in (None, "Unexpected.Module"):
            with self.subTest(replacement=replacement):
                rows = copy.deepcopy(self.records)
                rows[0]["modules"].pop()
                if replacement is not None:
                    rows[0]["modules"].append(replacement)
                self.reject("exact actual imported module set", rows)

    def test_duplicate_import(self):
        self.records[0]["modules"][-1] = self.records[0]["modules"][0]
        self.reject("duplicate name forbidden")

    def test_duplicate_missing_and_reordered_theorem(self):
        for section, start in (("model", 1), ("general", 19), ("named-control", 100)):
            for mutation in ("duplicate", "missing", "reordered"):
                with self.subTest(section=section, mutation=mutation):
                    rows = copy.deepcopy(self.records)
                    if mutation == "duplicate":
                        rows[start + 1] = copy.deepcopy(rows[start])
                    elif mutation == "missing":
                        del rows[start]
                    else:
                        rows[start], rows[start + 1] = rows[start + 1], rows[start]
                    self.reject("unique exact theorem resolution", rows)

    def test_wrong_owner_user_name_and_privacy(self):
        for field, value in (("owner", "Other.Module"),
                             ("user_name", "Wrong.theorem"), ("private", True)):
            with self.subTest(field=field):
                rows = copy.deepcopy(self.records)
                rows[1][field] = value
                self.reject("unique exact theorem resolution", rows)

    def test_public_actual_name(self):
        self.records[1]["actual_name"] = "Unexpected.name"
        self.reject("public theorem exact actual name")

    def test_exact_private_boolean(self):
        self.records[1]["private"] = 0
        self.reject("exact private boolean")

    def test_duplicate_candidate_and_node(self):
        for kind, message in (("candidate_declaration", "unique safe candidate ownership/kind"),
                              ("dependency", "unique approved dependency kind")):
            with self.subTest(kind=kind):
                rows = copy.deepcopy(self.records)
                members = select(rows, kind)
                members[1]["actual_name"] = members[0]["actual_name"]
                self.reject(message, rows)

    def test_candidate_wrong_owner_axiom_kind_and_forbidden_name(self):
        for field, value in (("owner", "Other.Module"), ("kind", "axiom"),
                             ("actual_name", "sorryAx")):
            with self.subTest(field=field):
                rows = copy.deepcopy(self.records)
                select(rows, "candidate_declaration")[-1][field] = value
                self.reject("unique safe candidate ownership/kind", rows)

    def test_forbidden_and_unapproved_dependency(self):
        for name in ("sorryAx", "Lean.trustCompiler", "Lean.ofReduceBool", "Lean.ofReduceNat",
                     "Lean.reduceBool", "Lean.reduceNat", "Unapproved.axiom"):
            with self.subTest(name=name):
                rows = copy.deepcopy(self.records)
                node = select(rows, "dependency")[-1]
                node["actual_name"] = name
                node["kind"] = "axiom"
                self.reject("unique approved dependency kind", rows)

    def test_unapproved_and_duplicate_axiom_claim(self):
        for kind in ("expected_theorem", "candidate_declaration"):
            for axioms, message in ((["Unapproved.axiom"], "only approved foundational axioms"),
                                     (["propext", "propext"], "duplicate name forbidden")):
                with self.subTest(kind=kind, axioms=axioms):
                    rows = copy.deepcopy(self.records)
                    select(rows, kind)[0]["axioms"] = axioms
                    self.reject(message, rows)

    def test_theorem_candidate_kind_mismatch(self):
        candidate = select(self.records, "candidate_declaration")[0]
        candidate["kind"] = "definition"
        node = next(r for r in select(self.records, "dependency") if r["actual_name"] == candidate["actual_name"])
        node["kind"] = "definition"
        self.reject("theorem/candidate record equality")

    def test_candidate_shared_graph_mismatch(self):
        for field, value in (("direct_dependencies", []), ("kind", "definition"),
                             ("missing-node", None)):
            with self.subTest(field=field):
                rows = copy.deepcopy(self.records)
                if field == "missing-node":
                    name = HELPER_PREFIX + "635"
                    rows = [r for r in rows if not
                            (r.get("record") == "dependency" and r.get("actual_name") == name)]
                    reconcile_counts(rows)
                else:
                    select(rows, "candidate_declaration")[0][field] = value
                self.reject("candidate and shared graph equality", rows)

    def test_theorem_candidate_record_mismatch(self):
        for field, value in (("user_name", "Wrong.name"),
                             ("owner", "Oak.Stdlib.BoundedReaderExtracted"), ("axioms", [])):
            with self.subTest(field=field):
                rows = copy.deepcopy(self.records)
                select(rows, "candidate_declaration")[0][field] = value
                self.reject("theorem/candidate record equality", rows)

    def test_missing_referenced_dependency(self):
        self.records = [r for r in self.records if r.get("actual_name") != "propext"]
        reconcile_counts(self.records)
        self.reject("every referenced dependency present")

    def test_unreachable_extra_dependency(self):
        self.records.insert(-1, {"record": "dependency", "actual_name": "Unreachable.extra",
                                 "kind": "definition", "direct_dependencies": []})
        reconcile_counts(self.records)
        self.reject("no extra or missing combined dependency node")

    def test_independent_theorem_axiom_disagreement(self):
        self.records[1]["axioms"] = []
        select(self.records, "candidate_declaration")[0]["axioms"] = []
        self.reject("independent theorem reachable axioms")

    def test_missing_duplicate_and_nonfinal_sentinel(self):
        for mutation, message in (("missing", "complete inventories"),
                                   ("duplicate", "exactly one last complete sentinel"),
                                   ("nonfinal", "exactly one last complete sentinel")):
            with self.subTest(mutation=mutation):
                rows = copy.deepcopy(self.records)
                if mutation == "missing":
                    rows.pop()
                elif mutation == "duplicate":
                    rows.append(copy.deepcopy(rows[-1]))
                else:
                    rows.append(copy.deepcopy(rows[-2]))
                self.reject(message, rows)

    def test_sentinel_counter_mismatch_and_boolean_integer(self):
        for field in ("expected_theorems", "candidate_declarations", "dependency_nodes",
                      "dependency_edges", "anonymous_examples_accounted_by_exact_source_compile"):
            for value, message in ((True, "completion integer counters"),
                                    (-1, "completion reconciliation")):
                with self.subTest(field=field, value=value):
                    rows = copy.deepcopy(self.records)
                    rows[-1][field] = value
                    self.reject(message, rows)

    def test_persisted_example_claim(self):
        for value in (True, 0):
            with self.subTest(value=value):
                rows = copy.deepcopy(self.records)
                rows[-1]["anonymous_examples_persisted"] = value
                self.reject("examples do not persist", rows)

    def test_record_schema_and_section_order(self):
        for mutation, message in (("unknown-key", "exact audit record schema"),
                                   ("wrong-order", "candidate section/order/count"),
                                   ("unknown-record", "unknown audit record"),
                                   ("non-record", "audit original deadline/record type")):
            with self.subTest(mutation=mutation):
                rows = copy.deepcopy(self.records)
                if mutation == "unknown-key":
                    rows[1]["unknown"] = None
                elif mutation == "wrong-order":
                    rows[1], rows[118] = rows[118], rows[1]
                elif mutation == "unknown-record":
                    rows[1]["record"] = "unknown"
                else:
                    rows[1] = None
                self.reject(message, rows)

    def test_candidate_and_dependency_inventory_caps(self):
        for kind, cap, message in (("candidate_declaration", 2000, "candidate section/order/count"),
                                   ("dependency", 10000, "dependency section/order/count")):
            with self.subTest(kind=kind):
                rows = copy.deepcopy(self.records)
                members = select(rows, kind)
                extras = []
                for i in range(cap + 1 - len(members)):
                    extra = copy.deepcopy(members[-1])
                    extra["actual_name"] = "RefinementControl.cap" + str(i)
                    extra["kind"] = "definition"
                    extra["direct_dependencies"] = []
                    if kind == "candidate_declaration":
                        extra["user_name"] = extra["actual_name"]
                    extras.append(extra)
                insertion = 871 if kind == "candidate_declaration" else len(rows) - 1
                rows[insertion:insertion] = extras
                self.reject(message, rows)

    def test_name_array_and_combined_edge_caps(self):
        for mutation, message in (("single-array", "finite name-array bound"),
                                   ("combined-edges", "combined edge-occurrence cap")):
            with self.subTest(mutation=mutation):
                rows = copy.deepcopy(self.records)
                count = 100001 if mutation == "single-array" else 100000
                deps = ["propext"] * count
                for record in rows:
                    if record.get("actual_name") == HELPER_PREFIX + "0":
                        record["direct_dependencies"] = deps
                reconcile_counts(rows)
                self.reject(message, rows)

    def test_empty_truncated_and_extra_blank_diagnostic_stream(self):
        raw = stream(self.records)
        for output, message in ((b"", "complete bounded audit stdout"),
                                (raw[:-1], "complete bounded audit stdout"),
                                (raw + b"\n", "audit parsing original deadline/empty line")):
            with self.subTest(message=message):
                with self.assertRaisesRegex(RuntimeError, message):
                    self.diagnostics(output)

    def test_diagnostic_byte_and_record_caps(self):
        for mutation, message in (("bytes", "complete bounded audit stdout"),
                                   ("records", "finite complete audit message count")):
            with self.subTest(mutation=mutation):
                raw = b"x" * 12582912 + b"\n" if mutation == "bytes" else b"{}\n" * 12120
                with self.assertRaisesRegex(RuntimeError, message):
                    self.diagnostics(raw)

    def test_unexpected_compile_stdout_and_any_stderr(self):
        for phase in ("reader", "extracted", "refinement"):
            with self.subTest(phase=phase):
                with self.assertRaisesRegex(RuntimeError, "reader/refinement must have no diagnostics"):
                    self.diagnostics(b"warning\n", phase=phase)
        with self.assertRaisesRegex(RuntimeError, "complete stderr must be empty"):
            self.diagnostics(stream(self.records), b"warning\n")

    def test_diagnostic_identity_severity_and_schema(self):
        for field, value in (("fileName", "/wrong/RefinementAuditDriver.lean"),
                             ("severity", "warning"), ("isSilent", True),
                             ("keepFullRange", True), ("caption", "unexpected"),
                             ("kind", "unexpected"), ("data", "OAK_APDU_AUDIT {}"),
                             ("data", 0)):
            with self.subTest(field=field, value=value):
                message = diagnostic(self.records[0])
                message[field] = value
                with self.assertRaisesRegex(RuntimeError, "only exact driver informational audit messages"):
                    self.diagnostics(encode(message) + b"\n")
        message = diagnostic(self.records[0])
        del message["endPos"]
        with self.assertRaisesRegex(RuntimeError, "exact audit record schema"):
            self.diagnostics(encode(message) + b"\n")

    def test_diagnostic_position_requires_bounded_integer(self):
        for field in ("pos", "endPos"):
            for value in (True, -1, 2 ** 32, 1.5):
                with self.subTest(field=field, value=value):
                    message = diagnostic(self.records[0])
                    message[field]["line"] = value
                    with self.assertRaisesRegex(RuntimeError, "message position"):
                        self.diagnostics(encode(message) + b"\n")

    def test_duplicate_outer_and_inner_json_keys(self):
        message = diagnostic(self.records[0])
        outer = encode(message).replace(b'"severity":"information"',
                                         b'"severity":"warning","severity":"information"')
        message["data"] = CONSUMER.PREFIX + '{"record":"imports","record":"imports"}'
        for raw in (outer, encode(message)):
            with self.subTest(raw_kind="outer" if raw == outer else "inner"):
                with self.assertRaisesRegex(RuntimeError, "duplicate JSON key"):
                    self.diagnostics(raw + b"\n")

    def test_original_deadline_during_records_and_stream(self):
        with mock.patch.object(CONSUMER.time, "monotonic", return_value=DEADLINE):
            self.reject("audit original deadline/record type")
            with self.assertRaisesRegex(RuntimeError, "complete stderr must be empty"):
                self.diagnostics(stream(self.records))

    def test_original_deadline_during_graph_reconstruction(self):
        with mock.patch.object(CONSUMER.time, "monotonic",
                               side_effect=[10.0] * (len(self.records) - 1) + [DEADLINE]):
            self.reject("graph reconstruction original deadline")


def main():
    global ADAPTER, CONSUMER, SUPPORT, CONTRACT
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--adapter", type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument("--contract", type=Path, required=True)
    options, remaining = parser.parse_known_args()
    ADAPTER = options.adapter.resolve()
    sys.dont_write_bytecode = True
    sys.path.insert(0, str(ADAPTER))
    refusal = AssertionError("subprocess execution is outside synthetic consumer controls")
    with ExitStack() as patches:
        for name in ("Popen", "run", "call", "check_call", "check_output"):
            patches.enter_context(mock.patch.object(subprocess, name, side_effect=refusal))
        patches.enter_context(mock.patch.object(os, "system", side_effect=refusal))
        SUPPORT = importlib.import_module("support")
        CONSUMER = importlib.import_module("refinement_audit_consumer")
        if Path(CONSUMER.__file__).resolve() != ADAPTER / "refinement_audit_consumer.py":
            raise RuntimeError("actual selected refinement consumer module required")
        if Path(SUPPORT.__file__).resolve() != ADAPTER / "support.py":
            raise RuntimeError("actual selected support module required")
        CONTRACT = SUPPORT.decode(SUPPORT.read_regular(options.contract.resolve(), 2 * 1024**2))
        unittest.main(argv=[sys.argv[0], *remaining])


if __name__ == "__main__":
    main()
