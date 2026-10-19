"""Finite controls for the actual fixed hosted refinement profile.

SOURCE ONLY until a separately authorized control run. This file has not been
imported, parsed, compiled, or run during preparation. It never starts Go, Lean,
a shell, or another process. Imports and every control run under five patched
subprocess entry points plus os.system; main cases replace host.run_lean fully.
Synthetic process/object/audit receipts are fixtures, not refinement evidence.

Run with --adapter for the staged actual modules and --repo-root for the locked
current source tree (default: check_refinement.REPO). Exact expected receipt
bytes come from the contract's receipt_utf8 and are independently checked
against its locked byte identity. No extraction or acceptance parser
is copied. Independent validation remains in the actual imported helpers.

Every method/subcase is bounded and named in SOURCE_INVENTORY below. File
fixtures contain at most 128 entries and 2 MiB of logical/allocated data; an in-memory
audit boundary probe reaches exactly 12 MiB. Over-cap file probes alter stat
metadata, never allocate an oversized audit file. No existing test is imported.
"""
import argparse
import copy
from contextlib import contextmanager, ExitStack
import hashlib
import importlib
import json
import os
from pathlib import Path
import shutil
import stat
import subprocess
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest import mock


ADAPTER = None
REPO = None
CHECK = None
SUPPORT = None
CONTRACT = None
SOURCE_BYTES = None
EXTRACTION = None
NOW = 10.0
DEADLINE = 20.0
CHECKOUT = "1" * 40
FILES = ("audit-stdout.log", "audit-stderr.log", "result.json", "object-hashes.json",
         "extracted/raw.lean", "extracted/BoundedReaderExtracted.lean", "extracted/extraction.json")
MODULES = ("BoundedReaderModel", "BoundedReaderExtracted", "BoundedReaderRefinement")
PHASES = ("controls", "extract", "reader", "extracted", "refinement", "audit")
SUBPROCESS_ENTRYPOINTS = ("Popen", "run", "call", "check_call", "check_output")
GO_MUTATIONS = ("empty", "stderr", "truncated", "no-pass", "extra-pass", "skip",
                "child", "missing-root", "duplicate-root", "reordered", "parallel",
                "wrong-duration", "extra-output", "non-ascii", "over-cap")
RECEIPT_MUTATIONS = ("status", "historical-tree", "missing-declaration", "duplicate-declaration",
                     "negative-raw-span", "profiled-span-shift", "span-hash",
                     "source-line-zero", "source-line-too-large", "source-span-bytes",
                     "source-span-hash", "missing-source-span")
OBJECT_MUTATIONS = ("missing", "extra", "wrong-type", "extra-key", "bytes-bool", "bytes-zero",
                    "bytes-over-cap", "hash-uppercase", "snapshot-short", "snapshot-bool",
                    "snapshot-negative", "inode-zero", "directory", "public-mode",
                    "two-links", "size-mismatch")
PROCESS_MUTATIONS = ("phase", "returncode", "returncode-bool", "eof", "overflow",
                     "joined", "descendant-claim", "argv-empty", "argv-many", "argv-nul",
                     "argv-long", "argv-type")
MAIN_FAULTS = ("controls", "extract", "reader", "extracted", "refinement", "audit",
               "manifest-construction", "manifest-write", "result-write",
               "final-membership", "final-physical", "final-deadline")

# Literal method inventory; nested subcases use only the fixed tuples or locked
# inventories named here. This is documentation/data, never a test-code parser.
SOURCE_INVENTORY = {
    "test_locked_contract_and_byte_drift": ("valid", "changed-byte"),
    "test_exact_62_plus_1_verbose_roots": ("controls-62", "emit-1"),
    "test_verbose_output_refusals": GO_MUTATIONS,
    "test_verbose_selector_refusals": ("duplicate", "child", "non-test"),
    "test_exact_extraction_and_historical_tree": ("exact",),
    "test_extraction_byte_drift": ("three-files-times-byte-and-length",),
    "test_extraction_inventory_and_type": ("missing", "extra", "renamed", "bytearray"),
    "test_committed_reference_drift": ("raw", "profiled"),
    "test_current_source_pins": ("four-locked-source-pins",),
    "test_current_fixture_pins": ("two-locked-fixture-pins",),
    "test_receipt_inner_guards": RECEIPT_MUTATIONS,
    "test_only_two_header_budget_edits": ("additional-option",),
    "test_extraction_deadline_stages": ("initial", "leaf", "source", "fixture", "span", "complete"),
    "test_fresh_extraction_membership_and_deadline": ("valid", "extra", "missing", "expired"),
    "test_phase_deadline_clipping_and_expiry": ("phase", "whole", "reserve-five", "past"),
    "test_six_phases_three_objects_and_tree_distinction": ("valid",),
    "test_result_scope_and_inventory": ("accepted", "generated", "oak", "contract", "checkout",
                                        "controls", "emit", "audit", "extraction"),
    "test_typed_go_counts_and_historical_binding": ("six-bool-counts", "historical-tree"),
    "test_typed_audit_counts_and_scope": ("five-counts-times-bool-and-drift", "six-bool-scopes",
                                         "four-graph-counters-times-four-invalid-values", "axioms"),
    "test_three_typed_object_receipts": OBJECT_MUTATIONS,
    "test_six_phase_inventory": ("missing", "extra", "reordered", "duplicate", "tuple"),
    "test_each_direct_process_receipt": PROCESS_MUTATIONS,
    "test_exact_argv_for_every_phase": ("all-six-phases-times-each-argument",),
    "test_seven_file_manifest_and_preflight": ("valid",),
    "test_retained_evidence_allowlist": ("missing", "extra", "renamed", "bytearray"),
    "test_preflight_work_and_extracted_membership": ("extra-root", "extra-extracted", "missing-phase"),
    "test_retained_hash_and_coherence_drift": ("seven-files", "manifest-object", "manifest-source",
                                             "manifest-historical", "manifest-checkout"),
    "test_each_required_file_missing_or_alias": ("seven-files-times-missing-symlink-hardlink",),
    "test_exact_read_caps_and_oversized_stat": ("fixed-seven-caps", "seven-oversized-stats"),
    "test_metadata_and_audit_boundaries": ("metadata-exact", "metadata-over", "audit-exact",
                                          "audit-empty", "stderr-nonempty", "extraction-over"),
    "test_noncanonical_metadata": ("result-and-manifest-times-compact-no-newline-extra-newline",),
    "test_retention_deadline": ("seven-read-boundaries", "after-manifest"),
    "test_exclusive_private_metadata_paths": ("result-and-manifest-times-existing-and-symlink",),
    "test_main_success_with_mocked_processes": ("ordinary", "late-phases"),
    "test_main_failure_and_late_finalization": MAIN_FAULTS,
    "test_main_refuses_preexisting_work": ("existing-work",),
}
SOURCE_CASE_COUNTS = {
    "test_locked_contract_and_byte_drift": 2,
    "test_exact_62_plus_1_verbose_roots": 2,
    "test_verbose_output_refusals": 15,
    "test_verbose_selector_refusals": 3,
    "test_exact_extraction_and_historical_tree": 1,
    "test_extraction_byte_drift": 6,
    "test_extraction_inventory_and_type": 4,
    "test_committed_reference_drift": 2,
    "test_current_source_pins": 4,
    "test_current_fixture_pins": 2,
    "test_receipt_inner_guards": 12,
    "test_only_two_header_budget_edits": 1,
    "test_extraction_deadline_stages": 6,
    "test_fresh_extraction_membership_and_deadline": 4,
    "test_phase_deadline_clipping_and_expiry": 4,
    "test_six_phases_three_objects_and_tree_distinction": 1,
    "test_result_scope_and_inventory": 9,
    "test_typed_go_counts_and_historical_binding": 7,
    "test_typed_audit_counts_and_scope": 33,
    "test_three_typed_object_receipts": 48,
    "test_six_phase_inventory": 5,
    "test_each_direct_process_receipt": 72,
    "test_exact_argv_for_every_phase": 67,
    "test_seven_file_manifest_and_preflight": 1,
    "test_retained_evidence_allowlist": 4,
    "test_preflight_work_and_extracted_membership": 3,
    "test_retained_hash_and_coherence_drift": 11,
    "test_each_required_file_missing_or_alias": 21,
    "test_exact_read_caps_and_oversized_stat": 8,
    "test_metadata_and_audit_boundaries": 6,
    "test_noncanonical_metadata": 6,
    "test_retention_deadline": 8,
    "test_exclusive_private_metadata_paths": 4,
    "test_main_success_with_mocked_processes": 2,
    "test_main_failure_and_late_finalization": 12,
    "test_main_refuses_preexisting_work": 1,
}


def identity(data):
    return {"bytes": len(data), "sha256": hashlib.sha256(data).hexdigest()}


def verbose(names):
    return ("".join("=== RUN   " + name + "\n--- PASS: " + name + " (0.00s)\n"
                    for name in names) + "PASS\n").encode("ascii")


def record(phase, argv):
    return {"phase": phase, "argv": argv, "returncode": 0,
            "pipe_eof": ["stderr", "stdout"], "overflow": False,
            "direct_child_joined": True, "arbitrary_descendant_emptiness_established": False,
            "wall_seconds": 0.0, "peak_direct_rss": 0}


class RefinementControls(unittest.TestCase):
    def setUp(self):
        self.C = CHECK
        self.H = CHECK.host
        self.contract = copy.deepcopy(CONTRACT)
        self.extraction = dict(EXTRACTION)
        temporary = tempfile.TemporaryDirectory(prefix="reader-refinement-controls-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.addCleanup(self.check_scratch)
        self.repo = self.root / "source"
        for relative, data in SOURCE_BYTES.items():
            path = self.repo / relative
            path.parent.mkdir(parents=True, exist_ok=True, mode=0o700)
            self.H.write_new(path, data)
        self.work = self.root / "work"
        self.work.mkdir(mode=0o700)
        self.clock = mock.patch.object(self.C.time, "monotonic", return_value=NOW)
        self.clock.start()
        self.addCleanup(self.clock.stop)
        refusal = mock.patch.object(self.H, "run_lean", side_effect=AssertionError("unmocked process runner"))
        refusal.start()
        self.addCleanup(refusal.stop)
        self.lean = self.root / "tool/bin/lean"
        self.extractor = self.root / "extractor.test"
        self.driver = self.repo / "spec/lean/reader_apdu/RefinementAuditDriver.lean"
        # Fixed summary fixture only; complete audit parsing has separate controls.
        self.summary = {"accepted": True, "named_theorems": 117, "named_controls": 18,
                        "candidate_declarations": 753, "actual_imports": 1050,
                        "source_examples": 0, "anonymous_examples_persisted": False,
                        "generated_definition_refinement_established": True,
                        "oak_implementation_refinement_established": False,
                        "implementation_refinement_established": False,
                        "imported_distribution_normal_trust": True,
                        "allowed_axioms": sorted(self.contract["allowed_axioms"]),
                        "dependency_nodes": 756, "dependency_edges": 123,
                        "independent_processed_nodes": 1458, "independent_edge_occurrences": 942}
        objects = {}
        object_dir = self.work / "objects/Oak/Stdlib"
        object_dir.mkdir(parents=True, mode=0o700)
        for module in MODULES:
            path = object_dir / (module + ".olean")
            self.H.write_new(path, ("synthetic object receipt " + module).encode())
            objects[path.name] = self.H.object_identity(path)
        self.result = {"accepted": True, "generated_definition_refinement": True,
                       "oak_implementation_refinement": False, "checkout_commit": CHECKOUT,
                       "source_contract_sha256": self.C.CONTRACT_SHA256,
                       "historical_extraction_tree": self.contract["historical_extraction_tree"],
                       "controls": {"roots": 62, "children": 0, "skips": 0},
                       "emit": {"roots": 1, "children": 0, "skips": 0},
                       "extraction": copy.deepcopy(self.contract["extraction"]["files"]),
                       "audit": self.summary, "objects": objects,
                       "direct_processes": self.records(self.work)}
        self.leaves = {"audit-stdout.log": b"synthetic audit fixture; no proof claim\n",
                       "audit-stderr.log": b"",
                       **{"extracted/" + name: data for name, data in self.extraction.items()}}

    def check_scratch(self):
        entries, logical, allocated = 0, 0, 0
        for directory, dirs, files in os.walk(self.root, followlinks=False):
            entries += 1 + len(files)
            allocated += Path(directory).lstat().st_blocks * 512
            for name in files:
                info = (Path(directory) / name).lstat()
                logical += info.st_size
                allocated += info.st_blocks * 512
        self.assertLessEqual(entries, 128, "finite scratch entry bound")
        self.assertLessEqual(logical, 2 * 1024**2, "finite scratch byte bound")
        self.assertLessEqual(allocated, 2 * 1024**2, "finite allocated scratch bound")

    def records(self, work):
        extractor, lean = str(self.extractor), str(self.lean)
        values = [record("controls", [extractor, "-test.v", "-test.count=1", "-test.timeout=10s",
                                      "-test.run=^TestBoundedReaderControl"]),
                  record("extract", [extractor, "-test.v", "-test.count=1", "-test.timeout=45s",
                                     "-test.run=^TestBoundedReaderExtractionEmit$",
                                     "-reader-source-root=" + str(self.repo),
                                     "-reader-fixture=" + str(self.repo / self.contract["fixture"]),
                                     "-reader-output=" + str(work / "extracted")])]
        values.extend(record(phase, [lean, *self.H.FLAGS, "--root=" + str(self.repo / "spec/lean"),
                                    "-o", str(work / "objects/Oak/Stdlib" / (module + ".olean")),
                                    str(self.repo / "spec/lean/Oak/Stdlib" / (module + ".lean"))])
                      for phase, module in zip(PHASES[2:5], MODULES))
        values.append(record("audit", [lean, *self.H.FLAGS,
                                       "--root=" + str(self.driver.parent), str(self.driver)]))
        return values

    def equality(self, leaves=None, contract=None):
        return self.C.extraction_equality(self.extraction if leaves is None else leaves,
                                          self.contract if contract is None else contract,
                                          DEADLINE, self.repo)

    def bundle(self):
        for name in ("home", "tmp", "extracted"):
            (self.work / name).mkdir(exist_ok=True, mode=0o700)
        for phase in PHASES:
            for suffix in ("-stdout.log", "-stderr.log", "-execution.json"):
                path = self.work / (phase + suffix)
                if not path.exists():
                    self.H.write_new(path, b"")
        leaves = {**self.leaves, "result.json": self.H.retained_json(self.result),
                  "object-hashes.json": self.C.retention_manifest(self.result, self.leaves, self.contract)}
        for name, data in leaves.items():
            path = self.work / name
            if path.exists() or path.is_symlink():
                path.unlink()
            self.H.write_new(path, data)
        self.check_scratch()
        return leaves

    def verify(self):
        with mock.patch.object(self.C, "load_contract", return_value=self.contract):
            return self.C.verify_retention(self.work, DEADLINE)

    def test_locked_contract_and_byte_drift(self):
        self.assertEqual(self.C.load_contract(ADAPTER), CONTRACT)
        raw = SUPPORT.read_regular(ADAPTER / "refinement_contract.json", 1024**2)
        self.H.write_new(self.root / "refinement_contract.json", raw + b" ")
        with self.assertRaisesRegex(RuntimeError, "locked refinement contract"):
            self.C.load_contract(self.root)

    def test_exact_62_plus_1_verbose_roots(self):
        self.assertEqual(len(self.contract["control_roots"]), 62)
        for names in (self.contract["control_roots"], ["TestBoundedReaderExtractionEmit"]):
            with self.subTest(roots=len(names)):
                self.assertEqual(self.C.test_output(verbose(names), b"", names),
                                 {"roots": len(names), "children": 0, "skips": 0})

    def test_verbose_output_refusals(self):
        names = self.contract["control_roots"]
        valid = verbose(names)
        for mutation in GO_MUTATIONS:
            with self.subTest(mutation=mutation):
                lines, stderr = valid.decode().splitlines(), b""
                if mutation == "empty": lines = []
                elif mutation == "stderr": stderr = b"warning\n"
                elif mutation == "no-pass": lines.pop()
                elif mutation == "extra-pass": lines.append("PASS")
                elif mutation == "skip": lines[1] = lines[1].replace("PASS", "SKIP")
                elif mutation == "child": lines[0] += "/child"
                elif mutation == "missing-root": del lines[2:4]
                elif mutation == "duplicate-root": lines[2:4] = lines[0:2]
                elif mutation == "reordered": lines[:4] = lines[2:4] + lines[:2]
                elif mutation == "parallel": lines[1] = "=== PAUSE " + names[0]
                elif mutation == "wrong-duration": lines[1] = lines[1].replace("0.00s", "NaNs")
                elif mutation == "extra-output": lines.insert(0, "noise")
                raw = ("\n".join(lines) + ("\n" if lines else "")).encode()
                if mutation == "truncated": raw = raw[:-1]
                elif mutation == "non-ascii": raw = b"\xff" + raw[1:]
                elif mutation == "over-cap": raw = b"x" * (256 * 1024) + b"\n"
                with self.assertRaises((RuntimeError, UnicodeDecodeError)):
                    self.C.test_output(raw, stderr, names)

    def test_verbose_selector_refusals(self):
        for label, names in (("duplicate", ["TestSame", "TestSame"]),
                             ("child", ["TestParent/child"]), ("non-test", ["BenchmarkOther"])):
            with self.subTest(case=label), self.assertRaises(RuntimeError):
                self.C.test_output(verbose(names), b"", names)

    def test_exact_extraction_and_historical_tree(self):
        self.assertEqual(self.equality(), self.contract["extraction"]["files"])
        receipt = SUPPORT.decode(self.extraction["extraction.json"])
        self.assertEqual(receipt, self.contract["extraction"]["receipt"])
        self.assertEqual(receipt["status"], "extracted_not_proved")
        self.assertNotEqual(CHECKOUT, receipt["tree_requires_outer_authentication"])

    def test_extraction_byte_drift(self):
        for name in sorted(self.extraction):
            for change in ("byte", "length"):
                with self.subTest(name=name, change=change):
                    leaves = dict(self.extraction)
                    leaves[name] = (bytes([leaves[name][0] ^ 1]) + leaves[name][1:]
                                    if change == "byte" else leaves[name][:-1])
                    with self.assertRaisesRegex(RuntimeError, "locked extraction bytes"):
                        self.equality(leaves)

    def test_extraction_inventory_and_type(self):
        for mutation in ("missing", "extra", "renamed", "bytearray"):
            with self.subTest(mutation=mutation):
                leaves = dict(self.extraction)
                if mutation == "missing": del leaves["raw.lean"]
                elif mutation == "extra": leaves["other"] = b""
                elif mutation == "renamed": leaves["other"] = leaves.pop("raw.lean")
                else: leaves["raw.lean"] = bytearray(leaves["raw.lean"])
                with self.assertRaises(RuntimeError): self.equality(leaves)

    def test_committed_reference_drift(self):
        for field in ("raw_reference", "profiled_reference"):
            with self.subTest(reference=field):
                path = self.repo / self.contract["extraction"][field]
                raw = path.read_bytes()
                try:
                    path.write_bytes(bytes([raw[0] ^ 1]) + raw[1:])
                    with self.assertRaisesRegex(RuntimeError, "actual output equals committed references"):
                        self.equality()
                finally: path.write_bytes(raw)

    def test_current_source_pins(self):
        for pin in self.contract["extraction"]["receipt"]["source_pins"]:
            with self.subTest(source=pin["Path"]):
                path = self.repo / pin["Path"]
                raw = path.read_bytes()
                try:
                    path.write_bytes(bytes([raw[0] ^ 1]) + raw[1:])
                    with self.assertRaisesRegex(RuntimeError, "current original source binding"):
                        self.equality()
                finally: path.write_bytes(raw)

    def test_current_fixture_pins(self):
        for pin in self.contract["extraction"]["receipt"]["fixture_pins"]:
            with self.subTest(fixture=pin["Path"]):
                path = self.repo / self.contract["fixture"] / pin["Path"]
                raw = path.read_bytes()
                try:
                    path.write_bytes(bytes([raw[0] ^ 1]) + raw[1:])
                    with self.assertRaisesRegex(RuntimeError, "current qualified fixture binding"):
                        self.equality()
                finally: path.write_bytes(raw)

    def test_receipt_inner_guards(self):
        # Counterfactual contracts expose independent checks after byte equality.
        # The production load_contract lock is never weakened or patched here.
        for mutation in RECEIPT_MUTATIONS:
            with self.subTest(mutation=mutation):
                contract, leaves = copy.deepcopy(self.contract), dict(self.extraction)
                receipt = contract["extraction"]["receipt"]
                declaration = next(d for d in receipt["declarations"] if "source_span" in d)
                if mutation == "status": receipt["status"] = "proved"
                elif mutation == "historical-tree": receipt["tree_requires_outer_authentication"] = CHECKOUT
                elif mutation == "missing-declaration": receipt["declarations"].pop()
                elif mutation == "duplicate-declaration": receipt["declarations"][1] = receipt["declarations"][0]
                elif mutation == "negative-raw-span": declaration["raw_start_byte"] = -1
                elif mutation == "profiled-span-shift": declaration["profiled_start_byte"] += 1
                elif mutation == "span-hash": declaration["raw_span_sha256"] = "0" * 64
                elif mutation == "source-line-zero": declaration["source_span"]["FirstLine"] = 0
                elif mutation == "source-line-too-large": declaration["source_span"]["LastLine"] = 1000000
                elif mutation == "source-span-bytes": declaration["source_span"]["Bytes"] += 1
                elif mutation == "source-span-hash": declaration["source_span"]["SHA256"] = "0" * 64
                else: del declaration["source_span"]
                leaves["extraction.json"] = (json.dumps(receipt, sort_keys=True) + "\n").encode()
                contract["extraction"]["files"]["extraction.json"] = identity(leaves["extraction.json"])
                contract["extraction"]["receipt_utf8"] = leaves["extraction.json"].decode()
                with self.assertRaises(RuntimeError): self.equality(leaves, contract)

    def test_only_two_header_budget_edits(self):
        contract, leaves = copy.deepcopy(self.contract), dict(self.extraction)
        leaves["BoundedReaderExtracted.lean"] += b"set_option pp.universes true\n"
        contract["extraction"]["files"]["BoundedReaderExtracted.lean"] = identity(leaves["BoundedReaderExtracted.lean"])
        path = self.repo / contract["extraction"]["profiled_reference"]
        path.write_bytes(leaves["BoundedReaderExtracted.lean"])
        with self.assertRaisesRegex(RuntimeError, "only two accepted header budget edits"):
            self.equality(leaves, contract)

    def test_extraction_deadline_stages(self):
        for label, index in (("initial", 0), ("leaf", 1), ("source", 4),
                             ("fixture", 8), ("span", 10), ("complete", 26)):
            with self.subTest(stage=label), mock.patch.object(self.C.time, "monotonic",
                    side_effect=[NOW] * index + [DEADLINE]):
                with self.assertRaisesRegex(RuntimeError, "deadline"):
                    self.equality()

    def test_fresh_extraction_membership_and_deadline(self):
        self.bundle()
        self.assertEqual(self.C.load_extraction(self.work, self.contract, DEADLINE, self.repo),
                         (self.extraction, self.contract["extraction"]["files"]))
        extra = self.work / "extracted/extra"
        self.H.write_new(extra, b"")
        with self.assertRaises(RuntimeError): self.C.load_extraction(self.work, self.contract, DEADLINE, self.repo)
        extra.unlink()
        (self.work / "extracted/raw.lean").unlink()
        with self.assertRaises(RuntimeError): self.C.load_extraction(self.work, self.contract, DEADLINE, self.repo)
        with mock.patch.object(self.C.time, "monotonic", return_value=DEADLINE):
            with self.assertRaisesRegex(RuntimeError, "extraction read deadline"):
                self.C.load_extraction(self.work, self.contract, DEADLINE, self.repo)

    def test_phase_deadline_clipping_and_expiry(self):
        self.assertEqual(self.H.phase_deadline(610.0, 120, 10.0), 130.0)
        self.assertEqual(self.H.phase_deadline(610.0, 120, 550.0), 580.0)
        for now in (575.0, 610.0):
            with self.subTest(now=now), self.assertRaisesRegex(RuntimeError, "phase has no cleanup reserve"):
                self.H.phase_deadline(610.0, 120, now)

    def test_six_phases_three_objects_and_tree_distinction(self):
        self.assertEqual(self.C.validate_retained_result(self.result, self.contract), str(self.driver))
        manifest = SUPPORT.decode(self.C.retention_manifest(self.result, self.leaves, self.contract))
        self.assertEqual(manifest["checkout_commit"], CHECKOUT)
        self.assertEqual(manifest["historical_extraction_tree"], self.contract["historical_extraction_tree"])
        self.assertNotEqual(manifest["checkout_commit"], manifest["historical_extraction_tree"])
        self.assertEqual(set(manifest["objects"]), {module + ".olean" for module in MODULES})

    def test_result_scope_and_inventory(self):
        mutations = (("accepted", 1), ("generated_definition_refinement", 1),
                     ("oak_implementation_refinement", 0), ("source_contract_sha256", "0" * 64),
                     ("checkout_commit", "x" * 40), ("controls", {"roots": 61}),
                     ("emit", {"roots": 0}), ("audit", {"accepted": False}), ("extraction", {}))
        for field, value in mutations:
            with self.subTest(field=field):
                result = copy.deepcopy(self.result)
                result[field] = value
                with self.assertRaises(RuntimeError): self.C.validate_retained_result(result, self.contract)

    def test_three_typed_object_receipts(self):
        for name in sorted(self.result["objects"]):
            for mutation in OBJECT_MUTATIONS:
                with self.subTest(object=name, mutation=mutation):
                    result = copy.deepcopy(self.result)
                    objects, obj = result["objects"], result["objects"][name]
                    if mutation == "missing": del objects[name]
                    elif mutation == "extra": objects["Extra.olean"] = copy.deepcopy(obj)
                    elif mutation == "wrong-type": objects[name] = []
                    elif mutation == "extra-key": obj["extra"] = 0
                    elif mutation == "bytes-bool": obj["bytes"] = True
                    elif mutation == "bytes-zero": obj["bytes"] = 0
                    elif mutation == "bytes-over-cap": obj["bytes"] = 8 * 1024**2 + 1
                    elif mutation == "hash-uppercase": obj["sha256"] = "A" * 64
                    elif mutation == "snapshot-short": obj["snapshot"].pop()
                    elif mutation == "snapshot-bool": obj["snapshot"][0] = True
                    elif mutation == "snapshot-negative": obj["snapshot"][0] = -1
                    elif mutation == "inode-zero": obj["snapshot"][1] = 0
                    elif mutation == "directory": obj["snapshot"][2] = stat.S_IFDIR | 0o700
                    elif mutation == "public-mode": obj["snapshot"][2] = stat.S_IFREG | 0o640
                    elif mutation == "two-links": obj["snapshot"][4] = 2
                    else: obj["snapshot"][5] += 1
                    with self.assertRaises(RuntimeError): self.C.validate_retained_result(result, self.contract)

    def test_typed_go_counts_and_historical_binding(self):
        for section in ("controls", "emit"):
            for field in ("roots", "children", "skips"):
                with self.subTest(section=section, field=field):
                    result = copy.deepcopy(self.result)
                    result[section][field] = bool(result[section][field])
                    with self.assertRaises(RuntimeError): self.C.validate_retained_result(result, self.contract)
        result = copy.deepcopy(self.result)
        result["historical_extraction_tree"] = CHECKOUT
        with self.assertRaisesRegex(RuntimeError, "retained extraction identities"):
            self.C.validate_retained_result(result, self.contract)

    def test_typed_audit_counts_and_scope(self):
        for field in ("named_theorems", "named_controls", "candidate_declarations", "actual_imports", "source_examples"):
            for value in (False, self.summary[field] + 1):
                with self.subTest(field=field, value=value):
                    result = copy.deepcopy(self.result)
                    result["audit"][field] = value
                    with self.assertRaises(RuntimeError): self.C.validate_retained_result(result, self.contract)
        for field in ("accepted", "anonymous_examples_persisted", "generated_definition_refinement_established",
                      "oak_implementation_refinement_established", "implementation_refinement_established",
                      "imported_distribution_normal_trust"):
            with self.subTest(scope=field):
                result = copy.deepcopy(self.result)
                result["audit"][field] = int(result["audit"][field])
                with self.assertRaises(RuntimeError): self.C.validate_retained_result(result, self.contract)
        for field, low, high in (("dependency_nodes", 1, 10000), ("dependency_edges", 0, 100000),
                                 ("independent_processed_nodes", 1, 1180000),
                                 ("independent_edge_occurrences", 0, 11800000)):
            for value in (True, 1.0, low - 1, high + 1):
                with self.subTest(counter=field, value=value):
                    result = copy.deepcopy(self.result)
                    result["audit"][field] = value
                    with self.assertRaises(RuntimeError): self.C.validate_retained_result(result, self.contract)
        result = copy.deepcopy(self.result)
        result["audit"]["allowed_axioms"] = ["sorryAx"]
        with self.assertRaises(RuntimeError): self.C.validate_retained_result(result, self.contract)

    def test_six_phase_inventory(self):
        for mutation in ("missing", "extra", "reordered", "duplicate", "tuple"):
            with self.subTest(mutation=mutation):
                result = copy.deepcopy(self.result)
                records = result["direct_processes"]
                if mutation == "missing": records.pop()
                elif mutation == "extra": records.append(copy.deepcopy(records[-1]))
                elif mutation == "reordered": records[:2] = records[1::-1]
                elif mutation == "duplicate": records[1] = copy.deepcopy(records[0])
                else: result["direct_processes"] = tuple(records)
                with self.assertRaises(RuntimeError): self.C.validate_retained_result(result, self.contract)

    def test_each_direct_process_receipt(self):
        changes = {"phase": "other", "returncode": 1, "returncode-bool": False,
                   "eof": ["stdout"], "overflow": True, "joined": False,
                   "descendant-claim": True, "argv-empty": [], "argv-many": ["x"] * 33,
                   "argv-nul": ["x\x00"], "argv-long": ["x" * 4097], "argv-type": [False]}
        keys = {"returncode-bool": "returncode", "eof": "pipe_eof", "joined": "direct_child_joined",
                "descendant-claim": "arbitrary_descendant_emptiness_established"}
        for index, phase in enumerate(PHASES):
            for mutation in PROCESS_MUTATIONS:
                with self.subTest(phase=phase, mutation=mutation):
                    result = copy.deepcopy(self.result)
                    key = "argv" if mutation.startswith("argv-") else keys.get(mutation, mutation)
                    result["direct_processes"][index][key] = changes[mutation]
                    with self.assertRaises(RuntimeError): self.C.validate_retained_result(result, self.contract)

    def test_exact_argv_for_every_phase(self):
        for index, original in enumerate(self.result["direct_processes"]):
            for argument in range(len(original["argv"])):
                with self.subTest(phase=PHASES[index], argument=argument):
                    result = copy.deepcopy(self.result)
                    result["direct_processes"][index]["argv"][argument] += "-changed"
                    with self.assertRaises(RuntimeError): self.C.validate_retained_result(result, self.contract)

    def test_seven_file_manifest_and_preflight(self):
        leaves = self.bundle()
        manifest = SUPPORT.decode(leaves["object-hashes.json"])
        self.assertEqual(set(self.C.ARTIFACT_CAPS), set(FILES))
        self.assertEqual(set(manifest["files"]), set(FILES) - {"object-hashes.json"})
        self.assertEqual(manifest["source_inputs"], self.contract["inputs"])
        for name, observed in manifest["files"].items():
            self.assertEqual(observed, identity(leaves[name]))
        self.assertIsNone(self.verify())

    def test_retained_evidence_allowlist(self):
        for mutation in ("missing", "extra", "renamed", "bytearray"):
            with self.subTest(mutation=mutation):
                leaves = dict(self.leaves)
                if mutation == "missing": del leaves["audit-stdout.log"]
                elif mutation == "extra": leaves["other"] = b""
                elif mutation == "renamed": leaves["other"] = leaves.pop("audit-stdout.log")
                else: leaves["audit-stdout.log"] = bytearray(leaves["audit-stdout.log"])
                with self.assertRaises(RuntimeError): self.C.retention_manifest(self.result, leaves, self.contract)

    def test_preflight_work_and_extracted_membership(self):
        for mutation in ("extra-root", "extra-extracted", "missing-phase"):
            with self.subTest(mutation=mutation):
                self.bundle()
                path = self.work / ("unexpected" if mutation == "extra-root" else
                                    "extracted/unexpected" if mutation == "extra-extracted" else
                                    "controls-execution.json")
                if mutation == "missing-phase": path.unlink()
                else: self.H.write_new(path, b"")
                with self.assertRaises(RuntimeError): self.verify()
                if path.exists(): path.unlink()

    def test_retained_hash_and_coherence_drift(self):
        for name in FILES:
            with self.subTest(file=name):
                leaves = self.bundle()
                raw = leaves[name]
                (self.work / name).write_bytes((bytes([raw[0] ^ 1]) + raw[1:]) if raw else b"x")
                with self.assertRaises((RuntimeError, ValueError)): self.verify()
        for section in ("objects", "source_inputs", "historical_extraction_tree", "checkout_commit"):
            with self.subTest(manifest=section):
                leaves = self.bundle()
                manifest = SUPPORT.decode(leaves["object-hashes.json"])
                if section in ("objects", "source_inputs"):
                    manifest[section][sorted(manifest[section])[0]]["sha256"] = "0" * 64
                else: manifest[section] = "0" * 40
                (self.work / "object-hashes.json").write_bytes(self.H.retained_json(manifest))
                with self.assertRaisesRegex(RuntimeError, "exact retained manifest and result"): self.verify()

    def test_each_required_file_missing_or_alias(self):
        for name in FILES:
            for mutation in ("missing", "symlink", "hardlink"):
                with self.subTest(file=name, mutation=mutation):
                    self.bundle()
                    path, target = self.work / name, self.root / "alias-target"
                    if mutation == "missing": path.unlink()
                    elif mutation == "symlink":
                        path.rename(target)
                        path.symlink_to(target)
                    else: os.link(path, target)
                    try:
                        with self.assertRaises((RuntimeError, FileNotFoundError)): self.verify()
                    finally:
                        if path.is_symlink(): path.unlink()
                        if target.exists(): target.unlink()

    def test_exact_read_caps_and_oversized_stat(self):
        self.bundle()
        caps = {"audit-stdout.log": 12 * 1024**2, "audit-stderr.log": 0,
                "result.json": 32768, "object-hashes.json": 32768,
                "extracted/raw.lean": 65536, "extracted/BoundedReaderExtracted.lean": 65536,
                "extracted/extraction.json": 65536}
        self.assertEqual(self.C.ARTIFACT_CAPS, caps)
        with mock.patch.object(self.C, "read_regular", wraps=SUPPORT.read_regular) as reader:
            self.verify()
        self.assertEqual(reader.call_args_list,
                         [mock.call(self.work / name, cap) for name, cap in caps.items()])
        original = os.fstat
        for name, cap in caps.items():
            with self.subTest(file=name):
                inode = (self.work / name).stat().st_ino
                def oversized(fd):
                    info = original(fd)
                    if info.st_ino != inode: return info
                    values = {key: getattr(info, key) for key in
                              ("st_dev", "st_ino", "st_mode", "st_uid", "st_nlink",
                               "st_size", "st_mtime_ns", "st_ctime_ns")}
                    values["st_size"] = cap + 1
                    return SimpleNamespace(**values)
                with mock.patch.object(SUPPORT.os, "fstat", side_effect=oversized):
                    with self.assertRaisesRegex(RuntimeError, "regular bounded input"): self.verify()

    def test_metadata_and_audit_boundaries(self):
        for size in (32768, 32769):
            with self.subTest(metadata_bytes=size):
                value = {"padding": ""}
                value["padding"] = "x" * (size - len(self.H.retained_json(value)))
                if size == 32768: self.assertEqual(len(self.H.retained_json(value)), size)
                else:
                    with self.assertRaisesRegex(RuntimeError, "bounded retained metadata"): self.H.retained_json(value)
        leaves = dict(self.leaves)
        leaves["audit-stdout.log"] = b"x" * (12 * 1024**2)
        manifest = SUPPORT.decode(self.C.retention_manifest(self.result, leaves, self.contract))
        self.assertEqual(manifest["files"]["audit-stdout.log"]["bytes"], 12 * 1024**2)
        del leaves
        for name, data in (("audit-stdout.log", b""), ("audit-stderr.log", b"x"),
                           ("extracted/raw.lean", b"x" * 65537)):
            with self.subTest(leaf=name):
                leaves = dict(self.leaves)
                leaves[name] = data
                with self.assertRaises(RuntimeError): self.C.retention_manifest(self.result, leaves, self.contract)

    def test_noncanonical_metadata(self):
        for name in ("result.json", "object-hashes.json"):
            for mutation in ("compact", "no-newline", "extra-newline"):
                with self.subTest(file=name, mutation=mutation):
                    leaves = self.bundle()
                    raw = leaves[name]
                    raw = (json.dumps(SUPPORT.decode(raw), separators=(",", ":")).encode()
                           if mutation == "compact" else raw[:-1] if mutation == "no-newline" else raw + b"\n")
                    (self.work / name).write_bytes(raw)
                    with self.assertRaises(RuntimeError): self.verify()

    def test_retention_deadline(self):
        self.bundle()
        # Permit extra deadline checks added around membership; expire when each
        # actual named read is next, and once immediately after reconstruction.
        real_read, real_manifest = self.C.read_regular, self.C.retention_manifest
        for expired in range(7):
            state = {"reads": 0}
            def now(): return DEADLINE if state["reads"] >= expired else NOW
            def read(*args, **kwargs):
                value = real_read(*args, **kwargs)
                state["reads"] += 1
                return value
            with self.subTest(before_file=FILES[expired]), \
                 mock.patch.object(self.C.time, "monotonic", side_effect=now), \
                 mock.patch.object(self.C, "read_regular", side_effect=read):
                with self.assertRaisesRegex(RuntimeError, "deadline"): self.verify()
                self.assertEqual(state["reads"], expired)
        state = {"done": False}
        def manifest(*args):
            value = real_manifest(*args)
            state["done"] = True
            return value
        with mock.patch.object(self.C.time, "monotonic", side_effect=lambda: DEADLINE if state["done"] else NOW), \
             mock.patch.object(self.C, "retention_manifest", side_effect=manifest):
            with self.assertRaisesRegex(RuntimeError, "deadline"): self.verify()

    def test_exclusive_private_metadata_paths(self):
        for name in ("result.json", "object-hashes.json"):
            with self.subTest(file=name):
                path = self.work / name
                self.H.write_new(path, b"original\n")
                self.assertEqual(path.stat().st_mode & 0o777, 0o600)
                with self.assertRaises(FileExistsError): self.H.write_new(path, b"replacement\n")
                self.assertEqual(path.read_bytes(), b"original\n")
                path.unlink()
                path.symlink_to(self.repo / self.contract["extraction"]["raw_reference"])
                with self.assertRaisesRegex(RuntimeError, "input alias"): self.H.write_new(path, b"replacement\n")
                path.unlink()

    @contextmanager
    def simulated_main(self, fault=None, late=False):
        """Real profile helpers and tiny files, with all process/tool I/O mocked."""
        directory = self.root / "simulated"
        directory.mkdir(mode=0o700)
        harness = self.repo / ".github/scripts/reader_refinement"
        harness_files = [harness / name for name in ("adapter.go", "adapter_test.go", "emit_test.go")]
        for path in harness_files:
            # Preserve real harness membership checks; source authentication and
            # every process are explicit mocks in this context only.
            self.H.write_new(path, b"synthetic-only\n")
        work = directory / "work"
        self.lean.parent.mkdir(parents=True, exist_ok=True, mode=0o700)
        for path in (self.lean, self.extractor):
            if not path.exists(): self.H.write_new(path, b"placeholder; never executed")
            path.chmod(0o700)
        state = {"now": NOW, "phases": [], "stops": [], "physical": 0,
                 "source_stops": [], "object_stops": []}
        original_write = self.H.write_new
        original_read = self.C.read_regular
        original_verify = self.C.verify_file
        original_inspect = self.H.inspect_objects
        original_members = self.C.members
        original_manifest = self.C.retention_manifest
        original_load = self.C.load_extraction

        def run(argv, env, target_work, phase, stop, cap):
            self.assertEqual(target_work, work)
            self.assertEqual(env["GOMAXPROCS"], "1")
            state["phases"].append(phase)
            state["stops"].append(stop)
            if fault == phase: raise RuntimeError("injected phase " + phase)
            if phase == "controls": out = verbose(self.contract["control_roots"])
            elif phase == "extract":
                out = verbose(["TestBoundedReaderExtractionEmit"])
                for name, data in self.extraction.items(): original_write(work / "extracted" / name, data)
            elif phase == "audit": out = self.leaves["audit-stdout.log"]
            else:
                out = b""
                original_write(Path(argv[argv.index("-o") + 1]), ("synthetic " + phase).encode())
            receipt = record(phase, argv)
            serialized = self.H.retained_json(receipt)
            self.assertLessEqual(len(serialized), 4096, "bounded synthetic process receipt")
            self.assertLessEqual(len(out), 16384, "bounded synthetic process stdout")
            for name, data in ((phase + "-stdout.log", out), (phase + "-stderr.log", b""),
                               (phase + "-execution.json", serialized)):
                original_write(work / name, data)
            return out, b"", receipt

        def read(path, cap, **kwargs):
            if Path(path) == self.driver.parent / "distribution.json": return b'{"files":{}}'
            return original_read(path, cap, **kwargs)

        def verify(path, expected, stop):
            path = Path(path)
            if path == self.extractor: return original_verify(path, expected, stop)
            state["source_stops"].append(stop)
            return {"bytes": expected["bytes"], "sha256": expected["sha256"]}

        def inspect(path, expected, stop):
            state["object_stops"].append(stop)
            value = original_inspect(path, expected, stop)
            # Advance between authenticated phases, never past a running phase's
            # own deadline. This exposes clipping without impossible receipts.
            if late and len(state["object_stops"]) in (2, 4, 6):
                state["now"] = {2: 500.0, 4: 550.0, 6: 570.0}[len(state["object_stops"])]
            return value

        def diagnostics(out, err, phase, *args):
            if late and phase == "audit": state["now"] = 579.0
            return self.summary if phase == "audit" else None

        def write(path, data):
            if fault == "manifest-write" and Path(path).name == "object-hashes.json":
                raise RuntimeError("injected manifest write")
            if fault == "result-write" and Path(path).name == "result.json":
                raise RuntimeError("injected result write")
            return original_write(path, data)

        def manifest(*args):
            if fault == "manifest-construction": raise RuntimeError("injected manifest construction")
            return original_manifest(*args)

        def members(path, cap):
            found = original_members(path, cap)
            if fault == "final-membership" and Path(path) == work and "result.json" in found:
                return found | {"unexpected"}
            return found

        def guards(path, pid=None):
            state["physical"] += 1
            if state["physical"] == 3:
                if fault == "final-physical": raise RuntimeError("injected final physical guard")
                if fault == "final-deadline": state["now"] = 609.0 if late else 40.0

        def load(work_path, contract, stop):
            # Pass the isolated source root explicitly: the production function's
            # default repo is intentionally bound at import time.
            return original_load(work_path, contract, stop, self.repo)

        try:
            with ExitStack() as stack:
                for target, name, value in ((self.C, "REPO", self.repo), (self.C, "HERE", self.driver.parent),
                                           (self.C.sys, "platform", "linux"),
                                           (self.C.sys, "argv", ["check_refinement.py", "--lean", str(self.lean),
                                            "--extractor", str(self.extractor), "--checkout-commit", CHECKOUT,
                                            "--work", str(work)])):
                    stack.enter_context(mock.patch.object(target, name, value))
                stack.enter_context(mock.patch.object(self.C.platform, "machine", return_value="x86_64"))
                stack.enter_context(mock.patch.object(self.C.signal, "signal"))
                stack.enter_context(mock.patch.object(self.C.os, "umask"))
                stack.enter_context(mock.patch.object(self.C.os, "statvfs", return_value=
                                                       SimpleNamespace(f_bavail=2 * 1024**3, f_frsize=1)))
                stack.enter_context(mock.patch.object(self.C.time, "monotonic", side_effect=lambda: state["now"]))
                stack.enter_context(mock.patch.object(self.C, "load_contract", return_value=self.contract))
                stack.enter_context(mock.patch.object(self.H, "verify_distribution"))
                stack.enter_context(mock.patch.object(self.C, "diagnostics", side_effect=diagnostics))
                for target, name, function in ((self.H, "run_lean", run), (self.C, "read_regular", read),
                    (self.C, "verify_file", verify), (self.H, "inspect_objects", inspect),
                    (self.H, "write_new", write), (self.C, "retention_manifest", manifest),
                    (self.C, "members", members), (self.H, "physical_guards", guards),
                    (self.C, "load_extraction", load)):
                    stack.enter_context(mock.patch.object(target, name, side_effect=function))
                output = stack.enter_context(mock.patch("builtins.print"))
                yield work, state, output
        finally:
            self.check_scratch()
            for path in harness_files:
                path.unlink()
            shutil.rmtree(directory)

    def test_main_success_with_mocked_processes(self):
        for late in (False, True):
            with self.subTest(late=late), self.simulated_main(late=late) as (work, state, output):
                self.assertIsNone(self.C.main())
                self.assertEqual(state["phases"], list(PHASES))
                self.assertEqual(state["stops"], [25.0, 70.0, 130.0,
                                                 580.0 if late else 130.0,
                                                 580.0 if late else 130.0,
                                                 580.0 if late else 130.0])
                final = 609.0 if late else 40.0
                count = len(self.contract["inputs"])
                self.assertEqual(state["source_stops"], [40.0] * count +
                    [130.0, 580.0 if late else 130.0, 580.0 if late else 130.0,
                     580.0 if late else 130.0] + [final] * count)
                self.assertEqual(state["object_stops"], [130.0, 130.0,
                    580.0 if late else 130.0, 580.0 if late else 130.0,
                    580.0 if late else 130.0, 580.0 if late else 130.0,
                    580.0 if late else 130.0, final])
                result = SUPPORT.decode((work / "result.json").read_bytes())
                self.assertIs(result["accepted"], True)
                self.assertEqual(result["direct_processes"], self.records(work))
                self.assertEqual(result["controls"]["roots"], 62)
                self.assertEqual(result["emit"]["roots"], 1)
                self.C.verify_retention(work, final)
                output.assert_called_once()
                self.assertIs(json.loads(output.call_args.args[0])["accepted"], True)

    def test_main_failure_and_late_finalization(self):
        for fault in MAIN_FAULTS:
            with self.subTest(fault=fault), self.simulated_main(fault=fault) as (work, state, output):
                with self.assertRaises(RuntimeError): self.C.main()
                if fault == "result-write":
                    self.assertFalse((work / "result.json").exists())
                    output.assert_not_called()
                elif fault.startswith("final-"):
                    # Retention-v2's reviewed boundary: late failure may leave
                    # accepted-looking bytes, but raises and prints no success.
                    # Only a successful workflow step can authorize upload.
                    result = SUPPORT.decode((work / "result.json").read_bytes())
                    self.assertIs(result["accepted"], True)
                    output.assert_not_called()
                else:
                    result = SUPPORT.decode((work / "result.json").read_bytes())
                    self.assertIs(result["accepted"], False)
                    self.assertIn("error", result)
                    self.assertFalse((work / "object-hashes.json").exists())
                    output.assert_called_once()
                    self.assertIs(json.loads(output.call_args.args[0])["accepted"], False)

    def test_main_refuses_preexisting_work(self):
        with self.simulated_main() as (work, state, output):
            work.mkdir(mode=0o700)
            self.H.write_new(work / "sentinel", b"unchanged")
            with self.assertRaisesRegex(RuntimeError, "extractor and fresh work"): self.C.main()
            self.assertEqual((work / "sentinel").read_bytes(), b"unchanged")
            self.assertEqual(state["phases"], [])
            output.assert_not_called()


def main():
    global ADAPTER, REPO, CHECK, SUPPORT, CONTRACT, SOURCE_BYTES, EXTRACTION
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--adapter", type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument("--repo-root", type=Path)
    options, remaining = parser.parse_known_args()
    ADAPTER = options.adapter.resolve()
    sys.dont_write_bytecode = True
    sys.path.insert(0, str(ADAPTER))
    refusal = AssertionError("process execution is outside fixed profile controls")
    with ExitStack() as patches:
        for name in SUBPROCESS_ENTRYPOINTS:
            patches.enter_context(mock.patch.object(subprocess, name, side_effect=refusal))
        patches.enter_context(mock.patch.object(os, "system", side_effect=refusal))
        SUPPORT = importlib.import_module("support")
        CHECK = importlib.import_module("check_refinement")
        for module, name in ((SUPPORT, "support.py"), (CHECK, "check_refinement.py"),
                             (CHECK.host, "check.py"),
                             (sys.modules["refinement_audit_consumer"], "refinement_audit_consumer.py"),
                             (sys.modules["audit_consumer"], "audit_consumer.py")):
            if Path(module.__file__).resolve() != ADAPTER / name:
                raise RuntimeError("actual selected profile module required: " + name)
        CONTRACT = CHECK.load_contract(ADAPTER)
        REPO = options.repo_root.resolve() if options.repo_root else CHECK.REPO
        SOURCE_BYTES = {}
        receipt = CONTRACT["extraction"]["receipt"]
        for pin in receipt["source_pins"]:
            SOURCE_BYTES[pin["Path"]] = SUPPORT.read_regular(REPO / pin["Path"], pin["Bytes"])
            if identity(SOURCE_BYTES[pin["Path"]]) != {"bytes": pin["Bytes"], "sha256": pin["SHA256"]}:
                raise RuntimeError("locked control source fixture differs: " + pin["Path"])
        for pin in receipt["fixture_pins"]:
            relative = str(Path(CONTRACT["fixture"]) / pin["Path"])
            SOURCE_BYTES[relative] = SUPPORT.read_regular(REPO / relative, pin["Bytes"])
            if identity(SOURCE_BYTES[relative]) != {"bytes": pin["Bytes"], "sha256": pin["SHA256"]}:
                raise RuntimeError("locked qualified fixture differs: " + relative)
        EXTRACTION = {"extraction.json": CONTRACT["extraction"]["receipt_utf8"].encode("utf-8")}
        if SUPPORT.decode(EXTRACTION["extraction.json"]) != receipt:
            raise RuntimeError("exact retained producer receipt differs from parsed contract")
        for name, field in (("raw.lean", "raw_reference"), ("BoundedReaderExtracted.lean", "profiled_reference")):
            relative = CONTRACT["extraction"][field]
            SOURCE_BYTES[relative] = SUPPORT.read_regular(REPO / relative, CHECK.EXTRACTION_BYTES)
            EXTRACTION[name] = SOURCE_BYTES[relative]
        for name, data in EXTRACTION.items():
            if identity(data) != CONTRACT["extraction"]["files"][name]:
                raise RuntimeError("locked extraction fixture bytes differ: " + name)
        if sum(map(len, SOURCE_BYTES.values())) > 128 * 1024:
            raise RuntimeError("bounded control source fixture")
        methods = {name for name in RefinementControls.__dict__ if name.startswith("test_")}
        if methods != set(SOURCE_INVENTORY) or methods != set(SOURCE_CASE_COUNTS) or len(methods) != 36:
            raise RuntimeError("exact source-defined method inventory")
        if sum(SOURCE_CASE_COUNTS.values()) != 397:
            raise RuntimeError("exact source-defined scenario count")
        unittest.main(argv=[sys.argv[0], *remaining])


if __name__ == "__main__":
    main()
