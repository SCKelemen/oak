"""Finite synthetic controls for the hosted APDU adapter; no Lean invocation.

SOURCE ONLY: this file has not been imported, compiled, parsed, or executed.
Run only under separate execution authorization. By default, subprocess entry
points are patched to refuse. Fixtures are protocol data, not Lean evidence.
"""
import argparse
import copy
from contextlib import nullcontext
import hashlib
import importlib
import json
import os
from pathlib import Path
import stat
import subprocess
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest import mock


ADAPTER = None
CHECK = None
CONSUMER = None
SUPPORT = None
CONTRACT = None
DEADLINE = 20.0


def encode(value):
    return json.dumps(value, separators=(",", ":"), ensure_ascii=True).encode("utf-8")


def fixture(contract):
    """503 nodes; shared cycles and repeated edges are intentionally valid.

    Synthetic private names exercise the consumer's existing prefix rule only.
    They make no claim about Lean's emitted private-name representation.
    """
    allowed = sorted(CONSUMER.ALLOWED)
    helpers = ["APDUControl.helper" + str(i) for i in range(452)]
    theorems = []
    candidates = []
    for i, row in enumerate(contract["expected"]["theorems"]):
        actual = "_private.control" + str(i) if row["private"] else row["qualified_name"]
        common = {
            "owner": row["module"], "user_name": row["qualified_name"],
            "actual_name": actual, "axioms": list(allowed),
            "direct_dependencies": [helpers[0]],
        }
        theorems.append(dict(common, record="expected_theorem", private=row["private"]))
        candidates.append(dict(common, record="candidate_declaration", kind="theorem"))
    for i, name in enumerate(helpers):
        deps = allowed + [helpers[1], allowed[0]] if i == 0 else [helpers[0]] if i == 1 else []
        candidates.append({
            "record": "candidate_declaration", "owner": "Oak.Stdlib.APDULengthModel",
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
        "record": "complete", "expected_theorems": 48,
        "candidate_declarations": 500, "dependency_nodes": len(nodes),
        "dependency_edges": sum(len(n["direct_dependencies"]) for n in nodes),
        "anonymous_examples_persisted": False,
        "anonymous_examples_accounted_by_exact_source_compile": 15,
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
        "fileName": str(ADAPTER / "AuditDriver.lean"),
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


class ConsumerControls(unittest.TestCase):
    def setUp(self):
        self.records = fixture(CONTRACT)
        self.clock = mock.patch.object(CONSUMER.time, "monotonic", return_value=10.0)
        self.clock.start()
        self.addCleanup(self.clock.stop)

    def accept(self, records=None):
        return CONSUMER.audit_records(self.records if records is None else records, DEADLINE, CONTRACT)

    def reject(self, message, records=None):
        with self.assertRaisesRegex(RuntimeError, message):
            self.accept(records)

    def diagnostics(self, stdout, stderr=b"", phase="audit"):
        return CONSUMER.diagnostics(stdout, stderr, phase, DEADLINE,
                                    ADAPTER / "AuditDriver.lean", CONTRACT)

    def test_valid_complete_shared_cyclic_graph_and_duplicate_edges(self):
        result = self.accept()
        self.assertIs(result["accepted"], True)
        self.assertEqual((result["named_theorems"], result["source_examples"],
                          result["candidate_declarations"], result["actual_imports"]),
                         (48, 15, 500, 1049))
        self.assertEqual(result["dependency_nodes"], 503)
        self.assertEqual(result["dependency_edges"], 54)

    def test_valid_complete_diagnostics_and_empty_compiles(self):
        self.assertIs(self.diagnostics(stream(self.records))["accepted"], True)
        for phase in ("reader", "apdu"):
            self.assertIsNone(self.diagnostics(b"", phase=phase))

    def test_wrong_candidate_inventory_even_with_reconciled_counts(self):
        for delta in (-1, 1):
            with self.subTest(delta=delta):
                rows = copy.deepcopy(self.records)
                if delta < 0:
                    name = select(rows, "candidate_declaration")[-1]["actual_name"]
                    rows = [r for r in rows if r.get("actual_name") != name]
                else:
                    extra = copy.deepcopy(select(rows, "candidate_declaration")[-1])
                    extra["actual_name"] = extra["user_name"] = "APDUControl.extra"
                    rows.insert(549, extra)
                    rows.insert(-1, {"record": "dependency", "actual_name": "APDUControl.extra",
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
        for mutation in ("duplicate", "missing", "reordered"):
            with self.subTest(mutation=mutation):
                rows = copy.deepcopy(self.records)
                if mutation == "duplicate":
                    rows[2] = copy.deepcopy(rows[1])
                elif mutation == "missing":
                    del rows[1]
                else:
                    rows[1], rows[2] = rows[2], rows[1]
                self.reject("unique exact theorem resolution", rows)

    def test_wrong_private_owner_user_name_and_privacy(self):
        for field, value in (("owner", "Oak.Stdlib.BoundedReaderModel"),
                             ("user_name", "Wrong.theorem"), ("private", False)):
            with self.subTest(field=field):
                rows = copy.deepcopy(self.records)
                theorem = next(r for r in rows if r.get("record") == "expected_theorem" and r["private"])
                theorem[field] = value
                self.reject("unique exact theorem resolution", rows)

    def test_private_marker_and_public_actual_name(self):
        for private, message in ((True, "private actual-name marker"),
                                 (False, "public theorem exact actual name")):
            with self.subTest(private=private):
                rows = copy.deepcopy(self.records)
                theorem = next(r for r in rows if r.get("record") == "expected_theorem" and r["private"] is private)
                theorem["actual_name"] = "Unexpected.name"
                self.reject(message, rows)

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
        for name in ("sorryAx", "Lean.trustCompiler", "Unapproved.axiom"):
            with self.subTest(name=name):
                rows = copy.deepcopy(self.records)
                node = select(rows, "dependency")[-1]
                node["actual_name"] = name
                node["kind"] = "axiom"
                self.reject("unique approved dependency kind", rows)

    def test_unapproved_and_duplicate_axiom_claim(self):
        for axioms, message in ((["Unapproved.axiom"], "only approved foundational axioms"),
                                 (["propext", "propext"], "duplicate name forbidden")):
            with self.subTest(axioms=axioms):
                rows = copy.deepcopy(self.records)
                rows[1]["axioms"] = axioms
                self.reject(message, rows)

    def test_theorem_candidate_kind_mismatch(self):
        candidate = select(self.records, "candidate_declaration")[0]
        candidate["kind"] = "definition"
        node = next(r for r in select(self.records, "dependency") if r["actual_name"] == candidate["actual_name"])
        node["kind"] = "definition"
        self.reject("theorem/candidate record equality")

    def test_candidate_shared_edge_mismatch(self):
        select(self.records, "candidate_declaration")[0]["direct_dependencies"] = []
        self.reject("candidate and shared graph equality")

    def test_theorem_candidate_record_mismatch(self):
        select(self.records, "candidate_declaration")[0]["user_name"] = "Wrong.name"
        self.reject("theorem/candidate record equality")

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
        self.records[-1]["anonymous_examples_persisted"] = True
        self.reject("examples do not persist")

    def test_record_schema_and_section_order(self):
        for mutation, message in (("unknown-key", "exact audit record schema"),
                                   ("wrong-order", "candidate section/order/count")):
            with self.subTest(mutation=mutation):
                rows = copy.deepcopy(self.records)
                if mutation == "unknown-key":
                    rows[1]["unknown"] = None
                else:
                    rows[1], rows[49] = rows[49], rows[1]
                self.reject(message, rows)

    def test_empty_truncated_and_extra_blank_diagnostic_stream(self):
        raw = stream(self.records)
        for output, message in ((b"", "complete bounded audit stdout"),
                                (raw[:-1], "complete bounded audit stdout"),
                                (raw + b"\n", "audit parsing original deadline/empty line")):
            with self.subTest(message=message):
                with self.assertRaisesRegex(RuntimeError, message):
                    self.diagnostics(output)

    def test_unexpected_compile_stdout_and_any_stderr(self):
        with self.assertRaisesRegex(RuntimeError, "reader/APDU must have no diagnostics"):
            self.diagnostics(b"warning\n", phase="reader")
        with self.assertRaisesRegex(RuntimeError, "complete stderr must be empty"):
            self.diagnostics(stream(self.records), b"warning\n")

    def test_diagnostic_identity_severity_and_schema(self):
        for field, value in (("fileName", "/wrong/AuditDriver.lean"), ("severity", "warning"),
                             ("isSilent", True), ("kind", "unexpected")):
            with self.subTest(field=field):
                message = diagnostic(self.records[0])
                message[field] = value
                with self.assertRaisesRegex(RuntimeError, "only exact driver informational audit messages"):
                    self.diagnostics(encode(message) + b"\n")
        message = diagnostic(self.records[0])
        del message["endPos"]
        with self.assertRaisesRegex(RuntimeError, "exact audit record schema"):
            self.diagnostics(encode(message) + b"\n")

    def test_diagnostic_position_requires_bounded_integer(self):
        for value in (True, -1, 2 ** 32, 1.5):
            with self.subTest(value=value):
                message = diagnostic(self.records[0])
                message["pos"]["line"] = value
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


class AdapterControls(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="reader-apdu-controls-")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.clock = mock.patch.object(SUPPORT.time, "monotonic", return_value=10.0)
        self.clock.start()
        self.addCleanup(self.clock.stop)
        self.addCleanup(self._check_temporary_budget)

    def _check_temporary_budget(self):
        """Check only this method's private fixture tree before removing it."""
        todo = [self.root]
        count = 1
        logical = 0
        allocated = self.root.lstat().st_blocks * 512
        while todo:
            with os.scandir(todo.pop()) as entries:
                for entry in entries:
                    count += 1
                    self.assertLessEqual(count, 128, "temporary fixture entry budget")
                    info = entry.stat(follow_symlinks=False)
                    allocated += info.st_blocks * 512
                    if stat.S_ISDIR(info.st_mode):
                        todo.append(Path(entry.path))
                    else:
                        logical += info.st_size
                    self.assertLessEqual(logical, 1024**2, "temporary logical-byte budget")
                    self.assertLessEqual(allocated, 2 * 1024**2, "temporary allocated-byte budget")

    def leaf(self, name="leaf", data=b"reviewed bytes"):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)
        path.chmod(0o600)
        return path, {"bytes": len(data), "sha256": hashlib.sha256(data).hexdigest()}

    def test_valid_leaf_and_exact_contract(self):
        path, expected = self.leaf()
        actual = SUPPORT.verify_file(path, expected, DEADLINE)
        self.assertEqual({key: actual[key] for key in ("bytes", "sha256")}, expected)
        self.assertEqual(actual["snapshot"], list(SUPPORT.identity(path.stat())))
        self.assertEqual(CHECK.load_contract(ADAPTER), CONTRACT)

    def test_source_driver_consumer_and_tool_byte_mutation(self):
        for name in ("BoundedReaderModel.lean", "APDULengthModel.lean", "AuditDriver.lean",
                     "audit_consumer.py", "support.py", "bin/lean"):
            with self.subTest(name=name):
                path, expected = self.leaf(name, b"original")
                path.write_bytes(b"modified")
                with self.assertRaisesRegex(RuntimeError, "selected source/tool drift"):
                    SUPPORT.verify_file(path, expected, DEADLINE)

    def test_changed_contract_metadata(self):
        for field, changed in (("toolchain", "leanprover/lean4:other"),
                               ("flags", []), ("distribution_modules", []), ("expected", {})):
            with self.subTest(field=field):
                contract = copy.deepcopy(CONTRACT)
                contract[field] = changed
                (self.root / "contract.json").write_bytes(encode(contract))
                with self.assertRaisesRegex(RuntimeError, "locked contract bytes"):
                    CHECK.load_contract(self.root)

    def test_missing_lean_refused_before_work_creation(self):
        work = self.root / "unused-work"
        argv = ["check.py", "--lean", str(self.root / "missing/bin/lean"), "--work", str(work)]
        with mock.patch.object(CHECK.sys, "argv", argv), \
             mock.patch.object(CHECK.sys, "platform", "linux"), \
             mock.patch.object(CHECK.platform, "machine", return_value="x86_64"), \
             mock.patch.object(CHECK.signal, "signal"):
            with self.assertRaisesRegex(RuntimeError, "selected executable path"):
                CHECK.main()
        self.assertFalse(work.exists())

    def test_existing_work_refused_before_authentication(self):
        lean, _ = self.leaf("bin/lean", b"synthetic executable, never invoked")
        lean.chmod(0o700)
        work = self.root / "stale-work"
        work.mkdir()
        argv = ["check.py", "--lean", str(lean), "--work", str(work)]
        with mock.patch.object(CHECK.sys, "argv", argv), \
             mock.patch.object(CHECK.sys, "platform", "linux"), \
             mock.patch.object(CHECK.platform, "machine", return_value="x86_64"), \
             mock.patch.object(CHECK.signal, "signal"):
            with self.assertRaisesRegex(RuntimeError, "fresh work directory required"):
                CHECK.main()
        self.assertEqual(list(work.iterdir()), [])

    def test_invalid_leaf_metadata(self):
        path, expected = self.leaf()
        for field, value in (("bytes", True), ("bytes", -1), ("bytes", 1.0),
                             ("sha256", "f" * 63), ("sha256", "G" * 64)):
            with self.subTest(field=field, value=value):
                changed = dict(expected, **{field: value})
                with self.assertRaisesRegex(RuntimeError, "exact leaf identity"):
                    SUPPORT.verify_file(path, changed, DEADLINE)

    def test_missing_leaf_and_bounded_read(self):
        with self.assertRaises(FileNotFoundError):
            SUPPORT.read_regular(self.root / "missing", 32)
        path, _ = self.leaf(data=b"12345")
        with self.assertRaisesRegex(RuntimeError, "regular bounded input"):
            SUPPORT.read_regular(path, 4)

    def test_symlink_leaf_and_symlink_ancestor(self):
        path, expected = self.leaf("source/data")
        link = self.root / "alias"
        link.symlink_to(path)
        ancestor = self.root / "aliased-directory"
        ancestor.symlink_to(path.parent, target_is_directory=True)
        for target in (link, ancestor / path.name):
            with self.subTest(target=str(target)):
                with self.assertRaisesRegex(RuntimeError, "input alias"):
                    SUPPORT.verify_file(target, expected, DEADLINE)

    def test_hardlink_input_refused(self):
        path, expected = self.leaf()
        os.link(path, self.root / "hardlink")
        with self.assertRaisesRegex(RuntimeError, "selected exact type/length"):
            SUPPORT.verify_file(path, expected, DEADLINE)

    def test_wrong_leaf_owner_without_chown(self):
        path, expected = self.leaf()
        real = path.stat()
        attributes = {name: getattr(real, name) for name in (
            "st_dev", "st_ino", "st_mode", "st_uid", "st_nlink", "st_size",
            "st_mtime_ns", "st_ctime_ns")}
        attributes["st_uid"] = os.getuid() + 100000
        with mock.patch.object(SUPPORT.os, "fstat", return_value=SimpleNamespace(**attributes)):
            with self.assertRaisesRegex(RuntimeError, "selected exact type/length"):
                SUPPORT.verify_file(path, expected, DEADLINE)

    def test_leaf_replaced_during_bounded_read(self):
        path, _ = self.leaf()
        original = path.stat()
        attributes = {name: getattr(original, name) for name in (
            "st_dev", "st_ino", "st_mode", "st_uid", "st_nlink", "st_size",
            "st_mtime_ns", "st_ctime_ns")}
        attributes["st_ino"] += 1
        with mock.patch.object(SUPPORT.os, "fstat", side_effect=[original, SimpleNamespace(**attributes)]):
            with self.assertRaisesRegex(RuntimeError, "stable bounded input"):
                SUPPORT.read_regular(path, 64)

    def test_unexpected_and_stale_object_membership(self):
        objects = self.root / "objects"
        target = objects / "Oak/Stdlib"
        target.mkdir(parents=True)
        CHECK.inspect_objects(objects, {}, DEADLINE)
        (target / "BoundedReaderModel.olean").write_bytes(b"stale object")
        with self.assertRaisesRegex(RuntimeError, "exact object membership"):
            CHECK.inspect_objects(objects, {}, DEADLINE)
        (target / "foreign.olean").write_bytes(b"unexpected object")
        with self.assertRaisesRegex(RuntimeError, "exact object membership"):
            CHECK.inspect_objects(objects, {}, DEADLINE)

    def test_same_bytes_object_replacement_is_rejected(self):
        objects = self.root / "objects"
        directory = objects / "Oak/Stdlib"
        directory.mkdir(parents=True)
        target = directory / "BoundedReaderModel.olean"
        target.write_bytes(b"fresh object")
        target.chmod(0o600)
        expected = {target.name: CHECK.object_identity(target)}
        CHECK.inspect_objects(objects, expected, DEADLINE)
        replacement = self.root / "replacement"
        replacement.write_bytes(b"fresh object")
        replacement.chmod(0o600)
        replacement.replace(target)
        with self.assertRaisesRegex(RuntimeError, "same owned object identity"):
            CHECK.inspect_objects(objects, expected, DEADLINE)

    def test_object_owner_and_private_mode(self):
        path, expected = self.leaf(data=b"fresh object")
        path.chmod(0o600)
        binding = CHECK.object_identity(path)
        for index, value in ((3, os.getuid() + 100000), (2, path.stat().st_mode | 0o040)):
            with self.subTest(snapshot_index=index):
                snapshot = list(binding["snapshot"])
                snapshot[index] = value
                with mock.patch.object(CHECK, "read_regular", return_value=(b"fresh object", snapshot)):
                    with self.assertRaisesRegex(RuntimeError, "owned private object"):
                        CHECK.object_identity(path)

    def test_fresh_storage_logical_and_allocated_overflow(self):
        path, _ = self.leaf(data=b"x")
        path.chmod(0o600)
        real = path.stat()
        for logical, blocks in ((CHECK.FRESH_BYTES + 1, 0),
                                (1, CHECK.FRESH_BYTES // 512 + 1)):
            with self.subTest(logical=logical, blocks=blocks):
                item = SimpleNamespace(st_mode=real.st_mode, st_uid=os.getuid(), st_nlink=1,
                                       st_size=logical, st_blocks=blocks)
                entry = SimpleNamespace(path=str(path), stat=lambda **kw: item)
                with mock.patch.object(CHECK.os, "scandir", return_value=nullcontext(iter([entry]))):
                    with self.assertRaisesRegex(RuntimeError, "fresh logical/allocated output cap"):
                        CHECK.storage_usage(self.root)

    def test_fresh_storage_owner_alias_and_directory_mode(self):
        path, _ = self.leaf(data=b"x")
        real = path.stat()
        item = SimpleNamespace(st_mode=real.st_mode, st_uid=os.getuid() + 100000,
                               st_nlink=1, st_size=1, st_blocks=0)
        entry = SimpleNamespace(path=str(path), stat=lambda **kw: item)
        with mock.patch.object(CHECK.os, "scandir", return_value=nullcontext(iter([entry]))):
            with self.assertRaisesRegex(RuntimeError, "fresh output owner"):
                CHECK.storage_usage(self.root)
        alias = self.root / "alias"
        alias.symlink_to(path)
        with self.assertRaisesRegex(RuntimeError, "fresh regular unaliased output"):
            CHECK.storage_usage(self.root)
        alias.unlink()
        (self.root / "public-directory").mkdir(mode=0o755)
        (self.root / "public-directory").chmod(0o755)
        with self.assertRaisesRegex(RuntimeError, "private owned output directory"):
            CHECK.storage_usage(self.root)

    def test_fresh_storage_entry_and_depth_caps(self):
        for i in range(64):
            (self.root / str(i)).touch(mode=0o600)
        CHECK.storage_usage(self.root)
        (self.root / "extra").touch(mode=0o600)
        with self.assertRaisesRegex(RuntimeError, "fresh output entry cap"):
            CHECK.storage_usage(self.root)
        nested = self.root / "depth"
        nested.mkdir(mode=0o700)
        current = nested
        for _ in range(5):
            current = current / "child"
            current.mkdir(mode=0o700)
        with self.assertRaisesRegex(RuntimeError, "fresh directory depth cap"):
            CHECK.storage_usage(nested)

    def test_output_creation_is_exclusive_and_no_follow(self):
        output = self.root / "capture.log"
        CHECK.write_new(output, b"complete stream")
        self.assertEqual(output.read_bytes(), b"complete stream")
        self.assertEqual(output.stat().st_mode & 0o777, 0o600)
        with self.assertRaises(FileExistsError):
            CHECK.write_new(output, b"replacement")
        alias = self.root / "alias.log"
        alias.symlink_to(output)
        with self.assertRaisesRegex(RuntimeError, "input alias"):
            CHECK.write_new(alias, b"replacement")
        self.assertEqual(output.read_bytes(), b"complete stream")

    def test_distribution_metadata_count_size_and_path(self):
        with self.assertRaisesRegex(RuntimeError, "exact selected distribution size"):
            CHECK.verify_distribution(self.root, {}, DEADLINE)
        count, total = 6289, 1100616161
        files = {"lib/lean/Control" + str(i) + ".olean":
                 {"bytes": total // count + (1 if i < total % count else 0), "sha256": "0" * 64}
                 for i in range(count)}
        with mock.patch.object(CHECK, "verify_file") as verify:
            CHECK.verify_distribution(self.root, files, DEADLINE)
            self.assertEqual(verify.call_count, count)
            verify.reset_mock()
            first = next(iter(files))
            files[first]["bytes"] += 1
            with self.assertRaisesRegex(RuntimeError, "exact selected distribution size"):
                CHECK.verify_distribution(self.root, files, DEADLINE)
            files[first]["bytes"] -= 1
            files["../outside"] = files.pop(first)
            with self.assertRaisesRegex(RuntimeError, "distribution relative path"):
                CHECK.verify_distribution(self.root, files, DEADLINE)

    def test_phase_deadline_clipping_and_no_reserve(self):
        self.assertEqual(CHECK.phase_deadline(480, 120, 100), 220)
        self.assertEqual(CHECK.phase_deadline(200, 180, 100), 170)
        with self.assertRaisesRegex(RuntimeError, "phase has no cleanup reserve"):
            CHECK.phase_deadline(135, 120, 100)

    def test_authentication_uses_original_deadline(self):
        path, expected = self.leaf()
        with mock.patch.object(SUPPORT.time, "monotonic", return_value=DEADLINE):
            with self.assertRaisesRegex(RuntimeError, "authentication original deadline"):
                SUPPORT.verify_file(path, expected, DEADLINE)

    def test_direct_completion_requires_zero_join_full_eof_and_live_deadline(self):
        self.assertIsNone(CHECK.validate_completion(0, {"stdout", "stderr"}, False, 19.0, DEADLINE))
        cases = [
            (None, {"stdout", "stderr"}, False, 19.0),
            (1, {"stdout", "stderr"}, False, 19.0),
            (-9, {"stdout", "stderr"}, False, 19.0),
            (False, {"stdout", "stderr"}, False, 19.0),
            (0, set(), False, 19.0),
            (0, {"stdout"}, False, 19.0),
            (0, {"stderr"}, False, 19.0),
            (0, {"stdout", "stderr", "unexpected"}, False, 19.0),
            (0, {"stdout", "stderr"}, True, 19.0),
            (0, {"stdout", "stderr"}, 0, 19.0),
            (0, {"stdout", "stderr"}, False, DEADLINE),
        ]
        for status, eof, overflow, now in cases:
            with self.subTest(status=status, eof=eof, overflow=overflow, now=now):
                with self.assertRaisesRegex(RuntimeError, "complete successful leaf"):
                    CHECK.validate_completion(status, eof, overflow, now, DEADLINE)

    def test_capture_accepts_cap_and_refuses_one_extra_byte(self):
        capture = CHECK.Capture(8)
        capture.append("stdout", b"1234")
        capture.append("stdout", b"5678")
        self.assertFalse(capture.overflow)
        with self.assertRaisesRegex(RuntimeError, "output cap exceeded"):
            capture.append("stdout", b"9")
        self.assertTrue(capture.overflow)
        self.assertEqual(bytes(capture.data["stdout"]), b"12345678")
        self.assertEqual(len(capture.data["stdout"]), 8)
        stderr = CHECK.Capture(8)
        stderr.append("stderr", b"x" * (512 * 1024))
        with self.assertRaisesRegex(RuntimeError, "output cap exceeded"):
            stderr.append("stderr", b"x")
        self.assertEqual(len(stderr.data["stderr"]), 512 * 1024)
        self.assertEqual(CHECK.Capture(12 * 1024**2).caps["stdout"], 12 * 1024**2)

    def test_resource_limits_without_changing_this_process(self):
        with mock.patch.object(CHECK.resource, "setrlimit") as limit, \
             mock.patch.object(CHECK.os, "umask") as umask:
            CHECK.leaf_limits()
        self.assertEqual(limit.call_args_list, [
            mock.call(CHECK.resource.RLIMIT_AS, (8 * 1024**3, 8 * 1024**3)),
            mock.call(CHECK.resource.RLIMIT_FSIZE, (8 * 1024**2, 8 * 1024**2)),
            mock.call(CHECK.resource.RLIMIT_CORE, (0, 0)),
        ])
        umask.assert_called_once_with(0o077)

    def test_duplicate_nonfinite_deep_and_truncated_json(self):
        for raw, message in ((b'{"x":1,"x":2}', "duplicate JSON key"),
                              (b"NaN", "nonfinite JSON"), (b"Infinity", "nonfinite JSON"),
                              (b"-Infinity", "nonfinite JSON"), (b"1e9999", "nonfinite JSON"),
                              (b"[" * 17 + b"0" + b"]" * 17, "bounded metadata depth")):
            with self.subTest(raw=raw):
                with self.assertRaisesRegex(RuntimeError, message):
                    SUPPORT.decode(raw)
        with self.assertRaises(json.JSONDecodeError):
            SUPPORT.decode(b'{"truncated":')
        with self.assertRaises(UnicodeDecodeError):
            SUPPORT.decode(b'"\xff"')


def main():
    global ADAPTER, CHECK, CONSUMER, SUPPORT, CONTRACT
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--adapter-directory", type=Path, default=Path(__file__).parent)
    args, remaining = parser.parse_known_args()
    ADAPTER = args.adapter_directory.absolute()
    sys.dont_write_bytecode = True
    sys.path.insert(0, str(ADAPTER))
    refusal = AssertionError("controls must never launch a subprocess")
    with mock.patch.object(subprocess, "Popen", side_effect=refusal), \
         mock.patch.object(subprocess, "run", side_effect=refusal), \
         mock.patch.object(subprocess, "call", side_effect=refusal), \
         mock.patch.object(subprocess, "check_call", side_effect=refusal), \
         mock.patch.object(subprocess, "check_output", side_effect=refusal):
        SUPPORT = importlib.import_module("support")
        CONSUMER = importlib.import_module("audit_consumer")
        CHECK = importlib.import_module("check")
        CONTRACT = CHECK.load_contract(ADAPTER)
        unittest.main(argv=[sys.argv[0], *remaining])


if __name__ == "__main__":
    main()
