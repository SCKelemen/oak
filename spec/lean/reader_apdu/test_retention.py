"""Finite SOURCE-ONLY retention controls; no execution is authorized by this file.

Run only after separate authorization, in place of test_check.py under the same
single 60-second control timeout and two-minute workflow step. BASE.main retains
all five subprocess-refusal patches and discovers its two unchanged classes plus
RetentionControls in __main__. Synthetic bytes are not Lean proof evidence.
"""
import sys

sys.dont_write_bytecode = True

import copy
from contextlib import contextmanager, ExitStack
import hashlib
import json
import os
from pathlib import Path
import shutil
import stat
import tempfile
from types import SimpleNamespace
import unittest
from unittest import mock

import test_check as BASE
from test_check import AdapterControls, ConsumerControls


FILES = ("audit-stdout.log", "audit-stderr.log", "result.json", "object-hashes.json")
OBJECTS = ("BoundedReaderModel.olean", "APDULengthModel.olean")
AUDIT_CAP = 12 * 1024**2
METADATA_CAP = 32768
FIXTURE_CAP = 1536 * 1024
SCRATCH_CAP = 4 * 1024**2
DEADLINE = BASE.DEADLINE


class RetentionControls(unittest.TestCase):
    def setUp(self):
        self.C = BASE.CHECK
        self.temporary = tempfile.TemporaryDirectory(prefix="reader-apdu-retention-controls-")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.addCleanup(self.check_scratch)
        self.clock = mock.patch.object(self.C.time, "monotonic", return_value=10.0)
        self.clock.start()
        self.addCleanup(self.clock.stop)
        self.contract = BASE.CONTRACT
        self.stdout = BASE.stream(BASE.fixture(self.contract))
        self.assertLessEqual(len(self.stdout), FIXTURE_CAP, "retention synthetic stream scratch bound")
        self.summary = BASE.CONSUMER.diagnostics(
            self.stdout, b"", "audit", DEADLINE, BASE.ADAPTER / "AuditDriver.lean", self.contract)
        receipts = {}
        for name in OBJECTS:
            path = self.root / name
            self.C.write_new(path, ("synthetic receipt " + name).encode())
            receipts[name] = self.C.object_identity(path)
        lean = "/synthetic/retention/bin/lean"
        driver = str(BASE.ADAPTER / "AuditDriver.lean")
        records = [self.record(phase, [lean, "synthetic-" + phase])
                   for phase in ("reader", "apdu")]
        records.append(self.record("audit", [lean, *self.C.FLAGS,
                                             "--root=" + str(BASE.ADAPTER), driver]))
        self.result = {"accepted": True, "implementation_refinement": False,
                       "source_contract_sha256": self.C.CONTRACT_SHA256,
                       "objects": receipts, "audit": self.summary,
                       "direct_processes": records}
        self.work = self.root / "retained"
        self.work.mkdir(mode=0o700)

    def check_scratch(self):
        todo = [self.root]
        count = 1
        logical = 0
        allocated = self.root.lstat().st_blocks * 512
        while todo:
            with os.scandir(todo.pop()) as entries:
                for entry in entries:
                    count += 1
                    info = entry.stat(follow_symlinks=False)
                    allocated += info.st_blocks * 512
                    if stat.S_ISDIR(info.st_mode):
                        todo.append(Path(entry.path))
                    else:
                        logical += info.st_size
                    self.assertLessEqual(count, 128, "retention fixture entry budget")
                    self.assertLessEqual(logical, SCRATCH_CAP, "retention logical scratch budget")
                    self.assertLessEqual(allocated, SCRATCH_CAP, "retention allocated scratch budget")

    @staticmethod
    def record(phase, argv):
        return {"phase": phase, "argv": argv, "returncode": 0,
                "pipe_eof": ["stderr", "stdout"], "overflow": False,
                "direct_child_joined": True,
                "arbitrary_descendant_emptiness_established": False,
                "wall_seconds": 0.0, "peak_direct_rss": 0}

    def manifest(self, result=None, stdout=None, stderr=b""):
        return self.C.retention_manifest(self.result if result is None else result,
                                         self.stdout if stdout is None else stdout,
                                         stderr, self.contract)

    def bundle(self, result=None):
        result = self.result if result is None else result
        leaves = {"audit-stdout.log": self.stdout, "audit-stderr.log": b"",
                  "result.json": self.C.retained_json(result),
                  "object-hashes.json": self.manifest(result)}
        for name, data in leaves.items():
            path = self.work / name
            if path.exists() or path.is_symlink():
                path.unlink()
            self.C.write_new(path, data)
        self.check_scratch()
        return leaves

    def verify(self):
        with mock.patch.object(self.C, "load_contract", return_value=self.contract):
            return self.C.verify_retention(self.work, DEADLINE)

    def reject_result(self, result, message):
        with self.assertRaisesRegex(RuntimeError, message):
            self.manifest(result)

    def test_positive_private_stream_manifest_and_preflight(self):
        leaves = self.bundle()
        self.assertIn(b"_private.control", leaves["audit-stdout.log"])
        self.assertEqual((self.summary["named_theorems"], self.summary["source_examples"],
                          self.summary["candidate_declarations"]), (48, 15, 500))
        manifest = BASE.SUPPORT.decode(leaves["object-hashes.json"])
        self.assertEqual(leaves["object-hashes.json"], self.manifest(copy.deepcopy(self.result)))
        self.assertEqual(manifest["source_inputs"], self.contract["inputs"])
        self.assertEqual(len(manifest["source_inputs"]), 6)
        for key in ("toolchain", "lean_executable_sha256", "official_linux_archive_sha256"):
            self.assertEqual(manifest[key], self.contract[key])
        self.assertEqual(manifest["source_contract_sha256"], self.C.CONTRACT_SHA256)
        self.assertEqual(set(manifest["objects"]), set(OBJECTS))
        self.assertEqual(set(manifest["files"]), set(FILES) - {"object-hashes.json"})
        for name, receipt in manifest["files"].items():
            self.assertEqual(receipt, {"bytes": len(leaves[name]),
                                      "sha256": hashlib.sha256(leaves[name]).hexdigest()})
        for name in OBJECTS:
            self.assertEqual(manifest["objects"][name],
                             {key: self.result["objects"][name][key] for key in ("bytes", "sha256")})
        self.assertEqual(manifest["audit_driver_path"], str(BASE.ADAPTER / "AuditDriver.lean"))
        self.assertIsNone(self.verify())

    def test_accepted_and_refinement_exact_booleans(self):
        for field, values in (("accepted", (False, 1, None)),
                              ("implementation_refinement", (True, 0, None))):
            for value in values:
                with self.subTest(field=field, value=value):
                    result = copy.deepcopy(self.result)
                    result[field] = value
                    self.reject_result(result, "only accepted abstract-model evidence")

    def test_result_source_contract_binding(self):
        for value in (None, "0" * 64, self.C.CONTRACT_SHA256.upper(), True):
            with self.subTest(value=value):
                result = copy.deepcopy(self.result)
                result["source_contract_sha256"] = value
                self.reject_result(result, "retained source contract binding")

    def test_object_inventory(self):
        for mutation in ("missing", "replacement", "extra", "wrong-type"):
            with self.subTest(mutation=mutation):
                result = copy.deepcopy(self.result)
                objects = result["objects"]
                if mutation == "missing":
                    del objects[OBJECTS[0]]
                elif mutation == "replacement":
                    objects["Other.olean"] = objects.pop(OBJECTS[0])
                elif mutation == "extra":
                    objects["Other.olean"] = copy.deepcopy(objects[OBJECTS[0]])
                else:
                    result["objects"] = list(objects)
                self.reject_result(result, "exact retained object inventory")

    def test_object_receipt_exact_keys_and_scalar_types(self):
        mutations = (("bytes", True), ("bytes", 0), ("bytes", -1), ("bytes", 1.0),
                     ("bytes", 8 * 1024**2 + 1), ("sha256", None), ("sha256", "f" * 63),
                     ("sha256", "F" * 64), ("sha256", "g" * 64))
        for name in OBJECTS:
            for field, value in mutations:
                with self.subTest(name=name, field=field, value=value):
                    result = copy.deepcopy(self.result)
                    result["objects"][name][field] = value
                    self.reject_result(result, "typed bounded retained object receipt")
            for field in ("bytes", "sha256", "snapshot", "extra", "wrong-type"):
                with self.subTest(name=name, schema=field):
                    result = copy.deepcopy(self.result)
                    receipt = result["objects"][name]
                    if field == "extra":
                        receipt[field] = None
                    elif field == "wrong-type":
                        result["objects"][name] = []
                    else:
                        del receipt[field]
                    self.reject_result(result, "typed bounded retained object receipt")

    def test_object_snapshot_shape_type_and_coherence(self):
        mutations = ((0, -1), (0, False), (1, 0), (2, stat.S_IFDIR | 0o700),
                     (2, stat.S_IFREG | 0o640), (3, -1), (4, 2), (4, 0),
                     (5, 0), (6, 1.0), (7, True))
        for name in OBJECTS:
            for index, value in mutations:
                with self.subTest(name=name, index=index, value=value):
                    result = copy.deepcopy(self.result)
                    result["objects"][name]["snapshot"][index] = value
                    self.reject_result(result, "retained object snapshot coherence")
            for shape in ("short", "long", "tuple"):
                with self.subTest(name=name, shape=shape):
                    result = copy.deepcopy(self.result)
                    snapshot = result["objects"][name]["snapshot"]
                    result["objects"][name]["snapshot"] = (snapshot[:-1] if shape == "short" else
                                                           snapshot + [0] if shape == "long" else
                                                           tuple(snapshot))
                    self.reject_result(result, "retained object snapshot coherence")

    def test_object_receipt_maximum_size(self):
        result = copy.deepcopy(self.result)
        for name in OBJECTS:
            result["objects"][name]["bytes"] = 8 * 1024**2
            result["objects"][name]["snapshot"][5] = 8 * 1024**2
        manifest = BASE.SUPPORT.decode(self.manifest(result))
        self.assertEqual([manifest["objects"][name]["bytes"] for name in OBJECTS],
                         [8 * 1024**2, 8 * 1024**2])

    def test_exact_reader_apdu_audit_sequence(self):
        for mutation in ("missing", "extra", "reordered", "duplicate", "wrong-type"):
            with self.subTest(mutation=mutation):
                result = copy.deepcopy(self.result)
                records = result["direct_processes"]
                if mutation == "missing":
                    records.pop()
                elif mutation == "extra":
                    records.append(copy.deepcopy(records[-1]))
                elif mutation == "reordered":
                    records[0], records[1] = records[1], records[0]
                elif mutation == "duplicate":
                    records[1] = copy.deepcopy(records[0])
                else:
                    result["direct_processes"] = tuple(records)
                self.reject_result(result, "retained direct sequence")

    def test_each_direct_success_receipt(self):
        mutations = (("phase", "other"), ("returncode", None), ("returncode", 1),
                     ("returncode", -9), ("returncode", False),
                     ("pipe_eof", []), ("pipe_eof", ["stdout"]), ("pipe_eof", ["stderr"]),
                     ("pipe_eof", ["stdout", "stderr"]),
                     ("pipe_eof", ["stderr", "stdout", "extra"]),
                     ("overflow", True), ("overflow", 0),
                     ("direct_child_joined", False), ("direct_child_joined", 1),
                     ("arbitrary_descendant_emptiness_established", True),
                     ("arbitrary_descendant_emptiness_established", 0))
        for index, phase in enumerate(("reader", "apdu", "audit")):
            for field, value in mutations:
                with self.subTest(phase=phase, field=field, value=value):
                    result = copy.deepcopy(self.result)
                    result["direct_processes"][index][field] = value
                    self.reject_result(result, "complete retained direct sequence")

    def test_each_argv_is_bounded_and_uses_same_executable(self):
        for index, phase in enumerate(("reader", "apdu", "audit")):
            for argv in (None, [], ["x"] * 33, [False], ["x\x00"], ["x" * 4097]):
                with self.subTest(phase=phase, argv_kind=str(type(argv)), count=len(argv or [])):
                    result = copy.deepcopy(self.result)
                    result["direct_processes"][index]["argv"] = argv
                    self.reject_result(result, "bounded retained argv")
        for index in (0, 1):
            with self.subTest(different_executable_phase=index):
                result = copy.deepcopy(self.result)
                result["direct_processes"][index]["argv"][0] = "/different/bin/lean"
                self.reject_result(result, "same retained Lean executable")

    def test_audit_argv_exact_flags_and_paths(self):
        for index in range(1, 1 + len(self.C.FLAGS)):
            with self.subTest(flag_index=index):
                result = copy.deepcopy(self.result)
                result["direct_processes"][-1]["argv"][index] += "-changed"
                self.reject_result(result, "exact retained audit argv")
        original = self.result["direct_processes"][-1]["argv"]
        variants = [original[:-1], original + ["--extra"],
                    [original[0], *reversed(original[1:-2]), *original[-2:]]]
        for argv in variants:
            with self.subTest(argv=argv):
                result = copy.deepcopy(self.result)
                result["direct_processes"][-1]["argv"] = argv
                self.reject_result(result, "exact retained audit argv")
        paths = ((0, "relative/bin/lean"), (0, "/synthetic//bin/lean"),
                 (0, "/synthetic/../bin/lean"), (0, "/synthetic/bin/not-lean"),
                 (0, "/synthetic/tools/lean"), (-1, "spec/lean/reader_apdu/AuditDriver.lean"),
                 (-1, "/other/AuditDriver.lean"),
                 (-1, str(BASE.ADAPTER) + "/./AuditDriver.lean"),
                 (-1, str(BASE.ADAPTER / "NotAuditDriver.lean")),
                 (-2, "--root=/different"), (-2, "--root=" + str(BASE.ADAPTER) + "/"))
        for index, path in paths:
            with self.subTest(path_index=index, value=path):
                result = copy.deepcopy(self.result)
                result["direct_processes"][-1]["argv"][index] = path
                self.reject_result(result, "retained (path|audit paths)")

    def test_manifest_locked_source_and_tool_bindings(self):
        leaves = self.bundle()
        baseline = BASE.SUPPORT.decode(leaves["object-hashes.json"])
        changes = [("source_contract_sha256", "0" * 64), ("toolchain", "other"),
                   ("lean_executable_sha256", "0" * 64),
                   ("official_linux_archive_sha256", "0" * 64),
                   ("schema", "other"), ("scope", "overstated proof"),
                   ("audit_driver_path", "/other/AuditDriver.lean")]
        for field, value in changes:
            with self.subTest(field=field):
                manifest = copy.deepcopy(baseline)
                manifest[field] = value
                (self.work / "object-hashes.json").write_bytes(self.C.retained_json(manifest))
                with self.assertRaisesRegex(RuntimeError, "exact retained evidence manifest"):
                    self.verify()
        for name in sorted(self.contract["inputs"]):
            for field in ("bytes", "sha256"):
                with self.subTest(source=name, field=field):
                    manifest = copy.deepcopy(baseline)
                    manifest["source_inputs"][name][field] = (0 if field == "bytes" else "0" * 64)
                    (self.work / "object-hashes.json").write_bytes(self.C.retained_json(manifest))
                    with self.assertRaisesRegex(RuntimeError, "exact retained evidence manifest"):
                        self.verify()

    def test_manifest_file_inventory_and_object_reconciliation(self):
        leaves = self.bundle()
        baseline = BASE.SUPPORT.decode(leaves["object-hashes.json"])
        for mutation in ("missing", "renamed", "extra"):
            with self.subTest(inventory=mutation):
                manifest = copy.deepcopy(baseline)
                files = manifest["files"]
                if mutation == "missing":
                    del files["audit-stdout.log"]
                elif mutation == "renamed":
                    files["other.log"] = files.pop("audit-stdout.log")
                else:
                    files["object-hashes.json"] = {"bytes": 0, "sha256": "0" * 64}
                (self.work / "object-hashes.json").write_bytes(self.C.retained_json(manifest))
                with self.assertRaisesRegex(RuntimeError, "exact retained evidence manifest"):
                    self.verify()
        for section, names in (("objects", OBJECTS), ("files", FILES[:3])):
            for name in names:
                for field in ("bytes", "sha256"):
                    with self.subTest(section=section, name=name, field=field):
                        manifest = copy.deepcopy(baseline)
                        value = manifest[section][name][field]
                        manifest[section][name][field] = value + 1 if field == "bytes" else "0" * 64
                        (self.work / "object-hashes.json").write_bytes(self.C.retained_json(manifest))
                        with self.assertRaisesRegex(RuntimeError, "exact retained evidence manifest"):
                            self.verify()

    def test_each_required_file_missing(self):
        for name in FILES:
            with self.subTest(name=name):
                self.bundle()
                (self.work / name).unlink()
                with self.assertRaises(FileNotFoundError):
                    self.verify()

    def test_each_required_file_corrupted(self):
        for name in FILES:
            with self.subTest(name=name):
                leaves = self.bundle()
                data = leaves[name]
                # Empty accepted stderr has no byte to flip; append one byte.
                changed = bytes([data[0] ^ 1]) + data[1:] if data else b"x"
                (self.work / name).write_bytes(changed)
                with self.assertRaises((RuntimeError, ValueError)):
                    self.verify()

    def test_each_required_file_symlink(self):
        for name in FILES:
            with self.subTest(name=name):
                self.bundle()
                target = self.root / "alias-target"
                path = self.work / name
                path.rename(target)
                path.symlink_to(target)
                self.check_scratch()
                with self.assertRaisesRegex(RuntimeError, "input alias"):
                    self.verify()
                path.unlink()
                target.unlink()

    def test_each_required_file_hardlink(self):
        for name in FILES:
            with self.subTest(name=name):
                self.bundle()
                alias = self.root / "hardlink-target"
                os.link(self.work / name, alias)
                self.check_scratch()
                with self.assertRaisesRegex(RuntimeError, "regular bounded input"):
                    self.verify()
                alias.unlink()

    def test_canonical_result_and_manifest_bytes(self):
        for name in ("result.json", "object-hashes.json"):
            for mutation in ("compact", "missing-newline", "extra-newline"):
                with self.subTest(name=name, mutation=mutation):
                    leaves = self.bundle()
                    data = leaves[name]
                    changed = (BASE.encode(BASE.SUPPORT.decode(data)) if mutation == "compact" else
                               data[:-1] if mutation == "missing-newline" else data + b"\n")
                    (self.work / name).write_bytes(changed)
                    with self.assertRaisesRegex(RuntimeError, "exact retained (result bytes|evidence manifest)"):
                        self.verify()

    def test_metadata_exact_boundary_and_one_byte_overflow(self):
        for length in (METADATA_CAP, METADATA_CAP + 1):
            with self.subTest(serialized_length=length):
                value = {"padding": ""}
                value["padding"] = "x" * (length - len(self.C.retained_json(value)))
                if length == METADATA_CAP:
                    self.assertEqual(len(self.C.retained_json(value)), length)
                else:
                    with self.assertRaisesRegex(RuntimeError, "bounded retained metadata"):
                        self.C.retained_json(value)
        result = copy.deepcopy(self.result)
        result["padding"] = ""
        result["padding"] = "x" * (METADATA_CAP - len(self.C.retained_json(result)))
        leaves = self.bundle(result)
        self.assertEqual(len(leaves["result.json"]), METADATA_CAP)
        self.assertIsNone(self.verify())
        for name in ("result.json", "object-hashes.json"):
            with self.subTest(file=name):
                self.bundle()
                path = self.work / name
                path.write_bytes(b"x" * METADATA_CAP)
                self.assertEqual(len(BASE.SUPPORT.read_regular(path, METADATA_CAP)), METADATA_CAP)
                path.write_bytes(b"x" * (METADATA_CAP + 1))
                with self.assertRaisesRegex(RuntimeError, "regular bounded input"):
                    self.verify()

    def test_audit_in_memory_boundary_empty_and_stderr(self):
        for length in (AUDIT_CAP, AUDIT_CAP + 1, 0):
            with self.subTest(audit_length=length):
                data = b"x" * length
                if length == AUDIT_CAP:
                    manifest = BASE.SUPPORT.decode(self.manifest(stdout=data))
                    self.assertEqual(manifest["files"]["audit-stdout.log"]["bytes"], AUDIT_CAP)
                else:
                    with self.assertRaisesRegex(RuntimeError, "accepted audit stream bounds"):
                        self.manifest(stdout=data)
        with self.assertRaisesRegex(RuntimeError, "accepted audit stream bounds"):
            self.manifest(stderr=b"x")

    def test_preflight_read_caps_and_oversized_stat(self):
        self.bundle()
        with mock.patch.object(self.C, "read_regular", wraps=BASE.SUPPORT.read_regular) as reader:
            self.assertIsNone(self.verify())
        self.assertEqual(reader.call_args_list,
                         [mock.call(self.work / name, cap) for name, cap in
                          zip(FILES, (AUDIT_CAP, 0, METADATA_CAP, METADATA_CAP))])
        real_fstat = os.fstat
        for name, cap in zip(FILES, (AUDIT_CAP, 0, METADATA_CAP, METADATA_CAP)):
            with self.subTest(name=name, cap=cap):
                inode = (self.work / name).stat().st_ino
                def oversized(fd):
                    info = real_fstat(fd)
                    if info.st_ino != inode:
                        return info
                    attributes = {key: getattr(info, key) for key in
                                  ("st_dev", "st_ino", "st_mode", "st_uid", "st_nlink",
                                   "st_size", "st_mtime_ns", "st_ctime_ns")}
                    attributes["st_size"] = cap + 1
                    return SimpleNamespace(**attributes)
                with mock.patch.object(BASE.SUPPORT.os, "fstat", side_effect=oversized):
                    with self.assertRaisesRegex(RuntimeError, "regular bounded input"):
                        self.verify()

    def test_deadline_before_each_preflight_read(self):
        self.bundle()
        for expired_index, name in enumerate(FILES):
            with self.subTest(before=name):
                with mock.patch.object(self.C.time, "monotonic",
                                       side_effect=[10.0] * expired_index + [DEADLINE]), \
                     mock.patch.object(self.C, "read_regular", wraps=BASE.SUPPORT.read_regular) as reader:
                    with self.assertRaisesRegex(RuntimeError, "retention preflight deadline"):
                        self.verify()
                self.assertEqual(reader.call_count, expired_index)

    def test_deadline_after_manifest_reconstruction(self):
        self.bundle()
        with mock.patch.object(self.C.time, "monotonic", side_effect=[10.0] * 4 + [DEADLINE]), \
             mock.patch.object(self.C, "retention_manifest", wraps=self.C.retention_manifest) as manifest:
            with self.assertRaisesRegex(RuntimeError, "retention preflight deadline"):
                self.verify()
        manifest.assert_called_once()

    def test_retained_metadata_creation_exclusive_and_private(self):
        for name in ("result.json", "object-hashes.json"):
            with self.subTest(name=name):
                path = self.work / name
                self.C.write_new(path, b"original\n")
                self.assertEqual(path.stat().st_mode & 0o777, 0o600)
                with self.assertRaises(FileExistsError):
                    self.C.write_new(path, b"replacement\n")
                self.assertEqual(path.read_bytes(), b"original\n")
                path.unlink()
                path.symlink_to(self.root / OBJECTS[0])
                with self.assertRaisesRegex(RuntimeError, "input alias"):
                    self.C.write_new(path, b"replacement\n")
                path.unlink()

    @contextmanager
    def simulated_main(self, fault=None, late=False, fresh_limit=None):
        """Only parent-side finalization: no real tool, distribution, or build.

        Authentication and run_lean are explicit mocks. Small synthetic objects,
        accepted fixture bytes, retained writers/readers, and final membership
        checks remain real. BASE.main's refusal patches surround this context.
        """
        directory = self.root / "simulated"
        directory.mkdir(mode=0o700)
        lean = directory / "bin/lean"
        lean.parent.mkdir(mode=0o700)
        lean.write_bytes(b"synthetic placeholder; never executed")
        lean.chmod(0o700)
        work = directory / "work"
        state = {"now": 10.0, "physical": 0, "phases": [], "auth_deadlines": []}
        real_write = self.C.write_new
        real_read = self.C.read_regular
        real_verify = self.C.verify_file
        real_members = self.C.members
        real_manifest = self.C.retention_manifest

        def run(argv, env, target_work, phase, deadline, cap):
            self.assertEqual(target_work, work)
            state["phases"].append(phase)
            if phase != "audit":
                target = Path(argv[argv.index("-o") + 1])
                real_write(target, ("synthetic " + phase).encode())
            stdout = self.stdout if phase == "audit" else b""
            record = self.record(phase, argv)
            for name, data in ((phase + "-stdout.log", stdout), (phase + "-stderr.log", b""),
                               (phase + "-execution.json", self.C.retained_json(record))):
                real_write(work / name, data)
            if phase == "audit" and late:
                state["now"] = 480.0
            return stdout, b"", record

        def read(path, cap, **kwargs):
            if Path(path) == self.C.HERE / "distribution.json":
                return b'{"files":{}}'
            return real_read(path, cap, **kwargs)

        def verify(path, expected, deadline):
            if Path(path).parent == work:
                state["auth_deadlines"].append(deadline)
                if fault == "audit-reauthentication":
                    raise RuntimeError("injected audit reauthentication")
                return real_verify(path, expected, deadline)
            if work in Path(path).parents:
                return real_verify(path, expected, deadline)
            return {"bytes": expected["bytes"], "sha256": expected["sha256"]}

        def write(path, data):
            if fault == "manifest-write" and Path(path).name == "object-hashes.json":
                raise RuntimeError("injected manifest write")
            if fault == "result-write" and Path(path).name == "result.json":
                raise RuntimeError("injected result write")
            return real_write(path, data)

        def manifest(*args):
            if fault == "manifest-construction":
                raise RuntimeError("injected manifest construction")
            return real_manifest(*args)

        def members(path, cap):
            found = real_members(path, cap)
            if fault == "final-membership" and Path(path) == work and "result.json" in found:
                return found | {"unexpected"}
            return found

        def guards(path, pid=None):
            state["physical"] += 1
            if state["physical"] == 3:
                if fault == "final-physical":
                    raise RuntimeError("injected final physical guard")
                if fault == "final-deadline":
                    state["now"] = 490.0 if late else 40.0

        try:
            with ExitStack() as stack:
                patches = ((self.C.sys, "argv", ["check.py", "--lean", str(lean), "--work", str(work)]),
                           (self.C.sys, "platform", "linux"),
                           (self.C, "FRESH_BYTES", self.C.FRESH_BYTES if fresh_limit is None else fresh_limit))
                for target, name, value in patches:
                    stack.enter_context(mock.patch.object(target, name, value))
                stack.enter_context(mock.patch.object(self.C.platform, "machine", return_value="x86_64"))
                stack.enter_context(mock.patch.object(self.C.signal, "signal"))
                stack.enter_context(mock.patch.object(self.C.os, "umask"))
                stack.enter_context(mock.patch.object(self.C.os, "statvfs", return_value=
                                                       SimpleNamespace(f_bavail=2 * 1024**3, f_frsize=1)))
                stack.enter_context(mock.patch.object(self.C.time, "monotonic", side_effect=lambda: state["now"]))
                stack.enter_context(mock.patch.object(self.C, "load_contract", return_value=self.contract))
                stack.enter_context(mock.patch.object(self.C, "verify_distribution"))
                stack.enter_context(mock.patch.object(self.C, "diagnostics",
                                                       side_effect=lambda out, err, phase, *args:
                                                       self.summary if phase == "audit" else None))
                for name, function in (("run_lean", run), ("read_regular", read), ("verify_file", verify),
                                       ("write_new", write), ("retention_manifest", manifest),
                                       ("members", members), ("physical_guards", guards)):
                    stack.enter_context(mock.patch.object(self.C, name, side_effect=function))
                output = stack.enter_context(mock.patch("builtins.print"))
                yield work, state, output
            self.check_scratch()
        finally:
            shutil.rmtree(directory)

    def test_simulated_main_success_and_original_final_deadline(self):
        for late, expected_deadline in ((False, 40.0), (True, 490.0)):
            with self.subTest(late=late):
                with self.simulated_main(late=late) as (work, state, output):
                    self.assertIsNone(self.C.main())
                    self.assertEqual(state["phases"], ["reader", "apdu", "audit"])
                    self.assertEqual(state["auth_deadlines"], [expected_deadline, expected_deadline])
                    result = BASE.SUPPORT.decode((work / "result.json").read_bytes())
                    self.assertIs(result["accepted"], True)
                    self.assertTrue((work / "object-hashes.json").is_file())
                    output.assert_called_once()
                    self.C.verify_retention(work, expected_deadline)

    def test_simulated_main_failure_and_finalization(self):
        early = ("manifest-construction", "audit-reauthentication", "manifest-write")
        failures = (("manifest-construction", "injected manifest construction"),
                    ("audit-reauthentication", "injected audit reauthentication"),
                    ("manifest-write", "injected manifest write"),
                    ("result-write", "injected result write"),
                    ("final-membership", "exact retained output membership"),
                    ("final-physical", "injected final physical guard"),
                    ("final-deadline", "retention within original final deadline"))
        for fault, message in failures:
            with self.subTest(fault=fault):
                with self.simulated_main(fault=fault) as (work, state, output):
                    with self.assertRaisesRegex(RuntimeError, message):
                        self.C.main()
                    if fault in early:
                        result = BASE.SUPPORT.decode((work / "result.json").read_bytes())
                        self.assertIs(result["accepted"], False)
                        self.assertIn("error", result)
                        self.assertFalse((work / "object-hashes.json").exists())
                        output.assert_called_once()
                        self.assertIs(json.loads(output.call_args.args[0])["accepted"], False)
                    elif fault == "result-write":
                        self.assertFalse((work / "result.json").exists())
                        output.assert_not_called()
                    else:
                        # A late failure can leave accepted=true bytes, but it raises
                        # and cannot return successfully or print a success summary.
                        result = BASE.SUPPORT.decode((work / "result.json").read_bytes())
                        self.assertIs(result["accepted"], True)
                        output.assert_not_called()

    def test_simulated_main_metadata_reserve_boundary(self):
        self.assertEqual(self.C.FRESH_BYTES, 64 * 1024**2)
        with self.simulated_main() as (work, state, output):
            self.C.main()
            retained = sum((work / (phase + suffix)).stat().st_size
                           for phase in ("reader", "apdu", "audit")
                           for suffix in ("-stdout.log", "-stderr.log", "-execution.json"))
            result = BASE.SUPPORT.decode((work / "result.json").read_bytes())
            retained += sum(receipt["bytes"] for receipt in result["objects"].values())
        for extra in (0, -1):
            with self.subTest(reserve_slack=extra):
                with self.simulated_main(fresh_limit=retained + 65536 + extra) as (work, state, output):
                    if extra == 0:
                        self.assertIsNone(self.C.main())
                    else:
                        with self.assertRaisesRegex(RuntimeError, "fresh output/whole deadline bound"):
                            self.C.main()
                        result = BASE.SUPPORT.decode((work / "result.json").read_bytes())
                        self.assertIs(result["accepted"], False)
                        self.assertFalse((work / "object-hashes.json").exists())


if __name__ == "__main__":
    BASE.main()
