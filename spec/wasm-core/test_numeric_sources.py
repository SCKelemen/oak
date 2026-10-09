#!/usr/bin/env python3
"""Local-only tests of pinned original bytes and fail-closed preparation.

Prepare the originals first with numeric_sources.py --fetch. Tests copy those
bytes into temporary directories; all HTTP is mocked and no network is used.
Run with python3 -B spec/wasm-core/test_numeric_sources.py [--source-dir DIR].
"""

import argparse
import io
import json
import os
import tempfile
import unittest
from pathlib import Path
from unittest import mock

import numeric_sources as gate


TEST_SOURCE_DIR = None


class NumericSourcesTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.sources = gate.load_manifest()
        cls.original_paths = gate.verify_sources(TEST_SOURCE_DIR)
        cls.originals = {path.name: path.read_bytes() for path in cls.original_paths}

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="oak-numeric-source-tests-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.source_dir = self.root / "upstream"
        self.source_dir.mkdir()
        for name, data in self.originals.items():
            (self.source_dir / name).write_bytes(data)
        self.no_network = mock.patch.object(
            gate, "urlopen", side_effect=AssertionError("Self-tests must not use the network"))
        self.http = self.no_network.start()
        self.addCleanup(self.no_network.stop)

    def write_manifest(self, change):
        data = json.loads(gate.DEFAULT_MANIFEST.read_text(encoding="utf-8"))
        change(data)
        path = self.root / "manifest.json"
        path.write_text(json.dumps(data), encoding="utf-8")
        return path

    def clear_sources(self):
        for path in self.source_dir.iterdir():
            path.unlink()

    def mock_downloads(self, corrupt=None):
        bodies = {source.raw_url: self.originals[source.file] for source in self.sources}
        if corrupt:
            bodies[corrupt] = b"corrupt"
        self.http.side_effect = lambda request, timeout: io.BytesIO(bodies[request.full_url])

    def test_successful_current_originals(self):
        self.assertEqual(tuple(path.name for path in gate.verify_sources(self.source_dir)),
                         gate.SOURCE_NAMES)
        self.http.assert_not_called()

    def test_same_length_mutation_rejected(self):
        path = self.source_dir / gate.SOURCE_NAMES[-1]
        data = bytearray(path.read_bytes())
        data[-2] ^= 1
        path.write_bytes(data)
        with self.assertRaisesRegex(gate.SourceError, "SHA-256 mismatch"):
            gate.verify_sources(self.source_dir)

    def test_wrong_length_rejected(self):
        path = self.source_dir / gate.SOURCE_NAMES[0]
        path.write_bytes(path.read_bytes() + b"\n")
        with self.assertRaisesRegex(gate.SourceError, "Byte length mismatch"):
            gate.verify_sources(self.source_dir)

    def test_missing_source_rejected_without_fetch(self):
        (self.source_dir / gate.SOURCE_NAMES[1]).unlink()
        with self.assertRaisesRegex(gate.SourceError, "Missing numeric source files"):
            gate.verify_sources(self.source_dir)
        self.http.assert_not_called()

    def test_absent_directory_rejected_without_creating_it(self):
        absent = self.root / "absent"
        with self.assertRaisesRegex(gate.SourceError, "Missing numeric source files"):
            gate.verify_sources(absent)
        self.assertFalse(absent.exists())
        self.http.assert_not_called()

    def test_extra_source_rejected(self):
        (self.source_dir / "unexpected.spectec").write_bytes(b"extra")
        with self.assertRaisesRegex(gate.SourceError, "Extra numeric source files"):
            gate.verify_sources(self.source_dir)

    def test_source_symlink_rejected(self):
        path = self.source_dir / gate.SOURCE_NAMES[0]
        saved = self.root / "saved.spectec"
        path.rename(saved)
        path.symlink_to(saved)
        with self.assertRaisesRegex(gate.SourceError, "non-regular numeric source"):
            gate.verify_sources(self.source_dir)

    def test_missing_extra_and_duplicate_manifest_entries_rejected(self):
        changes = (
            lambda data: data["sources"].pop(),
            lambda data: data["sources"].append(dict(data["sources"][0])),
            lambda data: data["sources"].__setitem__(1, dict(data["sources"][0])),
        )
        for change in changes:
            with self.subTest(change=change):
                manifest = self.write_manifest(change)
                with self.assertRaises(gate.SourceError):
                    gate.verify_sources(self.source_dir, manifest_path=manifest)

    def test_manifest_unpinned_url_or_extra_field_rejected(self):
        changes = (
            lambda data: data["sources"][0].update(raw_url="https://example.com/source"),
            lambda data: data["sources"][0].update(extra="unexpected"),
            lambda data: data["sources"][0].pop("sha256"),
            lambda data: data.update(commit="0" * 40),
        )
        for change in changes:
            with self.subTest(change=change):
                with self.assertRaises(gate.SourceError):
                    gate.load_manifest(self.write_manifest(change))

    def test_duplicate_json_key_rejected(self):
        path = self.root / "manifest.json"
        path.write_text('{"sources": [], "sources": []}', encoding="utf-8")
        with self.assertRaisesRegex(gate.SourceError, "Duplicate manifest key"):
            gate.load_manifest(path)

    def test_git_blob_digest_independently_checked(self):
        manifest = self.write_manifest(
            lambda data: data["sources"][0].update(git_blob_sha1="0" * 40))
        with self.assertRaisesRegex(gate.SourceError, "Git blob SHA-1 mismatch"):
            gate.verify_sources(self.source_dir, manifest_path=manifest)

    def test_environment_and_explicit_directory_selection(self):
        with mock.patch.dict(os.environ, {"OAK_WASM_NUMERIC_SOURCES": str(self.source_dir)}):
            self.assertEqual(gate.source_directory(), self.source_dir)
            self.assertEqual(len(gate.verify_sources()), len(gate.SOURCE_NAMES))
            self.assertEqual(gate.source_directory(self.root), self.root)

    def test_fetch_only_missing_sources(self):
        missing = self.sources[-1]
        (self.source_dir / missing.file).unlink()
        self.mock_downloads()
        gate.prepare_sources(self.source_dir, fetch=True)
        self.assertEqual(self.http.call_count, 1)
        self.assertEqual(self.http.call_args.args[0].full_url, missing.raw_url)
        self.assertEqual((self.source_dir / missing.file).read_bytes(),
                         self.originals[missing.file])
        self.assertEqual(sorted(path.name for path in self.source_dir.iterdir()),
                         list(gate.SOURCE_NAMES))

    def test_fetch_preserves_bad_existing_file_and_never_downloads(self):
        path = self.source_dir / gate.SOURCE_NAMES[0]
        path.write_bytes(b"wrong existing bytes")
        (self.source_dir / gate.SOURCE_NAMES[-1]).unlink()
        with self.assertRaises(gate.SourceError):
            gate.prepare_sources(self.source_dir, fetch=True)
        self.assertEqual(path.read_bytes(), b"wrong existing bytes")
        self.http.assert_not_called()

    def test_bad_fetch_publishes_nothing_and_cleans_temporary_files(self):
        self.clear_sources()
        self.mock_downloads(corrupt=self.sources[-1].raw_url)
        with self.assertRaises(gate.SourceError):
            gate.prepare_sources(self.source_dir, fetch=True)
        self.assertEqual(list(self.source_dir.iterdir()), [])

    def test_all_missing_files_fetch_successfully(self):
        self.clear_sources()
        self.mock_downloads()
        self.assertEqual(len(gate.prepare_sources(self.source_dir, fetch=True)),
                         len(gate.SOURCE_NAMES))
        self.assertEqual(self.http.call_count, len(gate.SOURCE_NAMES))
        self.assertEqual(sorted(path.name for path in self.source_dir.iterdir()),
                         list(gate.SOURCE_NAMES))

    def test_fetch_rejects_concurrent_bad_destination_without_overwriting(self):
        source = self.sources[-1]
        target = self.source_dir / source.file
        target.unlink()
        self.mock_downloads()

        def concurrent_create(temporary, destination):
            destination.write_bytes(b"concurrent wrong bytes")
            raise FileExistsError(destination)

        with mock.patch.object(gate.os, "link", side_effect=concurrent_create):
            with self.assertRaises(gate.SourceError):
                gate.prepare_sources(self.source_dir, fetch=True)
        self.assertEqual(target.read_bytes(), b"concurrent wrong bytes")
        self.assertEqual(sorted(path.name for path in self.source_dir.iterdir()),
                         list(gate.SOURCE_NAMES))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(add_help=False)
    parser.add_argument("--source-dir", type=Path)
    args, remaining = parser.parse_known_args()
    TEST_SOURCE_DIR = args.source_dir
    unittest.main(argv=[__file__, *remaining])
