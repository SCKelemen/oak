"""Failure controls for the bounded, equipped portable regression lane."""
import contextlib
import hashlib
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import required_c_regressions as required


class RequiredCRegressionsTests(unittest.TestCase):
    def setUp(self):
        self.fixture = required.FIXTURE.read_bytes()
        self.names = [case["name"] for case in json.loads(self.fixture)["cases"]]
        self.source = "a" * 64
        self.run_id = "b" * 64

    def receipt(self, env):
        return {
            "schema": 1, "source_sha256": env["OAK_ROR_TWIN_SOURCE"],
            "run": env["OAK_ROR_TWIN_RUN"],
            "fixture_sha256": hashlib.sha256(self.fixture).hexdigest(),
            "cases": [{"name": name} for name in self.names],
        }

    def run_lane(self, execute, digest=None):
        with patch.object(required.shutil, "which", return_value="/usr/bin/cc"), \
                patch.object(required, "source_digest", side_effect=digest, return_value=self.source), \
                patch.object(required, "run_suite", side_effect=execute) as calls, \
                contextlib.redirect_stdout(io.StringIO()):
            required.run()
        return calls

    def producer(self, suite, *, race, env):
        self.assertTrue(race)
        self.assertEqual(suite.timeout, "3m")
        self.assertEqual(env["OAK_REQUIRE_CC"], "1")
        self.assertEqual(env["OAK_REQUIRE_ROR_TWIN"], "1")
        self.assertEqual(env["GOENV"], "off")
        self.assertEqual(env["GOFLAGS"], "")
        self.assertEqual(env["GOWORK"], "off")
        path = Path(env["OAK_ROR_TWIN_RECEIPT"])
        if suite.package == "./asm":
            self.assertFalse(path.exists())
            path.write_text(json.dumps(self.receipt(env)))
        else:
            self.assertTrue(path.is_file())

    def test_required_lane_orders_all_exact_children_and_cleans_fresh_receipt(self):
        calls = self.run_lane(self.producer)
        suites = [call.args[0] for call in calls.call_args_list]
        self.assertEqual([suite.package for suite in suites], ["./asm", ".", "./compiler"])
        self.assertEqual([len(suite.tests) for suite in suites], [31, 31, 11])
        for selected in suites[:2]:
            self.assertEqual([name.split("/", 1)[1] for name in selected.tests[1:]], self.names)
        path = calls.call_args_list[0].kwargs["env"]["OAK_ROR_TWIN_RECEIPT"]
        self.assertFalse(Path(path).exists())

    def test_missing_cc_fails_before_any_go_test(self):
        with patch.object(required.shutil, "which", return_value=None), \
                patch.object(required, "run_suite") as run:
            with self.assertRaisesRegex(ValueError, "needs cc"):
                required.run()
            run.assert_not_called()

    def test_inherited_overlay_and_workspace_cannot_substitute_sources(self):
        with patch.dict(required.os.environ, GOFLAGS="-overlay=/outside/tree.json",
                        GOWORK="/outside/go.work", GOENV="/outside/go.env"):
            self.run_lane(self.producer)

    def test_missing_or_failed_producer_never_runs_consumer(self):
        for failure in (None, ValueError("producer failed")):
            calls = []

            def execute(suite, **kwargs):
                calls.append(suite.package)
                if failure is not None:
                    self.producer(suite, **kwargs)
                    raise failure

            with self.subTest(failure=failure), self.assertRaises(ValueError):
                self.run_lane(execute)
            self.assertEqual(calls, ["./asm"])

    def test_stale_substituted_incomplete_and_reordered_receipts_fail(self):
        mutations = [
            lambda receipt: receipt.update(schema=0),
            lambda receipt: receipt.update(source_sha256="c" * 64),
            lambda receipt: receipt.update(run="c" * 64),
            lambda receipt: receipt.update(fixture_sha256="c" * 64),
            lambda receipt: receipt.update(cases=receipt["cases"][:-1]),
            lambda receipt: receipt["cases"].reverse(),
        ]
        for mutate in mutations:
            calls = []

            def execute(suite, **kwargs):
                calls.append(suite.package)
                self.producer(suite, **kwargs)
                path = Path(kwargs["env"]["OAK_ROR_TWIN_RECEIPT"])
                document = json.loads(path.read_bytes())
                mutate(document)
                path.write_text(json.dumps(document))

            with self.subTest(mutate=mutate), self.assertRaises(ValueError):
                self.run_lane(execute)
            self.assertEqual(calls, ["./asm"])

    def test_source_drift_and_receipt_mutation_fail(self):
        with self.assertRaisesRegex(ValueError, "source tree changed"):
            self.run_lane(self.producer, iter([self.source, "c" * 64]))

        def execute(suite, **kwargs):
            self.producer(suite, **kwargs)
            if suite.package == ".":
                Path(kwargs["env"]["OAK_ROR_TWIN_RECEIPT"]).write_text("[]")

        with self.assertRaisesRegex(ValueError, "changed during consumption"):
            self.run_lane(execute)

    def test_digest_covers_all_file_bytes_and_paths(self):
        paths = ["compiler/a.go", "codegen/b.go", "asm/rotate_twin_fixture_test.go",
                 "solver.oak", "testdata/ror_consistency.json", ".github/workflows/ci.yml"]
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for name in paths:
                path = root / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(b"before")
            with patch.object(required, "ROOT", root), patch.object(
                    required.subprocess, "check_output", return_value=b"\0".join(name.encode() for name in paths)) as git:
                original = required.source_digest()
                self.assertEqual(git.call_args.args[0], ["git", "ls-files", "--cached", "--others", "--exclude-standard", "-z"])
                for name in paths:
                    (root / name).write_bytes(b"after")
                    self.assertNotEqual(required.source_digest(), original, name)
                    (root / name).write_bytes(b"before")

    def test_required_step_stays_in_packages_lane_with_existing_race_suite(self):
        source = (required.ROOT / ".github/workflows/ci.yml").read_text()
        self.assertEqual(source.count("python3 .github/scripts/required_c_regressions.py"), 1)
        self.assertIn("if: matrix.shard == 'packages'\n      timeout-minutes: 10", source)
        self.assertIn("packages) go test -v -race -timeout 45m", source)


if __name__ == "__main__":
    unittest.main()
