"""Exact root coverage, fail-closed selection, and workflow compatibility checks."""
import contextlib
import copy
import io
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import package_shards as shards


NAMES = ["TestOakCNFEmission", "TestOakCNFNodes", "TestOakSolverAgrees", "TestRest", "Example", "FuzzSeed"]
PACKAGES = [shards.ROOT_PACKAGE, shards.ROOT_PACKAGE + "/compiler", shards.ROOT_PACKAGE + "/parser"]


class PackageShardsTests(unittest.TestCase):
    def test_exact_stable_partition_and_boundaries(self):
        names = NAMES + ["TestOakCNF" + suffix for suffix in ("G", "H", "a", "_", "7", "")]
        names += ["TestOak" + family for family in ("Shell", "Lean", "Syntax", "SAT")]
        result = shards.partition_roots(names)
        self.assertEqual(result, shards.partition_roots(list(reversed(names))))
        self.assertEqual(sum(map(len, result.values())), len(names))
        self.assertIn("TestOakCNFG", result["root-cnf-a-g"])
        for suffix in ("H", "a", "_", "7", ""):
            self.assertIn("TestOakCNF" + suffix, result["root-cnf-h-z"])
        for family in ("Shell", "Lean", "Syntax"):
            self.assertIn("TestOak" + family, result["root-solver"])
        self.assertTrue({"TestOakSAT", "Example", "FuzzSeed"} <= set(result["root-rest"]))

    def test_missing_duplicate_extra_and_empty_shards_fail_closed(self):
        valid = shards.partition_roots(NAMES)
        invalid = []
        for shard in shards.ROOT_SHARDS:
            removed = copy.deepcopy(valid)
            removed[shard] = []
            invalid.append(removed)
        missing = copy.deepcopy(valid)
        del missing["root-rest"]
        invalid.append(missing)
        extra = copy.deepcopy(valid)
        extra["unexpected"] = []
        invalid.append(extra)
        for name in ("TestRest", "TestInvented"):
            extra = copy.deepcopy(valid)
            extra["root-solver"].append(name)
            invalid.append(extra)
        for partition in invalid:
            with self.subTest(partition=partition), self.assertRaises(ValueError):
                shards.check_partition(NAMES, partition)
        for names in ([], NAMES + [NAMES[0]], NAMES + ["TestParent/child"], NAMES + ["BenchmarkNotRun"], NAMES + ["Test Bad"]):
            with self.subTest(names=names), self.assertRaises(ValueError):
                shards.partition_roots(names)

    def test_regex_metacharacters_are_literal_and_root_anchored(self):
        names = ["Test[abc]", "Test.*", "Test(a|b)", "Example+", "Fuzz^$"]
        pattern = shards.run_pattern(names)
        self.assertEqual({name for name in names if re.search(pattern, name)}, set(names))
        for name in ("Testabc", "TestAnything", "OtherTest.*", "Test.*Other"):
            self.assertIsNone(re.search(pattern, name))
        self.assertNotIn("/", pattern)

    def test_live_inventory_uses_race_and_includes_fuzz_examples(self):
        output = "\n".join(NAMES + ["ok\t" + shards.ROOT_PACKAGE + "\t0.001s"]) + "\n"
        with patch.object(shards.subprocess, "check_output", return_value=output) as call:
            self.assertEqual(shards.root_inventory(), NAMES)
        self.assertEqual(call.call_args.args[0], ["go", "test", "-race", ".", "-list", "^(Test|Example|Fuzz)"])
        for output in ("", "ok\t" + shards.ROOT_PACKAGE + "\n", "TestOne\nTestOne\n", "TestOne\nunexpected output\n"):
            with self.subTest(output=output), patch.object(shards.subprocess, "check_output", return_value=output):
                with self.assertRaises(ValueError):
                    shards.root_inventory()

    def test_remaining_packages_preserve_old_set_without_root(self):
        packages = PACKAGES + [shards.ROOT_PACKAGE + "/compiler/support", shards.ROOT_PACKAGE + "/other/compiler"]
        with patch.object(shards.subprocess, "check_output", return_value="\n".join(packages)) as call:
            actual = shards.remaining_packages()
        old = {name for name in packages if not name.endswith("/compiler")}
        self.assertEqual(set(actual) | {shards.ROOT_PACKAGE}, old)
        self.assertNotIn(shards.ROOT_PACKAGE, actual)
        self.assertEqual(call.call_args.args[0], ["go", "list", "./..."])
        for packages in ([], PACKAGES[1:], [PACKAGES[0]], PACKAGES + [PACKAGES[0]], PACKAGES + ["foreign/package"]):
            with self.subTest(packages=packages), patch.object(shards.subprocess, "check_output", return_value="\n".join(packages)):
                with self.assertRaises(ValueError):
                    shards.remaining_packages()

    def test_commands_preserve_race_deadline_all_descendants_and_other_packages(self):
        for shard in (*shards.SHARDS, "--check"):
            with self.subTest(shard=shard), patch.object(shards, "root_inventory", return_value=NAMES), patch.object(shards, "remaining_packages", return_value=PACKAGES[2:]), patch.object(shards.subprocess, "run") as run, contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(shards.main([shard]), 0)
                if shard == "--check":
                    run.assert_not_called()
                    continue
                command = run.call_args.args[0]
                self.assertEqual(command[:6], ["go", "test", "-v", "-race", "-timeout", "45m"])
                self.assertTrue(run.call_args.kwargs["check"])
                if shard == "packages-rest":
                    self.assertEqual(command[6:], PACKAGES[2:])
                else:
                    self.assertEqual(command[6:8], [".", "-run"])
                    self.assertEqual(command[8], shards.run_pattern(shards.partition_roots(NAMES)[shard]))
                for forbidden in ("-short", "-fuzz", "-bench"):
                    self.assertNotIn(forbidden, command)

    def test_failure_never_starts_a_partial_suite(self):
        for error in (ValueError("empty"), OSError("cannot launch"), subprocess.CalledProcessError(1, ["go"])):
            with self.subTest(error=error), patch.object(shards, "root_inventory", side_effect=error), patch.object(shards.subprocess, "run") as run, contextlib.redirect_stderr(io.StringIO()):
                self.assertEqual(shards.main(["root-rest"]), 1)
                run.assert_not_called()
        with patch.object(shards, "root_inventory", return_value=NAMES), patch.object(shards, "remaining_packages", return_value=PACKAGES[2:]), patch.object(shards.subprocess, "run", side_effect=subprocess.CalledProcessError(2, ["go"])), contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
            self.assertEqual(shards.main(["root-rest"]), 1)

    def test_both_workflow_matrices_cover_all_shards(self):
        workflows = Path(__file__).resolve().parents[1] / "workflows"
        for filename in ("ci.yml", "stdlib.yml"):
            text = (workflows / filename).read_text()
            matrices = re.findall(r"shard: \[([^\]]+)\]", text)
            self.assertEqual(len(matrices), 1)
            actual = [name.strip() for name in matrices[0].split(",")]
            for shard in shards.SHARDS:
                self.assertEqual(actual.count(shard), 1)
            self.assertIn('python3 .github/scripts/package_shards.py "${{ matrix.shard }}"', text)
            self.assertNotIn("$(go list ./... | grep", text)
        ci = (workflows / "ci.yml").read_text()
        self.assertIn("name: Run Tests (1.27.1, packages)\n", ci)
        self.assertIn("OAK_REQUIRE_RV64_GCC: ${{ matrix.shard == 'packages-rest' && '1' || '' }}", ci)
        self.assertIn("if: matrix.shard == 'packages-rest'\n", ci)

    def test_compatibility_aggregates_reject_skips_failures_and_cancellations(self):
        workflows = Path(__file__).resolve().parents[1] / "workflows"
        cases = (("ci.yml", "packages", ["test"], ["TEST_RESULT"]),
                 ("stdlib.yml", "stdlib", ["stdlib-content", "race-tests"], ["CONTENT_RESULT", "RACE_RESULT"]))
        for filename, job, needs, variables in cases:
            text = (workflows / filename).read_text()
            block = re.search(r"(?ms)^  " + job + r":\n(.*?)(?=^  [a-z][\w-]*:|\Z)", text).group(1)
            self.assertIn("if: always()", block)
            self.assertRegex(block, r"needs: " + re.escape(needs[0] if len(needs) == 1 else "[" + ", ".join(needs) + "]"))
            command = re.search(r"run: (test .*)", block).group(1)
            env = {**os.environ, **dict.fromkeys(variables, "success")}
            self.assertEqual(subprocess.run(["sh", "-c", command], env=env).returncode, 0)
            for variable, dependency in zip(variables, needs):
                self.assertIn(variable + ": ${{ needs." + dependency + ".result }}", block)
                for outcome in ("failure", "cancelled", "skipped", ""):
                    with self.subTest(filename=filename, variable=variable, outcome=outcome):
                        self.assertNotEqual(subprocess.run(["sh", "-c", command], env={**env, variable: outcome}).returncode, 0)


@unittest.skipUnless(shutil.which("go"), "Go is required for the race-build fixture")
class GoFixtureTests(unittest.TestCase):
    def test_live_race_platform_inventory_and_all_seed_descendants(self):
        # The real root suite is expensive. This bounded fixture exercises the
        # actual Go discovery/run boundary, including build-tagged tests.
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "go.mod").write_text("module shardfixture\n\ngo 1.20\n")
            (root / "fixture_test.go").write_text('''package shardfixture
import ("fmt"; "testing")
func TestOakCNFEmission(t *testing.T) { t.Run("nested", func(t *testing.T) {}) }
func TestOakCNFNodes(t *testing.T) {}
func TestOakSolverAgrees(t *testing.T) {}
func TestRest(t *testing.T) {}
func Example() { fmt.Println("example"); /* Output: example */ }
func FuzzSeed(f *testing.F) { f.Add("seed"); f.Fuzz(func(t *testing.T, value string) {}) }
''')
            (root / "race_test.go").write_text('//go:build race\n\npackage shardfixture\nimport "testing"\nfunc TestRaceOnly(t *testing.T) {}\n')
            platform = subprocess.check_output(["go", "env", "GOOS"], text=True).strip()
            other = "darwin" if platform != "darwin" else "linux"
            for suffix, name in ((platform, "TestCurrentPlatform"), (other, "TestOtherPlatform")):
                (root / ("platform_" + suffix + "_test.go")).write_text('package shardfixture\nimport "testing"\nfunc ' + name + '(t *testing.T) {}\n')
            previous = os.getcwd()
            try:
                os.chdir(root)
                with patch.object(shards, "ROOT_PACKAGE", "shardfixture"):
                    names = shards.root_inventory()
                self.assertEqual(set(names), set(NAMES) | {"TestRaceOnly", "TestCurrentPlatform"})
                groups = shards.partition_roots(names)
                outputs = []
                for group in groups.values():
                    outputs.append(subprocess.check_output(["go", "test", "-v", "-race", "-timeout", "30s", ".", "-run", shards.run_pattern(group)], text=True))
                output = "\n".join(outputs)
                for name in ("TestOakCNFEmission/nested", "FuzzSeed/seed#0", "Example", "TestRaceOnly", "TestCurrentPlatform"):
                    self.assertEqual(output.count("--- PASS: " + name + " ("), 1, output)
                self.assertNotIn("TestOtherPlatform", output)
            finally:
                os.chdir(previous)


if __name__ == "__main__":
    unittest.main()
