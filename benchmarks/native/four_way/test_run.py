import copy
import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import run


class FourWayTests(unittest.TestCase):
    def row(self, mode="check", implementation="oak-native", width=32, elements=7):
        row = dict(mode=mode, implementation=implementation, width=width,
                   elements=elements, calls=1, checksum=run.oracle(width, elements))
        if mode == "measure":
            row["elapsed_ns"] = 100
        return row

    def accept(self, row, mode="check"):
        return run.accept_row(row, mode, "oak-native", 32, 7, 1, run.oracle(32, 7))

    def test_oracle_zero_and_first_value(self):
        self.assertEqual(run.oracle(32, 0), "0000000000000000")
        self.assertEqual(run.oracle(64, 0), "0000000000000000")
        first = (42 * 6364136223846793005 + 1) & ((1 << 64) - 1)
        self.assertEqual(run.oracle(32, 1), f"{first >> 32:016x}")
        self.assertEqual(run.oracle(64, 1), f"{first:016x}")

    def test_hashes_actual_compiler_inputs_not_standard_library(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            for name in ("go.mod", "go.sum", "compiler.go", "embed.txt", "ffi.c"):
                (directory / name).write_text(name)
            packages = [dict(Standard=True, Dir="/not-read", GoFiles=["stdlib.go"]),
                        dict(Dir=str(directory), GoFiles=["compiler.go"], EmbedFiles=["embed.txt"], CFiles=["ffi.c"])]
            with patch.object(run, "ROOT", directory), patch.object(run, "capture", return_value="\n".join(map(json.dumps, packages))):
                self.assertEqual(set(run.compiler_source_hashes()), {"go.mod", "go.sum", "compiler.go", "embed.txt", "ffi.c"})

    def test_cli_rejects_invalid_bounds_without_building(self):
        cases = [("--samples", "2"), ("--samples", "101"), ("--calls", "0"),
                 ("--calls", "1048577"), ("--elements", "0"), ("--max-load", "nan")]
        for flags in cases:
            argv = ["run.py", "prepare", "--artifacts", "/unused", *flags]
            with self.subTest(flags=flags), patch("sys.argv", argv), patch.object(run, "prepare") as prepare, \
                    patch.object(run.platform, "system", return_value="Darwin"), \
                    patch.object(run.platform, "machine", return_value="arm64"), \
                    patch("sys.stderr"), self.assertRaises(SystemExit):
                run.main()
            prepare.assert_not_called()

    def test_accepts_valid_check_and_measure(self):
        self.accept(self.row())
        self.accept(self.row("measure"), "measure")

    def test_rejects_wrong_identity_schema_checksum(self):
        good = self.row()
        bad = [None, {}, dict(good, mode="measure"), dict(good, implementation="c"),
               dict(good, width=64), dict(good, calls=True), dict(good, elements=8),
               dict(good, checksum="0000000000000000"), dict(good, elapsed_ns=0)]
        for row in bad:
            with self.subTest(row=row), self.assertRaises(ValueError):
                self.accept(row)

    def test_rejects_bad_timing(self):
        for elapsed in (0, -1, True, 1.5, float("nan"), "100"):
            with self.subTest(elapsed=elapsed), self.assertRaises(ValueError):
                self.accept(dict(self.row("measure"), elapsed_ns=elapsed), "measure")
        with self.assertRaises(ValueError):
            self.accept(self.row(), "measure")

    def test_requires_both_proven_bodies_and_selected_dump(self):
        for text in ("", "asm unit sum32: witnessed", "asm unit sum32: proven equal to its Oak body"):
            with self.assertRaises(ValueError):
                run.selected_bodies(text)
        diagnostics = "sum32 = {\n  old\n}\n"
        for name in ("sum32", "sum64"):
            diagnostics += f"{name} = {{\n  ret\n}}\nasm unit {name}: proven equal to its Oak body\n"
        self.assertNotIn("old", run.selected_bodies(diagnostics)["sum32"]["assembly"])

    def test_zig_requires_recorded_cpu_and_enabled_neon(self):
        good = "compilation: sums\n  cpu: apple_m1\n  features: +aes,+neon,-sve\n"
        self.assertEqual(run.zig_target(good)["cpu"], "apple_m1")
        for diagnostics in ("", good.replace("+neon", "-neon"), good.replace("  cpu: apple_m1\n", "")):
            with self.assertRaises(ValueError):
                run.zig_target(diagnostics)

    def manifest(self, directory):
        artifacts = {}
        for name in ("runner", "emit", "kernels.c", "kernels.o", "c.o", "rust.o", "zig.o"):
            (directory / name).write_text(name)
            artifacts[name] = run.digest(directory / name)
        return {"schema": run.SCHEMA, "state": "correctness-passed-timing-pending",
                "source_sha256": run.source_hashes(), "artifacts_sha256": artifacts,
                "native_bodies": {name: {"verdict": "proven"} for name in ("sum32", "sum64")},
                "correctness": [self.row(implementation=impl, width=width, elements=n)
                                for impl in run.IMPLEMENTATIONS for width in (32, 64) for n in run.CHECK_SIZES]}

    def test_manifest_requires_every_implementation_boundary_and_proof(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            good = self.manifest(directory)
            run.verify_artifacts(directory, good)
            missing = copy.deepcopy(good)
            missing["correctness"] = [row for row in missing["correctness"] if row["implementation"] != "zig"]
            duplicate = copy.deepcopy(good)
            duplicate["correctness"].append(duplicate["correctness"][0])
            unproven = copy.deepcopy(good)
            unproven["native_bodies"]["sum64"]["verdict"] = "witnessed"
            for report in (missing, duplicate, unproven, dict(good, source_sha256={})):
                with self.assertRaises(ValueError):
                    run.verify_artifacts(directory, report)

    def test_manifest_rejects_missing_tampered_or_escaping_artifact(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            good = self.manifest(directory)
            missing = copy.deepcopy(good)
            del missing["artifacts_sha256"]["zig.o"]
            escaping = copy.deepcopy(good)
            escaping["artifacts_sha256"]["../outside"] = "0" * 64
            for report in (missing, escaping):
                with self.assertRaises(ValueError):
                    run.verify_artifacts(directory, report)
            (directory / "runner").write_text("modified")
            with self.assertRaises(ValueError):
                run.verify_artifacts(directory, good)

    def test_quiet_guard_checks_all_load_windows_and_cpu(self):
        prepared = dict(cpu="test CPU", machine="arm64", logical_cpus=16, load_average=[0.1, 0.2, 0.3])
        with patch.object(run, "host", return_value=prepared):
            self.assertEqual(run.quiet_host(prepared, 1), prepared)
        for current in (dict(prepared, cpu=None), dict(prepared, cpu="other"),
                        dict(prepared, load_average=[0.1, 0.2, 1.1])):
            with patch.object(run, "host", return_value=current), self.assertRaises(ValueError):
                run.quiet_host(prepared, 1)

    def test_measure_requires_explicit_confirmation_before_execution(self):
        class Args:
            confirm_host_quiet = False
        with patch.object(run, "capture") as capture, self.assertRaises(ValueError):
            run.measure(Args())
        capture.assert_not_called()


if __name__ == "__main__":
    unittest.main()
