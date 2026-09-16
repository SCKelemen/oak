import json
import unittest
from unittest.mock import patch

import run


class SamplingTests(unittest.TestCase):
    def test_interleaves_and_rotates_implementations(self):
        calls = []
        timings = {"c": iter([30, 10, 20]), "native": iter([60, 20, 40])}

        def capture(command):
            impl = command[0]
            calls.append(command)
            return json.dumps({"impl": impl, "kernel": "blake3", "size": 1024,
                               "checksum": "abcd", "samples": [next(timings[impl])]})

        with patch.object(run, "capture", side_effect=capture):
            rows = run.sample_kernel([["c", "blake3"], ["native", "blake3"]], 1024, 5, 3)

        self.assertEqual([c[0] for c in calls], ["c", "native", "native", "c", "c", "native"])
        self.assertTrue(all(c[1:] == ["blake3", "1024", "5", "1"] for c in calls))
        self.assertEqual([r["impl"] for r in rows], ["c", "native"])
        self.assertEqual([r["samples"] for r in rows], [[30, 10, 20], [60, 20, 40]])
        self.assertEqual([r["ns_per_op_median"] for r in rows], [20, 40])

    def test_rotates_more_than_two_implementations(self):
        calls = []

        def capture(command):
            calls.append(command[0])
            return json.dumps({"impl": command[0], "kernel": "sum", "size": 1,
                               "checksum": "abcd", "samples": [1]})

        with patch.object(run, "capture", side_effect=capture):
            run.sample_kernel([[name, "sum"] for name in ["c", "native", "go"]], 1, 1, 3)
        self.assertEqual(calls, ["c", "native", "go", "native", "go", "c", "go", "c", "native"])

    def test_rejects_a_later_sample_checksum_mismatch(self):
        checksums = iter(["abcd", "abcd", "bad"])

        def capture(command):
            return json.dumps({"impl": command[0], "kernel": "blake3", "size": 1,
                               "checksum": next(checksums), "samples": [1]})

        with patch.object(run, "capture", side_effect=capture):
            with self.assertRaisesRegex(ValueError, "blake3: implementations disagree at sample 2"):
                run.sample_kernel([["c", "blake3"], ["native", "blake3"]], 1, 1, 3)


if __name__ == "__main__":
    unittest.main()
