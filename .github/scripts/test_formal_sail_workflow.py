"""The compiler-backed Sail gates must run on production compiler changes."""
from pathlib import Path
import re
import unittest


class FormalSailWorkflowTests(unittest.TestCase):
    def test_push_filter_covers_all_compiler_inputs(self):
        workflow = (Path(__file__).resolve().parents[1] / "workflows/formal-sail.yml").read_text()
        push = re.search(r"(?ms)^  push:\n(.*?)(?=^  \S|\Z)", workflow)
        self.assertIsNotNone(push, "Sail workflow must have a push trigger")
        paths = re.search(r"(?ms)^    paths:\n(.*?)(?=^    \S|\Z)", push.group(1))
        self.assertIsNotNone(paths, "Sail push trigger must declare its input paths")
        # Require the whole compiler, including source_bitwise_parity_test.go
        # and production emission code, not only the named BTI test driver.
        self.assertIn("      - 'compiler/**'\n", paths.group(1))


if __name__ == "__main__":
    unittest.main()
