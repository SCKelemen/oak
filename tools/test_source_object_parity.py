"""Fail-closed controls for the source/full-artifact proof evidence gate."""
import unittest

import source_object_parity as check


class SourceObjectControls(unittest.TestCase):
    def test_pinned_current_source_and_queries(self):
        self.assertEqual(len(check.MODEL), 7)
        self.assertEqual(len(check.FIXTURES), 19)
        self.assertEqual(len(check.EXPECTED), 26)
        check.validate_inventories()

    def test_refuse_changed_missing_or_duplicate_inventory(self):
        for expected in (check.MODEL, check.FIXTURES, check.EXPECTED):
            check.require_inventory("control", expected, expected)
            changed = ("unexpected.theorem",) + expected[1:]
            for actual in ((), expected[:-1], expected + expected[:1],
                           tuple(reversed(expected)), changed):
                with self.subTest(actual=actual), self.assertRaises(SystemExit):
                    check.require_inventory("control", actual, expected)
        with self.assertRaises(SystemExit):
            check.require_inventory("control", (), ())

    def test_exact_multiline_reports(self):
        output = "".join("'" + name + "' depends on axioms: [propext,\n Quot.sound]\n"
                         for name in check.EXPECTED)
        check.native.audit_reports(output, check.EXPECTED)
        malformed = ("", output.replace("Quot.sound", "sorryAx", 1),
                     output + output, output + "unexpected output\n",
                     output.replace(check.EXPECTED[0], "unexpected.theorem", 1),
                     output[output.index("\n Quot.sound]") + len("\n Quot.sound]\n"):])
        for actual in malformed:
            with self.subTest(actual=actual), self.assertRaises(SystemExit):
                check.native.audit_reports(actual, check.EXPECTED)


if __name__ == "__main__":
    unittest.main()
