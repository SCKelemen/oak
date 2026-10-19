"""Regression controls for the fixed native-object evidence gate, not proof authority."""
import unittest
import check


class AuditControls(unittest.TestCase):
    def test_exact_wrapped_and_unwrapped_reports(self):
        for output in ["'good' does not depend on any axioms\n",
                       "'good' depends on axioms: [propext, Quot.sound]\n",
                       "'good' depends on axioms: [propext,\n Quot.sound]\n"]:
            check.audit_reports(output, ['good'])

    def test_refuse_malformed_or_incomplete_reports(self):
        good = "'good' depends on axioms: [propext,\n Quot.sound]\n"
        cases = ['', good.replace('Quot.sound', 'sorryAx'), good + good,
                 good + "'extra' does not depend on any axioms\n",
                 good[:good.rfind(']')], 'success\n', good + 'success\n',
                 good.replace('Quot.sound', 'success')]
        for output in cases:
            with self.subTest(output=output), self.assertRaises(SystemExit):
                check.audit_reports(output, ['good'])

    def test_exact_pinned_inventories(self):
        for kind, path, count in [('model', 'Oak/NativeBitwiseObject.lean', 15),
                                  ('fixtures', 'NativeBitwiseObjectFixtures.lean', 547)]:
            values = list(check.inventory((check.LEAN / path).read_text().splitlines()).values())
            self.assertEqual(len(values), count)
            check.require_inventory(kind, values)
            for altered in [[], values[:-1], values + [values[0]]]:
                with self.subTest(kind=kind), self.assertRaises(SystemExit):
                    check.require_inventory(kind, altered)


if __name__ == '__main__':
    unittest.main()
