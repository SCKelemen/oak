import unittest

import run


class TableViewBenchmarkTests(unittest.TestCase):
    def test_fixture_uses_exact_table_and_function(self):
        source = "ignored\npub grapheme_table: table\npub grapheme_class: body\n// grapheme_gcb: ignored"
        self.assertEqual(run.fixture(source), "pub grapheme_table: table\npub grapheme_class: body\n\nmain: (): i32 = 0\n")
        with self.assertRaises(ValueError):
            run.fixture("no fixture")

    def test_selects_last_body_and_requires_proof(self):
        text = "grapheme_class = {\nold\n}\ngrapheme_class = {\nnew\n}\n"
        trusted = text + "native backend: asm unit grapheme_class: not verified\n"
        self.assertIn("new", run.selected(trusted)["assembly"])
        with self.assertRaises(ValueError):
            run.selected(trusted, True)
        with self.assertRaises(ValueError):
            run.selected(text, True)
        self.assertIn("new", run.selected(text + "native backend: asm unit grapheme_class: proven equal to its Oak body\n", True)["assembly"])

    def test_rejects_invalid_samples_and_disagreement(self):
        good = {"elapsed_ns": 10, "checksum": "0000000000000042"}
        self.assertEqual(run.accept(good, None), good["checksum"])
        for row in ({}, dict(good, elapsed_ns=0), dict(good, elapsed_ns=True), dict(good, checksum="bad")):
            with self.assertRaises(ValueError):
                run.accept(row, None)
        with self.assertRaises(ValueError):
            run.accept(good, "0000000000000000")


if __name__ == "__main__":
    unittest.main()
