import unittest

from run import accept_sample, observation_index, selected_bodies


class BenchmarkTests(unittest.TestCase):
    def test_interleaves_every_variant(self):
        for round_ in range(9):
            self.assertEqual({observation_index(round_, offset, 8) for offset in range(8)}, set(range(8)))
            self.assertEqual(observation_index(round_, 0, 8), round_ % 8)

    def test_rejects_bad_samples(self):
        good = {"elapsed_ns": 10, "checksum": "000000000000002a"}
        self.assertEqual(accept_sample(good, None), good["checksum"])
        for row in ({}, dict(good, elapsed_ns=0), dict(good, elapsed_ns=True), dict(good, checksum="wrong"), dict(good, checksum="000000000000002b")):
            with self.assertRaises(ValueError):
                accept_sample(row, good["checksum"])

    def test_requires_proven_selected_bodies(self):
        with self.assertRaises(ValueError):
            selected_bodies("asm unit sum32: witness-checked")

    def test_last_dump_is_selected(self):
        text = "sum32 = {\n  frame 999\n  ret\n}\n"
        for name in ("sum32", "sum64"):
            text += (f"{name} = {{\nloop_1:\n  add x10, x0, w3, uxtw #2\n"
                     "  ldr q16, [x10]\n  b.lo loop_1\ndone_2:\n  ret\n}\n"
                     f"asm unit {name}: proven equal to its Oak body\n")
        bodies = selected_bodies(text)
        self.assertEqual(bodies["sum32"]["frame_bytes"], 0)
        self.assertEqual(bodies["sum32"]["main_loop_instructions"], 3)
        self.assertEqual(bodies["sum64"]["main_loop_addresses"], 1)


if __name__ == "__main__":
    unittest.main()
