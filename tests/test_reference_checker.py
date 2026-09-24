import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import reference_check as rc


class ReferenceCheckerTests(unittest.TestCase):
    def test_known_exception_m3(self):
        self.assertEqual(rc.parity_digit_sums(6, 2), (1, 1))
        self.assertEqual(rc.actual_valuation(6, 3, 2), 2)
        self.assertEqual(rc.predicted_valuation(6, 3, 2), 2)

    def test_known_exception_m4(self):
        self.assertEqual(rc.parity_digit_sums(28, 3), (1, 1))
        self.assertEqual(rc.actual_valuation(28, 4, 3), 2)
        self.assertEqual(rc.predicted_valuation(28, 4, 3), 2)

    def test_repaired_uniform_witness(self):
        N, m, p = 21, 3, 2
        t, s, k = rc.edge_uniform_witness(N, m, p)
        self.assertEqual((t, s, k), (4, 2, 12))
        self.assertEqual(k % m, 0)
        self.assertEqual(rc.borrow_count(N, k, p), 1)
        self.assertEqual(rc.vp(__import__("math").comb(N, k), p), 1)

    def test_small_sweep(self):
        checked, failures, edge_checked, edge_failures = rc.sweep(10, 180, 31)
        self.assertGreater(checked, 0)
        self.assertGreater(edge_checked, 0)
        self.assertEqual(failures, [])
        self.assertEqual(edge_failures, [])


if __name__ == "__main__":
    unittest.main()
