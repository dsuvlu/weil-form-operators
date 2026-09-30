"""Bounded regressions; invoke from any cwd, no pytest dependency."""
from pathlib import Path
import copy
import hashlib
import json
import sys
import unittest
from unittest.mock import patch

RESEARCH = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(RESEARCH / "reviewed"))
import mpmath as mp
import experiment_13_characteristic_mean as e13
import experiment_15_davenport_heilbronn_control as e15
import experiment_16_arithmetic_localization as e16
import research_diagnostics as d
import research_runtime as runtime
import weil_general as wg


class ReviewedTests(unittest.TestCase):
    def setUp(self):
        mp.mp.dps = 80

    def test_negative_energy_is_selected(self):
        original = e13.parity_blocks
        def shifted(*args):
            L, om, even, odd = original(*args)
            for matrix in (even, odd):
                for i in range(len(matrix)):
                    matrix[i][i] -= 1
            return L, om, even, odd
        baseline = e13.analyze(5, 6, 80)
        with patch.object(e13, "parity_blocks", shifted):
            result = e13.analyze(5, 6, 80)
        self.assertLess(result["E0"], 0)
        self.assertTrue(e13.passes(result))
        self.assertLess(abs(result["mu"] - baseline["mu"]), mp.mpf("1e-60"))

    def test_selection_statuses(self):
        self.assertEqual(d.selection_status(mp.mpf(1), -1, 80), "odd_ground")
        self.assertEqual(d.selection_status(0, 1, 80), "unresolved_gap")
        self.assertEqual(d.selection_status(1, mp.mpf(".999"), 80), "unresolved_parity")
        self.assertEqual(d.selection_status(1, 1, 80, endpoint=0), "unresolved_endpoint")

    def test_full_roots_and_two_attempts(self):
        result = e13.precision_stable(5, 6, max_dps=120)
        self.assertEqual(result["status"], "precision_stable")
        self.assertEqual(len(result["attempts"]), 2)
        for attempt in result["attempts"]:
            self.assertEqual(len(attempt["roots_squared"]), 6)
            self.assertEqual(set(attempt["roots_squared"][0]), {"real", "imag"})
            self.assertLess(mp.mpf(attempt["trace_mean_scaled_difference"]), mp.mpf("1e-60"))
        json.dumps(result, allow_nan=False)

    def test_failures_and_single_precision_are_retained(self):
        def broken(x, N, dps):
            raise ArithmeticError("test numerical failure")
        result = d.precision_record(5, 6, broken, [60, 90])
        self.assertEqual(result["status"], "numerical_failure")
        self.assertEqual(len(result["attempts"]), 2)
        result = d.precision_record(5, 6, e13.analyze, [78])
        self.assertEqual(result["status"], "unresolved_precision")
        with patch.object(wg, "family_matrix", side_effect=ArithmeticError("synthetic failure")):
            result = e15.spectra_point("dh", 5, [])
            self.assertEqual(result["status"], "numerical_failure")
            self.assertEqual(len(result["attempts"]), 2)
            rows = e16.surgery(5)
            self.assertEqual(len(rows), 4)
            self.assertTrue(all(len(r["attempts"]) == 2 for r in rows))

    def test_root_comparison_not_only_mean(self):
        a = e13.analyze(5, 6, 80)
        b = copy.deepcopy(a)
        b["roots_squared"][0] += 1
        self.assertFalse(d.compare_runs(a, b)["stable"])

    def test_complex_roots_fail_closed(self):
        result = d.roots_from_vector([mp.mpf(0), mp.mpf(1), mp.mpf(0)], [-1, 0, 1],
                                    mp.mpf(1), 1, 80, lambda rows, dps: [mp.mpc(1, ".001")])
        self.assertEqual(result["root_status"], "unstable_roots")
        self.assertNotIn("mu", result)
        self.assertEqual(result["roots_squared"], [mp.mpc(1, ".001")])

    def test_nonpositive_roots_fail_closed(self):
        # vector gives M = [-1], whose exact root is negative.
        result = d.roots_from_vector([mp.mpf(1), mp.mpf(-1), mp.mpf(1)], [-1, 0, 1],
                                    mp.mpf(1), 1, 80, lambda rows, dps: [mp.mpf(-1)])
        self.assertEqual(result["root_status"], "nonpositive_roots")
        self.assertNotIn("mu", result)

    def test_secular_polynomial_identity(self):
        p, weights, z = [mp.mpf(2), mp.mpf(5)], [mp.mpf(".2"), mp.mpf("-.7")], mp.mpc("1.3", ".4")
        M = mp.matrix([[(p[i] if i == j else 0) - weights[j] for j in range(2)] for i in range(2)])
        rhs = mp.fprod(z - q for q in p) * (1 + mp.fsum(weights[j] / (z - p[j]) for j in range(2)))
        self.assertLess(abs(mp.det(z * mp.eye(2) - M) - rhs), mp.mpf("1e-75"))

    def test_dh_two_precisions(self):
        result = e15.characteristic_point(20, N=4, precisions=[60, 84])
        self.assertEqual(result["status"], "precision_stable")
        self.assertEqual([r["coefficient_dps"] for r in result["attempts"]], [60, 84])

    def test_cramer_precision_independent_of_ambient(self):
        mp.mp.dps = 15
        low_ambient = e16.cramer_coeffs(1, 50, 10, dps=100)
        mp.mp.dps = 120
        high_ambient = e16.cramer_coeffs(1, 50, 10, dps=100)
        self.assertEqual(low_ambient, high_ambient)
        self.assertEqual(mp.mp.dps, 100)

    def test_general_matrix_matches_release(self):
        self.assertLess(wg.check_against_repo(20, 4, 80), mp.mpf("1e-70"))

    def test_output_paths_and_plot_isolation(self):
        frozen = runtime.EXPERIMENTS / "figures"
        before = {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in frozen.iterdir() if p.is_file()}
        import matplotlib
        matplotlib.use("Agg")
        import matplotlib.pyplot as plt
        import presentation
        import research_presentation as ui
        self.assertEqual(presentation.FIGURE_DIR, frozen)
        fig, ax = plt.subplots()
        ax.plot([0, 1], [0, 1])
        path = ui.save(fig, "test_output_isolation.svg", title="Numerical diagnostic, uncertified")
        self.assertEqual(path.parent, runtime.OUTPUT / "figures")
        after = {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in frozen.iterdir() if p.is_file()}
        self.assertEqual(before, after)
        with self.assertRaises(ValueError):
            runtime.write_json(RESEARCH / "imported" / "forbidden.json", {})

    def test_nonfinite_and_wrong_count(self):
        vector = [mp.mpf(0), mp.mpf(1), mp.mpf(0)]
        for invalid in (mp.mpf("nan"), mp.mpf("inf"), mp.mpc(1, "inf")):
            with self.assertRaises(ValueError):
                d.roots_from_vector(vector, [-1,0,1],mp.mpf(1),1,80,lambda rows,dps:[invalid])
            with self.assertRaises(ValueError):
                d.serialize(invalid,80)
        for roots in ([],[mp.mpf(1),mp.mpf(2)]):
            result=d.roots_from_vector(vector,[-1,0,1],mp.mpf(1),1,80,lambda rows,dps:roots)
            self.assertEqual(result["root_status"],"wrong_root_count")
            self.assertNotIn("mu",result)

    def test_sampled_scanner_is_not_named_complete(self):
        self.assertFalse(hasattr(e15, "online_zeros"))
        with self.assertRaises(ValueError):
            e15.sampled_online_roots(step=0)


if __name__ == "__main__":
    unittest.main(verbosity=2)
