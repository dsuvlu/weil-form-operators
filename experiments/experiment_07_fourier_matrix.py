"""Experiment 7: construct the literal finite Weil matrix by two routes.

Default mode is the original NumPy calculation.  With ``--precision mp50``
(or another profile), the interpolation/Theorem-9 route is recomputed with
mpmath while the direct localized-form route remains a simple float64
quadrature.  This keeps the demonstration readable: high precision is used
where cancellation is most visible, while the independent route stays easy to
inspect.
"""

import argparse

import matplotlib.pyplot as plt
import numpy as np

from common import FIGURE_DIR, build_weil_matrix, direct_weil_matrix
from high_precision import mp_build_weil_matrix, mp_to_float_matrix
from precision import add_precision_arguments, resolve_precision


parser = argparse.ArgumentParser(description=__doc__)
add_precision_arguments(parser)
args = parser.parse_args()
precision = resolve_precision(args)

x = 13.0
N = 4

print("building float64 Theorem 9 matrix ...")
H_float, indices, _ = build_weil_matrix(x, N, gamma_terms=6000)

if precision.uses_mpmath:
    print(f"building {precision.name} Theorem 9 matrix ...")
    H_mp, _, _ = mp_build_weil_matrix(x, N, dps=precision.dps)
    H_formula = mp_to_float_matrix(H_mp)
    print(
        "max |high precision - float64 formula| = "
        f"{np.max(np.abs(H_formula - H_float)):.6e}"
    )
else:
    H_formula = H_float

print("building direct equation (67) matrix with readable float64 quadrature ...")
H_direct = direct_weil_matrix(x, N, y_steps=7000)

difference = H_direct - H_formula
print(f"precision profile                 = {precision.name}")
print(f"max absolute matrix difference   = {np.max(np.abs(difference)):.6e}")
print(f"symmetry error, formula route    = {np.max(np.abs(H_formula-H_formula.T)):.3e}")
print(f"symmetry error, direct route     = {np.max(np.abs(H_direct-H_direct.T)):.3e}")

plt.figure(figsize=(6.3, 5.5))
plt.imshow(H_formula, origin="lower", aspect="auto")
plt.colorbar(label="matrix entry")
plt.xticks(range(len(indices)), indices)
plt.yticks(range(len(indices)), indices)
plt.xlabel("k")
plt.ylabel("j")
plt.title("Finite Weil matrix from the arithmetic interpolation")
plt.tight_layout()
plt.savefig(FIGURE_DIR / "experiment_07_weil_matrix_formula.svg")
plt.close()

plt.figure(figsize=(6.3, 5.5))
plt.imshow(H_direct, origin="lower", aspect="auto")
plt.colorbar(label="matrix entry")
plt.xticks(range(len(indices)), indices)
plt.yticks(range(len(indices)), indices)
plt.xlabel("k")
plt.ylabel("j")
plt.title("The same matrix from the localized Weil pairing")
plt.tight_layout()
plt.savefig(FIGURE_DIR / "experiment_07_weil_matrix_direct.svg")
plt.close()

plt.figure(figsize=(6.3, 5.5))
plt.imshow(difference, origin="lower", aspect="auto")
plt.colorbar(label="direct - formula")
plt.xticks(range(len(indices)), indices)
plt.yticks(range(len(indices)), indices)
plt.xlabel("k")
plt.ylabel("j")
plt.title("Difference between the two constructions")
plt.tight_layout()
plt.savefig(FIGURE_DIR / "experiment_07_weil_matrix_difference.svg")
plt.close()
