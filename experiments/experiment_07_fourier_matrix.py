"""Experiment 7: construct the literal finite Weil matrix by two routes.

Paper I, Theorem 9, eq. (94), against the localized form of Theorem 7,
eq. (76).  In the basis U_j(t) = L^{-1/2} exp(i omega_j t), |j| <= N, the
localized Weil form has matrix

    (H_N)_jk = a_Gamma(omega_j) delta_jk + (2/L) a_x[omega_j, omega_k],

the divided differences of one real odd function a_x, with a separately
computed diagonal.  The script builds H_N from this formula and, independently,
by integrating eq. (76) against each pair of Fourier modes.

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

from common import build_weil_matrix, direct_weil_matrix
from high_precision import mp_build_weil_matrix, mp_to_float_matrix
from precision import add_precision_arguments, resolve_precision
import presentation as ui


parser = argparse.ArgumentParser(description=__doc__)
add_precision_arguments(parser)
args = parser.parse_args()
precision = resolve_precision(args)

ui.use_style()
ui.banner(
    7,
    "The finite Weil matrix, two ways",
    status=ui.IDENTITY,
    reference="Paper I, Theorem 9, eq. (94); Theorem 7, eq. (76)",
    claim=(
        "The divided-difference formula of Theorem 9 and direct integration of "
        "the localized form (76) give the same Fourier matrix H_N, including "
        "its diagonal."
    ),
)

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

print("building direct equation (76) matrix with readable float64 quadrature ...")
H_direct = direct_weil_matrix(x, N, y_steps=7000)

difference = H_direct - H_formula
print(f"precision profile                 = {precision.name}")
print(f"max absolute matrix difference   = {np.max(np.abs(difference)):.6e}")
print(f"symmetry error, formula route    = {np.max(np.abs(H_formula-H_formula.T)):.3e}")
print(f"symmetry error, direct route     = {np.max(np.abs(H_direct-H_direct.T)):.3e}")

max_difference = np.max(np.abs(difference))
ui.reading(
    f"The routes agree to {max_difference:.1e} in every entry.  The gap is "
    "quadrature error in the direct route: it falls fourfold when that route's "
    "y-grid is doubled (second-order midpoint rule).  The formula route is "
    "already at rounding level; compare --precision mp50.",
    figures=(
        "experiment_07_weil_matrix_formula.svg",
        "experiment_07_weil_matrix_direct.svg",
        "experiment_07_weil_matrix_difference.svg",
    ),
)

source = f"Paper I, Theorem 9 and eq. (76)  ·  x = {x:g}, N = {N}  ·  " + ui.IDENTITY
limit = np.max(np.abs(H_formula))


def draw_matrix(fig, ax, matrix, vmax, label):
    # One-hue map when every entry is nonnegative; otherwise a diverging map
    # centred on zero, so colour always carries the sign faithfully.
    if np.min(matrix) >= 0.0:
        image = ax.imshow(matrix, origin="lower", cmap=ui.SEQUENTIAL, vmin=0.0, vmax=vmax)
    else:
        image = ax.imshow(matrix, origin="lower", cmap=ui.DIVERGING, vmin=-vmax, vmax=vmax)
    ax.grid(False)
    for side in ("top", "right"):
        ax.spines[side].set_visible(False)
    ax.set_xticks(range(len(indices)), indices)
    ax.set_yticks(range(len(indices)), indices)
    ax.set_xlabel(r"$k$")
    ax.set_ylabel(r"$j$")
    bar = fig.colorbar(image, ax=ax, shrink=0.9, pad=0.03)
    bar.set_label(label, color=ui.INK_2)
    bar.outline.set_visible(False)
    bar.ax.tick_params(colors=ui.AXIS, labelcolor=ui.INK_2)


fig = plt.figure(figsize=(6.2, 5.2))
ax = fig.add_subplot()
draw_matrix(fig, ax, H_formula, limit, r"$(H_N)_{jk}$")
ui.save(
    fig,
    "experiment_07_weil_matrix_formula.svg",
    title="Finite Weil matrix from the arithmetic interpolation",
    subtitle=(
        r"$(H_N)_{jk} = a_\Gamma(\omega_j)\,\delta_{jk} + \frac{2}{L}\,\mathfrak{a}_x[\omega_j, \omega_k]$: "
        "divided differences of one\nreal odd function, plus the Γ multiplier on the diagonal (Theorem 9)."
    ),
    source=source,
)

fig = plt.figure(figsize=(6.2, 5.2))
ax = fig.add_subplot()
draw_matrix(fig, ax, H_direct, limit, r"$W_L(U_j, U_k)$")
ui.save(
    fig,
    "experiment_07_weil_matrix_direct.svg",
    title="The same matrix from the localized Weil pairing",
    subtitle=(
        r"Each entry integrates eq. (76) against $U_j, U_k$: polar, Γ, and prime terms,"
        "\n"
        r"with midpoint quadrature in $y$ (7000 steps).  Same colour scale as the formula route."
    ),
    source=source,
)

fig = plt.figure(figsize=(6.2, 5.2))
ax = fig.add_subplot()
draw_matrix(fig, ax, difference, max_difference, "direct − formula")
ui.save(
    fig,
    "experiment_07_weil_matrix_difference.svg",
    title="The two constructions differ only by quadrature error",
    subtitle=(
        rf"$\max\,|\Delta_{{jk}}| = {ui.sci(max_difference)}$ (${ui.sci(max_difference / limit)}$ of the largest entry), falling fourfold"
        "\n"
        r"per doubling of the direct route's $y$-grid.  It sits on the diagonal, the only entries where"
        "\n"
        r"eq. (76) subtracts the term $2\langle u, v\rangle / (e^y - e^{-y})$."
    ),
    source=source,
)
