"""Experiment 10: literal completed range versus its periodic projection.

Paper I, eq. (28), Proposition 13 and Section 6.  The paper proves
Ran X_L(1/2) = {f in H^1(0,L): f(L)=0} and Pi_N Ran X_L(1/2) = E_N.  Here we
visualize the second statement using terminal-zero tapered Fourier modes.
The first explains why the periodic ground state itself is never in the range:
a periodic Fourier polynomial has f(L) = f(0), and xi_N(0) = 1.
"""

import math

import matplotlib.pyplot as plt
import numpy as np

from common import fourier_series_values, ground_state_data
import presentation as ui


ui.use_style()
ui.banner(
    10,
    "The completed range versus its periodic projection",
    status=ui.THEOREM,
    reference="Paper I, eq. (28), Proposition 13, Section 6",
    claim=(
        "The completed range consists of H^1 functions with f(L) = 0, so it "
        "misses the endpoint-bright ground state, yet its orthogonal projection "
        "onto the periodic Fourier section E_N is all of E_N."
    ),
)

x = 2.0
N = 4
L = math.log(x)
indices = np.arange(-N, N + 1)
omegas = 2.0 * math.pi * indices / L

t = np.linspace(0.0, L, 6000)


def terminal_taper(t_values, width):
    """Equal to one away from L and smoothly decreases to zero at L."""

    chi = np.ones_like(t_values)
    start = L - width
    mask = t_values > start
    phase = (t_values[mask] - start) / width
    chi[mask] = 0.5 * (1.0 + np.cos(math.pi * phase))
    return chi


width = 0.18 * L
chi = terminal_taper(t, width)

# Column j is Pi_N [chi(t) U_j(t)] in the U_k basis.
projection_matrix = np.zeros((len(indices), len(indices)), dtype=complex)
for column, j in enumerate(indices):
    U_j = np.exp(1j * (2.0 * math.pi * j / L) * t) / math.sqrt(L)
    f_j = chi * U_j

    for row, k in enumerate(indices):
        U_k = np.exp(1j * (2.0 * math.pi * k / L) * t) / math.sqrt(L)
        projection_matrix[row, column] = np.trapezoid(np.conjugate(U_k) * f_j, t)

singular_values = np.linalg.svd(projection_matrix, compute_uv=False)
print(f"smallest singular value of projected terminal-zero family = {singular_values[-1]:.6e}")
print(f"numerical rank = {np.linalg.matrix_rank(projection_matrix)} of {len(indices)}")

# Compare with the selected periodic ground state, which is boundary-bright.
data = ground_state_data(x, N, gamma_terms=6000)
ground_coefficients = data["ground_coefficients"]
ground = fourier_series_values(ground_coefficients, data["indices"], t, L)
print(f"ground endpoint xi_N(L) = {ground[-1]:.8e}")

rank = np.linalg.matrix_rank(projection_matrix)
ui.reading(
    f"Tapering each Fourier mode to zero at L puts it in the completed range.  "
    f"Projected back onto E_N, the nine tapered modes have rank {rank} with "
    f"smallest singular value {singular_values[-1]:.3f}, so they span E_N.  The "
    f"ground state itself has xi_N(L) = {ground[-1].real:.4f} and so is not in "
    "the range: projection recovers E_N, but not by containing it.",
    figures=(
        "experiment_10_terminal_taper.svg",
        "experiment_10_projection_singular_values.svg",
        "experiment_10_range_vs_periodic_ground.svg",
    ),
)

source = f"Paper I, eq. (28), Proposition 13, Section 6  ·  x = {x:g}, N = {N}  ·  " + ui.THEOREM

# -----------------------------------------------------------------------------
# Figure 1: the taper.
# -----------------------------------------------------------------------------

fig = plt.figure(figsize=(8.0, 3.2))
ax = fig.add_subplot()
ax.axvspan(L - width, L, color=ui.WASH, linewidth=0.0, zorder=0)
ax.plot(t, chi, color=ui.BLUE)
ax.plot([L], [0.0], marker="o", color=ui.BLUE, zorder=4, **ui.marker_ring())
ui.label_end(ax, L, 0.0, r"$\chi(L) = 0$", dx=-9, dy=8, ha="right")
ui.note(ax, L - width / 2.0, 1.08, "taper width 0.18 L", ha="center", va="bottom")
ax.set_xlim(0.0, L + 0.01)
ax.set_ylim(-0.08, 1.25)
ax.set_xlabel(r"$t$")
ax.set_ylabel(r"$\chi(t)$")
ui.save(
    fig,
    "experiment_10_terminal_taper.svg",
    title="A smooth taper to zero at the terminal endpoint",
    subtitle=(
        r"Multiplying any Fourier mode by $\chi$ lands in the completed range, "
        r"$\mathrm{Ran}\,X_L(\frac{1}{2}) = \{f \in H^1(0, L) : f(L) = 0\}$ (eq. 28)."
    ),
    source=source,
)

# -----------------------------------------------------------------------------
# Figure 2: singular values of the projected family.
# -----------------------------------------------------------------------------

fig = plt.figure(figsize=(8.0, 3.4))
ax = fig.add_subplot()
order = np.arange(len(singular_values))
ax.axhline(0.0, color=ui.AXIS, lw=0.9)
ui.lollipop(ax, order, singular_values, ui.BLUE)
ui.label_end(ax, order[-1], singular_values[-1], rf"$\sigma_{{\min}} = {singular_values[-1]:.3f}$", dx=0, dy=12, ha="center")
ax.set_xticks(order)
ax.set_ylim(-0.05, 1.12 * singular_values[0])
ax.set_xlabel("singular-value index")
ax.set_ylabel("singular value")
ui.save(
    fig,
    "experiment_10_projection_singular_values.svg",
    title="The projected terminal-zero modes span the whole Fourier section",
    subtitle=(
        rf"$\Pi_N(\chi U_j)$, $|j| \leq {N}$: every singular value is bounded away from zero "
        rf"(rank {rank} of {len(indices)}), so $\Pi_N\,\mathrm{{Ran}}\,X_L(\frac{{1}}{{2}}) = E_N$."
    ),
    source=source,
)

# -----------------------------------------------------------------------------
# Figure 3: the periodic ground state against its tapered copy.
# -----------------------------------------------------------------------------

fig = plt.figure(figsize=(8.0, 3.8))
ax = fig.add_subplot()
ax.axvspan(L - width, L, color=ui.WASH, linewidth=0.0, zorder=0)
ax.plot(t, np.real(ground), color=ui.BLUE, label=r"periodic ground $\xi_N$ (in $E_N$)")
ax.plot(t, np.real(chi * ground), color=ui.ORANGE, label=r"tapered $\chi\,\xi_N$ (in the range)")
ax.plot([L], [np.real(ground[-1])], marker="o", color=ui.BLUE, zorder=4, **ui.marker_ring())
ax.plot([L], [0.0], marker="o", color=ui.ORANGE, zorder=4, **ui.marker_ring())
ui.label_end(ax, L, np.real(ground[-1]), r"$\xi_N(L) = 1$", dx=6, dy=14, ha="center")
ui.label_end(ax, L, 0.0, r"$\chi\xi_N(L) = 0$", dx=-10, dy=-11, ha="right")
ax.axhline(0.0, color=ui.AXIS, lw=0.9)
ax.set_xlim(0.0, L + 0.02)
ax.set_ylim(-1.6, 1.08 * np.max(np.real(ground)))
ax.set_xlabel(r"$t$")
ax.set_ylabel("value")
ax.legend(loc="upper left")
ui.save(
    fig,
    "experiment_10_range_vs_periodic_ground.svg",
    title="The range and the periodic ground disagree at the terminal endpoint",
    subtitle=(
        r"$\mathrm{Ran}\,X_L(\frac{1}{2}) \cap E_N = \ker \mathrm{ev}_0$ (eq. 119): periodic polynomials have $f(L) = f(0)$,"
        "\n"
        r"and the selected ground has $\xi_N(0) = 1$, so it lies outside the range while its taper lies inside."
    ),
    source=source,
)
