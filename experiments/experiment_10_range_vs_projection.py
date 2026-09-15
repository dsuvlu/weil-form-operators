"""Experiment 10: literal completed range versus its periodic projection.

The paper proves Ran X_L(1/2) = {f in H^1(0,L): f(L)=0} and
Pi_N Ran X_L(1/2) = E_N.  Here we visualize the second statement using
terminal-zero tapered Fourier modes.
"""

import math

import matplotlib.pyplot as plt
import numpy as np

from common import FIGURE_DIR, fourier_series_values, ground_state_data


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

plt.figure(figsize=(8, 4.5))
plt.plot(t, chi)
plt.axvline(L)
plt.xlabel("t")
plt.ylabel("taper")
plt.title("A terminal-zero H1 taper used to generate the projected section")
plt.tight_layout()
plt.savefig(FIGURE_DIR / "experiment_10_terminal_taper.svg")
plt.close()

plt.figure(figsize=(8, 4.5))
plt.plot(np.arange(len(singular_values)), singular_values, marker="o")
plt.xlabel("singular-value index")
plt.ylabel("singular value")
plt.title("Projection of terminal-zero modes spans the whole finite Fourier section")
plt.tight_layout()
plt.savefig(FIGURE_DIR / "experiment_10_projection_singular_values.svg")
plt.close()

plt.figure(figsize=(8, 4.5))
plt.plot(t, np.real(ground), label="periodic selected ground")
plt.plot(t, np.real(chi * ground), label="terminal-zero tapered ground")
plt.axvline(L)
plt.xlabel("t")
plt.ylabel("value")
plt.title("Literal absorbing range and periodic selection impose different endpoints")
plt.legend()
plt.tight_layout()
plt.savefig(FIGURE_DIR / "experiment_10_range_vs_periodic_ground.svg")
plt.close()
