"""Experiment 8: finite spectral selection of the least eigenline.

Paper I, Section 5 and Lemma 10.  Diagonalize the finite Weil matrix H_N.
When its least eigenvalue is simple with an eigenvector even under
t -> L - t (the full simple-even hypothesis), that eigenvector cannot vanish
at the endpoint (boundary brightness), so it has a unique normalization
xi_N(0) = 1.  This xi_N is the ground state used by the finite characteristic
in Experiment 9.

Use ordinary float64 by default.  Add ``--precision mp50``, ``mp100`` or
``mp200`` to repeat the matrix construction and Hermitian eigensolve with
mpmath.  The plots are still drawn from float conversions of the final small
vectors; extra digits are for diagnostics, not for prettier figures.
"""

import argparse
import math

import matplotlib.pyplot as plt
import numpy as np

from common import fourier_series_values, ground_state_data
from high_precision import mp_ground_state_data, mp_to_complex_array
from precision import add_precision_arguments, configure_mpmath, resolve_precision
import presentation as ui


parser = argparse.ArgumentParser(description=__doc__)
add_precision_arguments(parser)
args = parser.parse_args()
precision = resolve_precision(args)

ui.use_style()
ui.banner(
    8,
    "Selecting the ground state of the finite Weil matrix",
    status=ui.DIAGNOSTIC,
    reference="Paper I, Section 5, Lemma 10",
    claim=(
        "For x = 2, N = 4 the least eigenvalue of H_N is simple with an even "
        "eigenvector; boundary brightness makes its endpoint value nonzero, so "
        "it normalizes uniquely to xi_N(0) = 1."
    ),
)

x = 2.0
N = 4
L = math.log(x)

if precision.uses_mpmath:
    mp = configure_mpmath(precision.dps)
    data = mp_ground_state_data(x, N, dps=precision.dps)
    indices = np.array(data["indices"], dtype=int)
    eigenvalues = data["eigenvalues"]
    coefficients = mp_to_complex_array(data["ground_coefficients"])

    print(f"precision profile              = {precision.name}")
    print(f"least eigenvalue               = {mp.nstr(eigenvalues[0], 30)}")
    print(f"first spectral gap             = {mp.nstr(eigenvalues[1]-eigenvalues[0], 30)}")
    print(f"even-parity error              = {mp.nstr(data['parity_error_even'], 8)}")
    print(f"odd-parity error               = {mp.nstr(data['parity_error_odd'], 8)}")
    print(
        "endpoint before normalization  = "
        f"{mp.nstr(data['endpoint_before_normalization'], 30)}"
    )
    print(f"eigenpair residual             = {mp.nstr(data['eigenpair_residual'], 8)}")
    eigenvalues_for_plot = np.array([float(value) for value in eigenvalues])
else:
    data = ground_state_data(x, N, gamma_terms=6000)
    indices = data["indices"]
    eigenvalues = data["eigenvalues"]
    coefficients = data["ground_coefficients"]

    print("precision profile              = float64")
    print(f"least eigenvalue               = {eigenvalues[0]:.12e}")
    print(f"first spectral gap             = {eigenvalues[1]-eigenvalues[0]:.12e}")
    print(f"even-parity error              = {data['parity_error_even']:.3e}")
    print(f"odd-parity error               = {data['parity_error_odd']:.3e}")
    print(
        "endpoint before normalization  = "
        f"{data['endpoint_before_normalization']:.12e}"
    )
    eigenvalues_for_plot = eigenvalues

endpoint_after = np.sum(coefficients) / math.sqrt(L)
print(f"endpoint after normalization   = {endpoint_after:.12e}")

t = np.linspace(0.0, L, 1200)
xi = fourier_series_values(coefficients, indices, t, L)

ground_energy = float(eigenvalues_for_plot[0])
gap = float(eigenvalues_for_plot[1] - eigenvalues_for_plot[0])
parity_error = float(data["parity_error_even"])
raw_endpoint = abs(complex(data["endpoint_before_normalization"]))
ui.reading(
    f"The least eigenvalue {ground_energy:.4e} is separated from the next by "
    f"{gap:.4f}.  Its unit eigenvector is even (parity error {parity_error:.1e}; "
    "the odd-parity error of 2 just says it is not odd) and has endpoint value "
    f"{raw_endpoint:.4f}, comfortably nonzero, so dividing by it gives xi_N(0) = 1.",
    figures=(
        "experiment_08_ground_state.svg",
        "experiment_08_low_spectrum.svg",
        "experiment_08_ground_coefficients.svg",
    ),
)

source = f"Paper I, Section 5, Lemma 10  ·  x = {x:g}, N = {N}, {precision.name}  ·  " + ui.DIAGNOSTIC

# -----------------------------------------------------------------------------
# Figure 1: the endpoint-normalized ground state in physical coordinates.
# -----------------------------------------------------------------------------

fig = plt.figure(figsize=(8.0, 3.8))
ax = fig.add_subplot()
ax.axvline(L / 2.0, color=ui.AXIS, lw=0.9)
ui.note(ax, L / 2.0, np.max(np.real(xi)) * 1.02, r" axis of symmetry $t = L/2$", va="bottom")
ax.plot(t, np.real(xi), color=ui.BLUE)
ax.axhline(0.0, color=ui.AXIS, lw=0.9)
for end in (0.0, L):
    ax.plot([end], [1.0], marker="o", color=ui.BLUE, zorder=4, **ui.marker_ring())
ui.label_end(ax, 0.0, 1.0, r"$\xi_N(0) = 1$", dx=8, dy=-10)
ui.label_end(ax, L, 1.0, r"$\xi_N(L) = 1$", dx=-8, dy=-10, ha="right")
ax.set_xlim(-0.01, L + 0.01)
ax.set_xlabel(r"$t$")
ax.set_ylabel(r"$\xi_N(t)$")
ui.save(
    fig,
    "experiment_08_ground_state.svg",
    title="The selected ground state is even and bright at the boundary",
    subtitle=(
        r"Least eigenvector of $H_N$, even under $t \mapsto L - t$.  Its unit version has endpoint value "
        rf"${raw_endpoint:.4f} \neq 0$"
        "\n"
        r"(Lemma 10), so it can be normalized to $\xi_N(0) = 1$."
    ),
    source=source,
)

# -----------------------------------------------------------------------------
# Figure 2: the whole spectrum, with the selected eigenvalue marked.
# -----------------------------------------------------------------------------

count = min(12, len(eigenvalues_for_plot))
fig = plt.figure(figsize=(8.0, 3.6))
ax = fig.add_subplot()
order = np.arange(count)
ax.plot(order[1:], eigenvalues_for_plot[1:count], linestyle="none", marker="o", color=ui.MUTED,
        label="rest of the spectrum", **ui.marker_ring())
ax.plot(order[:1], eigenvalues_for_plot[:1], linestyle="none", marker="o", markersize=7.5, color=ui.BLUE,
        label=r"least eigenvalue $\varepsilon_N$", **ui.marker_ring())
ui.label_end(ax, 0.0, eigenvalues_for_plot[0], rf"$\varepsilon_N = {ui.sci(ground_energy, 2)}$", dx=9, dy=-2)
ui.label_end(ax, 1.0, eigenvalues_for_plot[1], rf"$\varepsilon_N + {gap:.4f}$", dx=9, dy=2)
ax.set_xticks(order)
ax.set_xlim(-0.5, count - 0.5)
ax.set_ylim(-0.15, 1.08 * eigenvalues_for_plot[count - 1])
ax.set_xlabel("eigenvalue index (ascending)")
ax.set_ylabel("eigenvalue")
ax.legend(loc="upper left")
ui.save(
    fig,
    "experiment_08_low_spectrum.svg",
    title="The least eigenvalue is simple and isolated",
    subtitle=(
        rf"All {len(eigenvalues_for_plot)} eigenvalues of $H_N$ ($x = {x:g}$, $N = {N}$).  "
        r"The simple-even hypothesis of Section 5 needs $\varepsilon_N$ simple;"
        "\n"
        rf"here the next eigenvalue is ${gap:.4f}$ higher."
    ),
    source=source,
)

# -----------------------------------------------------------------------------
# Figure 3: the Fourier coefficients of the ground state.
# -----------------------------------------------------------------------------

fig = plt.figure(figsize=(8.0, 3.6))
ax = fig.add_subplot()
ui.lollipop(ax, indices, np.real(coefficients), ui.BLUE)
ax.axhline(0.0, color=ui.AXIS, lw=0.9)
ax.axvline(0.0, color=ui.AXIS, lw=0.9, zorder=0.5)
ax.set_xticks(indices)
ax.set_xlabel(r"Fourier index $j$")
ax.set_ylabel(r"coefficient $\xi_{N,j}$")
ui.save(
    fig,
    "experiment_08_ground_coefficients.svg",
    title="Its Fourier coefficients are symmetric in j",
    subtitle=(
        rf"$\xi_{{N,-j}} = \xi_{{N,j}}$ to ${ui.sci(parity_error)}$: the evenness of the ground state, in Fourier coordinates."
        "\n"
        r"Experiment 9 reuses these numbers: $\Theta_N(\omega_j) = (-1)^j\,\xi_{N,j}/\sqrt{L}$ (eq. 112)."
    ),
    source=source,
)
