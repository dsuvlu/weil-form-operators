"""Experiment 9: build the finite characteristic in two independent ways.

Paper I, Theorem 12, eqs. (9), (111)-(112), and Proposition 11.  With the
endpoint-normalized ground state xi_N of Experiment 8 and the rank-one
corrected derivative D'_N = D_N - (D_N xi_N) ev_0,

    Theta_N(z) = sinc(Lz/2) det(D'_N - z) / det(D_N - z)
               = (1/L) int_0^L xi_N(t) exp(-iz(t - L/2)) dt.

D'_N is self-adjoint for a positive metric, so Theta_N has only real zeros.

The entire Fourier-transform formula is the preferred numerical evaluator.
The determinant ratio is used as an independent check away from the free
Fourier lattice.  Optional mpmath precision makes the cancellation in this
identity easy to inspect without changing the plotting workflow.
"""

import argparse
import math

import matplotlib.pyplot as plt
import numpy as np

from common import (
    characteristic_from_determinants,
    characteristic_from_transform,
    corrected_derivative_matrix,
    ground_state_data,
)
from high_precision import (
    mp_characteristic_from_determinants,
    mp_characteristic_from_transform,
    mp_corrected_derivative_matrix,
    mp_ground_state_data,
    mp_to_complex_array,
)
from precision import add_precision_arguments, configure_mpmath, resolve_precision
import presentation as ui


parser = argparse.ArgumentParser(description=__doc__)
add_precision_arguments(parser)
args = parser.parse_args()
precision = resolve_precision(args)

ui.use_style()
ui.banner(
    9,
    "The finite boundary characteristic",
    status=ui.IDENTITY,
    reference="Paper I, Theorem 12, eqs. (9), (111)-(112); Proposition 11",
    claim=(
        "The determinant ratio sinc(Lz/2) det(D'_N - z)/det(D_N - z) equals the "
        "Fourier transform of the selected ground state divided by L, and all "
        "of its zeros are real."
    ),
)

x = 2.0
N = 4
L_float = math.log(x)

test_points = [
    -12.3 + 0.35j,
    -4.7 + 0.20j,
    1.1 + 0.30j,
    7.4 + 0.25j,
    14.2 + 0.40j,
]

if precision.uses_mpmath:
    mp = configure_mpmath(precision.dps)
    data_mp = mp_ground_state_data(x, N, dps=precision.dps)
    indices_mp = data_mp["indices"]
    omegas_mp = data_mp["omegas"]
    coefficients_mp = data_mp["ground_coefficients"]
    L_mp = mp.log(mp.mpf(str(x)))

    errors = []
    print(f"precision profile = {precision.name}")
    for z in test_points:
        a = mp_characteristic_from_transform(
            coefficients_mp, indices_mp, omegas_mp, L_mp, z, dps=precision.dps
        )
        b = mp_characteristic_from_determinants(
            coefficients_mp, omegas_mp, L_mp, z, dps=precision.dps
        )
        error = abs(a - b)
        errors.append(error)
        print(
            f"z={z!s:>12}: transform={mp.nstr(a, 18)}, "
            f"determinant={mp.nstr(b, 18)}, error={mp.nstr(error, 6)}"
        )
    print(f"maximum comparison error = {mp.nstr(max(errors), 8)}")

    D_prime_mp = mp_corrected_derivative_matrix(
        coefficients_mp, omegas_mp, L_mp, dps=precision.dps
    )
    roots_mp, _ = mp.eig(D_prime_mp)
    largest_imag = max(abs(mp.im(root)) for root in roots_mp)
    print(
        "largest imaginary part among eigenvalues of D'_N = "
        f"{mp.nstr(largest_imag, 8)}"
    )

    # Plotting needs only ordinary precision.
    indices = np.array(indices_mp, dtype=int)
    omegas = np.array([float(value) for value in omegas_mp])
    coefficients = mp_to_complex_array(coefficients_mp)
    roots = np.array([complex(value) for value in roots_mp])
else:
    data = ground_state_data(x, N, gamma_terms=6000)
    indices = data["indices"]
    omegas = data["omegas"]
    coefficients = data["ground_coefficients"]

    errors = []
    print("precision profile = float64")
    for z in test_points:
        a = characteristic_from_transform(coefficients, indices, omegas, L_float, z)
        b = characteristic_from_determinants(coefficients, omegas, L_float, z)
        errors.append(abs(a - b))
        print(
            f"z={z!s:>12}: transform={a:+.8e}, determinant={b:+.8e}, "
            f"error={abs(a-b):.3e}"
        )
    print(f"maximum comparison error = {max(errors):.3e}")

    D_prime = corrected_derivative_matrix(coefficients, omegas, L_float)
    roots = np.linalg.eigvals(D_prime)
    print(
        "largest imaginary part among eigenvalues of D'_N = "
        f"{np.max(np.abs(np.imag(roots))):.3e}"
    )

# D'_N xi_N = 0, so 0 is always an eigenvalue of D'_N; in the determinant
# ratio it cancels against the free lattice point omega_0 = 0.  The zeros of
# Theta_N are the remaining eigenvalues (and omega_j with |j| > N).
zeros = np.sort(np.real(roots[np.abs(roots) > 1.0e-8]))
lattice_values = np.array(
    [((-1) ** int(j)) * np.real(c) / math.sqrt(L_float) for j, c in zip(indices, coefficients)]
)

ui.reading(
    f"The two formulas agree to {float(max(errors)):.1e} at five off-axis points.  "
    f"The eigenvalues of D'_N are real to {float(np.max(np.abs(np.imag(roots)))):.1e}; "
    "apart from the eigenvalue 0, which cancels against omega_0, they are "
    f"zeros of Theta_N: +-{', +-'.join(f'{z:.2f}' for z in zeros[zeros > 0])}.  "
    "Theta_N also vanishes at the lattice points omega_j with |j| > N (eq. 112).",
    figures=(
        "experiment_09_characteristic_real_axis.svg",
        "experiment_09_characteristic_complex_plane.svg",
    ),
)

source = f"Paper I, Theorem 12 and Proposition 11  ·  x = {x:g}, N = {N}, {precision.name}  ·  " + ui.IDENTITY

# Figures deliberately use the fast entire transform evaluator.  Extra digits
# are diagnostic; a screen-resolution plot cannot display them.
z_real = np.linspace(-28.0, 28.0, 1800)
theta_real = np.array(
    [
        characteristic_from_transform(coefficients, indices, omegas, L_float, complex(z))
        for z in z_real
    ]
)

# -----------------------------------------------------------------------------
# Figure 1: Theta_N on the real axis, its zeros, and its free-lattice values.
# -----------------------------------------------------------------------------

fig = plt.figure(figsize=(8.0, 4.0))
ax = fig.add_subplot()
ax.axhline(0.0, color=ui.AXIS, lw=0.9)
ax.plot(z_real, np.real(theta_real), color=ui.BLUE, label=r"$\Theta_N(z)$, $z$ real")
visible = np.abs(omegas) <= z_real[-1]
ax.plot(omegas[visible], lattice_values[visible], linestyle="none", marker="o", markersize=7.0,
        markerfacecolor="none", markeredgecolor=ui.INK, markeredgewidth=1.0,
        label=r"lattice values $(-1)^j \xi_{N,j} / \sqrt{L}$ at $\omega_j$ (eq. 112)")
shown = zeros[np.abs(zeros) <= z_real[-1]]
ax.plot(shown, np.zeros_like(shown), linestyle="none", marker="o", color=ui.ORANGE, zorder=4,
        label=r"zeros = nonzero eigenvalues of $D'_N$", **ui.marker_ring())
for z in shown[shown > 0]:
    ax.annotate(f"{z:.2f}", (z, 0.0), xytext=(0, -13), textcoords="offset points",
                ha="center", va="top", fontsize=8.0, color=ui.INK_2)
ax.set_xlim(z_real[0], z_real[-1])
ax.set_ylim(-1.6, 1.28 * np.max(np.real(theta_real)))
ax.set_xlabel(r"real $z$")
ax.set_ylabel(r"$\Theta_N(z)$")
ax.legend(loc="upper left")
ui.save(
    fig,
    "experiment_09_characteristic_real_axis.svg",
    title="The finite characteristic on the real axis",
    subtitle=(
        r"$\Theta_N(z) = \frac{1}{L}\int_0^L \xi_N(t)\, e^{-iz(t - L/2)}\,dt$ passes through the free-lattice values of eq. (112)"
        "\n"
        r"and, in this window, vanishes exactly at the nonzero eigenvalues of the corrected derivative $D'_N$."
    ),
    source=source,
)

# -----------------------------------------------------------------------------
# Figure 2: log-modulus over a strip of the complex plane.
# -----------------------------------------------------------------------------

x_values = np.linspace(-22.0, 22.0, 260)
y_values = np.linspace(-3.0, 3.0, 150)
log_modulus = np.empty((len(y_values), len(x_values)))

for row, y in enumerate(y_values):
    for column, xr in enumerate(x_values):
        value = characteristic_from_transform(
            coefficients, indices, omegas, L_float, complex(xr, y)
        )
        log_modulus[row, column] = math.log10(max(abs(value), 1.0e-14))

fig = plt.figure(figsize=(8.0, 4.2))
ax = fig.add_subplot()
image = ax.imshow(
    log_modulus,
    origin="lower",
    aspect="auto",
    cmap=ui.SEQUENTIAL,
    extent=[x_values[0], x_values[-1], y_values[0], y_values[-1]],
)
ax.grid(False)
ax.contour(x_values, y_values, log_modulus, levels=np.arange(-1.5, 1.01, 0.5),
           colors=ui.SURFACE, linewidths=0.5, linestyles="solid", alpha=0.7)
ax.axhline(0.0, color=ui.SURFACE, lw=0.8)
inside = zeros[np.abs(zeros) <= x_values[-1]]
ax.plot(inside, np.zeros_like(inside), linestyle="none", marker="o", color=ui.ORANGE,
        zorder=4, **ui.marker_ring())
for z in inside:
    ax.annotate(rf"zero at ${z:+.2f}$", (z, 0.0), xytext=(0, 12), textcoords="offset points",
                ha="center", va="bottom", fontsize=8.0, color=ui.INK,
                bbox={"facecolor": ui.SURFACE, "edgecolor": "none", "pad": 1.2, "alpha": 0.85})
bar = fig.colorbar(image, ax=ax, pad=0.02)
bar.set_label(r"$\log_{10} |\Theta_N(z)|$", color=ui.INK_2)
bar.outline.set_visible(False)
bar.ax.tick_params(colors=ui.AXIS, labelcolor=ui.INK_2)
ax.set_xlabel(r"$\mathrm{Re}\, z$")
ax.set_ylabel(r"$\mathrm{Im}\, z$")
ui.save(
    fig,
    "experiment_09_characteristic_complex_plane.svg",
    title="Every zero of the finite characteristic lies on the real axis",
    subtitle=(
        r"$\log_{10}|\Theta_N|$ on $|\mathrm{Re}\,z| \leq 22$, $|\mathrm{Im}\,z| \leq 3$.  The only wells sit on the real line:"
        "\n"
        r"$D'_N$ is self-adjoint for a positive metric (Proposition 11), so its eigenvalues are real."
    ),
    source=source,
)
