"""Experiment 6: boundary leakage and the critical source-Gram derivative.

Paper I, Theorem 5 and eq. (63), with the localized form of Theorem 7,
eq. (76).  Extend a source f on (0, L) by zero and apply the full-line
completed operator.  Its output splits into the part retained in (0, L),
X_L(s) f, and the part escaping to the left, L_L(s) f.  The full-line norm is
stationary at s = 1/2, so the two squared norms have opposite derivatives, and

    W_L(X f, X f) = d/ds ||X_L(s) f||^2 at s = 1/2 = -d/ds ||L_L(s) f||^2.

The full-line leakage picture is drawn from the exact critical kernel.  For a
numerically stable derivative check, the retained finite-window family X_L(s)
is evaluated directly from its Euler, Gamma, and polar factors.  This avoids
truncating the infinite escaped tail when differentiating in s.

The manuscript proves the full retained/escaped identity analytically.  This
script is a theorem visualization and consistency check, not a numerical proof.
"""

import math

import matplotlib.pyplot as plt
import numpy as np

from common import (
    critical_kernel,
    escaped_output,
    finite_completed_output_product,
    l2_norm,
    retained_output,
    weil_form_same_vector,
)
import presentation as ui


ui.use_style()
ui.banner(
    6,
    "Boundary leakage and the leakage derivative",
    status=ui.THEOREM,
    reference="Paper I, Theorem 5, eq. (63); Theorem 7, eq. (76)",
    claim=(
        "The localized Weil form of a completed output equals the s-derivative "
        "at s = 1/2 of the energy retained in the window, and minus the "
        "derivative of the energy escaping it."
    ),
)

L = math.log(2.0)
source_grid = np.linspace(0.0, L, 600)
r_grid = np.linspace(0.0, 4.0, 500)

source = np.sin(math.pi * source_grid / L) ** 2
source /= l2_norm(source, source_grid)

# Critical output and visible leakage use the exact Theorem 1 kernel.
y_grid = np.linspace(0.0, r_grid[-1] + L, 1800)
K = critical_kernel(y_grid)
critical_retained = retained_output(source_grid, source, y_grid, K)
critical_escaped = escaped_output(source_grid, source, r_grid, y_grid, K)

# Cross-check the critical kernel against the literal finite factorization.
critical_product = finite_completed_output_product(
    0.5, source_grid, source, gamma_y_steps=1100
)
critical_difference = l2_norm(critical_product - critical_retained, source_grid)
print(f"||critical product output - critical kernel output|| = {critical_difference:.3e}")

# Differentiate the RETAINED finite-window energy using the literal product.
h = 0.002
minus = finite_completed_output_product(
    0.5 - h, source_grid, source, gamma_y_steps=1100
)
plus = finite_completed_output_product(
    0.5 + h, source_grid, source, gamma_y_steps=1100
)

energy_minus = l2_norm(minus, source_grid) ** 2
energy_plus = l2_norm(plus, source_grid) ** 2
retained_derivative = (energy_plus - energy_minus) / (2.0 * h)

weil_direct = weil_form_same_vector(critical_product, source_grid, y_steps=2200)

print(f"d/ds retained energy at 1/2 = {retained_derivative:+.8e}")
print(f"direct localized Weil form  = {weil_direct:+.8e}")
print(f"difference                  = {retained_derivative - weil_direct:+.8e}")
print(f"The theorem predicts escaped-energy derivative = {-retained_derivative:+.8e}")

# -----------------------------------------------------------------------------
# Refinement ladder.  The two sides are computed by different discretizations,
# so a single resolution cannot say whether their gap is a failure of the
# identity or discretization error.  Repeat both at 1/2, 2 and 4 times the
# default resolution (all grids scaled together, h scaled inversely).
# -----------------------------------------------------------------------------


def both_sides(scale):
    grid = np.linspace(0.0, L, int(round(600 * scale)))
    profile = np.sin(math.pi * grid / L) ** 2
    profile /= l2_norm(profile, grid)
    steps = int(round(1100 * scale))
    step = 0.002 / scale
    low = finite_completed_output_product(0.5 - step, grid, profile, gamma_y_steps=steps)
    high = finite_completed_output_product(0.5 + step, grid, profile, gamma_y_steps=steps)
    central = finite_completed_output_product(0.5, grid, profile, gamma_y_steps=steps)
    derivative = (l2_norm(high, grid) ** 2 - l2_norm(low, grid) ** 2) / (2.0 * step)
    form = weil_form_same_vector(central, grid, y_steps=int(round(2200 * scale)))
    return derivative, form


scales = [0.5, 1.0, 2.0, 4.0]
ladder = []
for scale in scales:
    if scale == 1.0:
        ladder.append((retained_derivative, weil_direct))
    else:
        ladder.append(both_sides(scale))
ladder_derivative = np.array([row[0] for row in ladder])
ladder_form = np.array([row[1] for row in ladder])
ladder_gap = np.abs(ladder_derivative - ladder_form)

print()
print("refinement   d/ds retained energy   direct Weil form      |difference|")
for scale, derivative, form, gap in zip(scales, ladder_derivative, ladder_form, ladder_gap):
    print(f"{scale:>7.1f}x   {derivative:+.10e}   {form:+.10e}   {gap:.3e}")

retained_energy = l2_norm(critical_retained, source_grid) ** 2
escaped_energy = l2_norm(critical_escaped, r_grid) ** 2
ui.reading(
    f"At the default resolution the two sides differ by "
    f"{abs(retained_derivative - weil_direct):.1e} "
    f"({abs(retained_derivative - weil_direct) / abs(weil_direct):.1%}).  Under "
    f"refinement the gap halves with every doubling, down to {ladder_gap[-1]:.1e} "
    "at 4x: first-order discretization error, not a failure of the identity.  "
    "The first-order term comes from the midpoint rule on the Gamma factor, "
    "whose s-derivative has a logarithmic singularity at y = 0 (Section 2.2).",
    figures=("experiment_06_boundary_leakage.svg", "experiment_06_retained_derivative.svg"),
)

theorem_source = "Paper I, Theorem 5, eq. (63); Theorem 7, eq. (76)  ·  L = log 2  ·  " + ui.THEOREM

negative_t = -r_grid[::-1]
negative_values = critical_escaped[::-1]

# -----------------------------------------------------------------------------
# Figure 1: the full-line output split at the window boundary.
# -----------------------------------------------------------------------------

fig = plt.figure(figsize=(8.0, 3.9))
ax = fig.add_subplot()
ax.axvspan(0.0, L, color=ui.WASH, zorder=0, linewidth=0.0)
ax.plot(negative_t, np.real(negative_values), color=ui.ORANGE,
        label=rf"escaped $\mathcal{{L}}_L f$,  energy ${escaped_energy:.3f}$ on $(-4, 0)$")
ax.plot(source_grid, np.real(critical_retained), color=ui.BLUE,
        label=rf"retained $X_L f$,  energy ${retained_energy:.3f}$")
ax.axvline(0.0, color=ui.AXIS, lw=0.9)
ax.axvline(L, color=ui.AXIS, lw=0.9)
ymax = 1.15 * max(np.max(np.real(critical_retained)), np.max(np.real(negative_values)))
ui.note(ax, L / 2.0, ymax * 0.97, "window\n$(0, L)$", ha="center", va="top")
ax.annotate("", xy=(-1.6, ymax * 0.8), xytext=(-0.25, ymax * 0.8),
            arrowprops={"arrowstyle": "-|>", "color": ui.INK_2, "lw": 0.9})
ui.note(ax, -0.9, ymax * 0.83, "leaks to the left only", ha="center", va="bottom")
ax.axhline(0.0, color=ui.AXIS, lw=0.9)
ax.set_xlim(-4.0, L + 0.1)
ax.set_ylim(min(0.0, 1.15 * np.min(np.real(negative_values))), ymax)
ax.set_xlabel(r"$t$")
ax.set_ylabel("completed output at $s = 1/2$")
ax.legend(loc="upper left")
ui.save(
    fig,
    "experiment_06_boundary_leakage.svg",
    title="A completed output splits at the window boundary",
    subtitle=(
        r"Backward convolution only samples to the right, so the full-line output of a source in $(0, L)$"
        "\n"
        r"escapes only to the left.  Retained and escaped energies have opposite $s$-derivatives."
    ),
    source=theorem_source,
)

# -----------------------------------------------------------------------------
# Figure 2: the two sides of Theorem 5 under refinement.
# -----------------------------------------------------------------------------

fig = plt.figure(figsize=(8.0, 3.8))
left, right = fig.subplots(1, 2, gridspec_kw={"width_ratios": [1.25, 1.0]})
left.plot(scales, ladder_derivative, color=ui.BLUE, marker="o",
          label=r"$\frac{d}{ds}\|X_L(s)f\|^2$ at $s=\frac{1}{2}$", **ui.marker_ring())
left.plot(scales, ladder_form, color=ui.ORANGE, marker="o",
          label=r"$W_L(Xf, Xf)$ from eq. (76)", **ui.marker_ring())
left.set_xscale("log", base=2)
left.set_xticks(scales, ["½×", "1×", "2×", "4×"])
left.set_xlabel("resolution (default = 1×)")
left.set_ylabel("value")
left.legend(loc="lower right")
left.set_title("the two sides", color=ui.INK_2)

# First-order guide, offset upward so it does not hide the data.
guide = 1.6 * ladder_gap[0] * (np.asarray(scales) / scales[0]) ** -1.0
right.loglog(scales, guide, color=ui.AXIS, lw=1.2)
right.loglog(scales, ladder_gap, color=ui.BLUE, marker="o", **ui.marker_ring())
ui.label_end(right, scales[1], guide[1], "slope −1 guide", dx=6, dy=6)
right.set_xscale("log", base=2)
right.set_xticks(scales, ["½×", "1×", "2×", "4×"])
right.set_xlabel("resolution")
gap_ticks = [3.0e-5, 1.0e-4, 3.0e-4]
right.set_yticks(gap_ticks, [f"${ui.sci(v, 0)}$" for v in gap_ticks])
right.minorticks_off()
right.set_ylabel("|difference|")
right.set_title("their gap", color=ui.INK_2)
ui.save(
    fig,
    "experiment_06_retained_derivative.svg",
    title="The two sides of Theorem 5 converge to each other",
    subtitle=(
        r"The retained-energy derivative (finite difference of the factorized family) and the localized Weil form"
        "\n"
        rf"(direct quadrature) differ by ${ui.sci(ladder_gap[1])}$ at the default resolution; the gap halves with every doubling."
    ),
    source=theorem_source,
)
