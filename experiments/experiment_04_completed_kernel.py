"""Experiment 4: visualize the explicit completed critical kernel.

Paper I, Theorem 1, eqs. (7), (40) and (42).  Completing the critical Euler
synthesis with its Gamma and polar factors gives a bounded convolution
operator X_+ f = int_0^oo K(y) S_y f dy with

    K(y) = pi exp(-5y/2) m (m + 1) (1 - 2 theta),   m = floor(e^y), theta = e^y - m,

and int_0^oo |K| <= 8 pi / 3.

The figure is always drawn with NumPy/Matplotlib.  The optional precision
argument only changes the scalar diagnostic for the L1 integral, which makes
this script a simple first example of the precision ladder.
"""

import argparse
import math

import matplotlib.pyplot as plt
import numpy as np

from common import critical_kernel
from high_precision import mp_completed_kernel_l1
from precision import add_precision_arguments, resolve_precision
import presentation as ui


parser = argparse.ArgumentParser(description=__doc__)
add_precision_arguments(parser)
args = parser.parse_args()
precision = resolve_precision(args)

ui.use_style()
ui.banner(
    4,
    "The completed critical kernel",
    status=ui.THEOREM,
    reference="Paper I, Theorem 1, eqs. (7) and (40)",
    claim=(
        "The completed critical operator is convolution with the explicit "
        "kernel K(y) = pi exp(-5y/2) m(m+1)(1 - 2 theta), m = floor(e^y), "
        "theta = e^y - m, and int |K| <= 8 pi / 3, so X_+ is bounded."
    ),
)

y = np.linspace(0.0, 10.0, 12000)
K = critical_kernel(y)

if precision.uses_mpmath:
    absolute_integral = mp_completed_kernel_l1(10.0, dps=precision.dps)
    print(f"precision profile           = {precision.name}")
    print(f"integral_0^10 |K(y)| dy    = {absolute_integral}")
else:
    absolute_integral = np.trapezoid(np.abs(K), y)
    print("precision profile           = float64")
    print(f"integral_0^10 |K(y)| dy    = {absolute_integral:.12f}")

theoretical_bound = 8.0 * math.pi / 3.0
print(f"theoretical L1 bound       = {theoretical_bound:.12f}")

panels = int(math.floor(math.exp(y[-1])))
if precision.uses_mpmath:
    method = (
        f"The {precision.name} value integrates each of the {panels} arithmetic "
        "panels [log n, log(n+1)) exactly with the closed antiderivative."
    )
else:
    method = (
        f"The float64 value is a trapezoid sum on {len(y)} samples, but [0, 10] "
        f"contains {panels} arithmetic panels, so only its first three or four "
        "digits are reliable; --precision mp50 integrates every panel exactly."
    )
ui.reading(
    f"The L1 mass on [0, 10] is {float(absolute_integral):.4f}, well inside the "
    f"bound 8 pi/3 = {theoretical_bound:.4f}.  {method}",
    figures=(
        "experiment_04_completed_kernel.svg",
        "experiment_04_scaled_kernel.svg",
        "experiment_04_multiplicative_kernel.svg",
    ),
)

source = "Paper I, Theorem 1, eqs. (7), (40), (42)  ·  " + ui.THEOREM

# -----------------------------------------------------------------------------
# Figure 1: the kernel under its envelope.
# -----------------------------------------------------------------------------

# The envelope is smooth, so a coarse grid draws it exactly enough.
y_envelope = np.linspace(0.0, 10.0, 400)
envelope = math.pi * (np.exp(-y_envelope / 2.0) + np.exp(-1.5 * y_envelope))
fig = plt.figure(figsize=(8.0, 4.0))
ax = fig.add_subplot()
ax.fill_between(y_envelope, -envelope, envelope, color=ui.BLUE, alpha=0.08, linewidth=0.0)
ax.plot(y_envelope, envelope, color=ui.BLUE, lw=0.8, alpha=0.6)
ax.plot(y_envelope, -envelope, color=ui.BLUE, lw=0.8, alpha=0.6)
# 12,000 samples; rasterizing this one trace keeps the SVG small.
ax.plot(y, K, color=ui.BLUE, lw=0.7, rasterized=True)
ax.axhline(0.0, color=ui.AXIS, lw=0.9)
ax.annotate(
    r"bound (40): $|K(y)| \leq \pi\,(e^{-y/2} + e^{-3y/2})$",
    xy=(4.2, math.pi * (math.exp(-2.1) + math.exp(-6.3))),
    xytext=(4.6, 1.7),
    fontsize=8.5,
    color=ui.INK_2,
    arrowprops={"arrowstyle": "-", "color": ui.INK_2, "lw": 0.8},
)
ui.note(ax, 9.9, -1.05,
        "past y ≈ 5 the panels are narrower than the\nsampling grid, so the trace fills the envelope",
        fontsize=8.0, color=ui.MUTED, ha="right", va="top")
ax.set_xlim(0.0, 10.0)
ax.set_ylim(-3.0, 6.7)
ax.set_xlabel(r"$y$")
ax.set_ylabel(r"$K(y)$")
ui.save(
    fig,
    "experiment_04_completed_kernel.svg",
    title="An arithmetic sawtooth under an integrable envelope",
    subtitle=(
        r"$K(y) = \pi e^{-5y/2}\, m(m+1)(1 - 2\theta)$, $m = \lfloor e^y \rfloor$, $\theta = e^y - m$.  "
        rf"$\int_0^{{10}} |K| = {float(absolute_integral):.3f} \leq 8\pi/3 = {theoretical_bound:.3f}$, "
        r"so $X_+$ is bounded."
    ),
    source=source,
)

# -----------------------------------------------------------------------------
# Figure 2: divide out the envelope and the factor m(m + 1).
# -----------------------------------------------------------------------------

zoom = y <= math.log(20.0)
m = np.floor(np.exp(y[zoom]))
sawtooth = np.exp(2.5 * y[zoom]) * K[zoom] / (math.pi * m * (m + 1.0))

fig = plt.figure(figsize=(8.0, 3.6))
ax = fig.add_subplot()
ax.grid(axis="x", visible=False)
for n in range(2, 20):
    ax.axvline(math.log(n), color=ui.GRID, lw=0.8, zorder=0)
# Break the line at each threshold so the jumps are not drawn as steep segments.
jumps = np.flatnonzero(np.diff(m)) + 1
for piece_y, piece_v in zip(np.split(y[zoom], jumps), np.split(sawtooth, jumps)):
    ax.plot(piece_y, piece_v, color=ui.BLUE, lw=1.3)
ax.axhline(0.0, color=ui.AXIS, lw=0.9)
top = ax.secondary_xaxis("top", functions=(np.exp, lambda v: np.log(np.maximum(v, 1.0e-12))))
top.set_xticks([1, 2, 3, 4, 5, 6, 8, 10, 15, 20])
top.set_xlabel(r"$e^y$  (panel $[\log m, \log(m+1))$ starts at each integer $m$)", color=ui.INK_2)
top.tick_params(colors=ui.AXIS, labelcolor=ui.INK_2)
ax.set_xlim(0.0, math.log(20.0))
ax.set_ylim(-1.2, 1.2)
ax.set_xlabel(r"$y$")
ax.set_ylabel(r"$e^{5y/2} K(y)\ /\ \pi m(m+1)$")
ui.save(
    fig,
    "experiment_04_scaled_kernel.svg",
    title="Every arithmetic panel carries the same sawtooth",
    subtitle=(
        r"Dividing out the envelope $\pi e^{-5y/2}$ and the integer weight $m(m+1)$ leaves $1 - 2\theta$,"
        "\n"
        r"which falls from $+1$ to $-1$ across each panel and crosses zero at $y = \log(m + 1/2)$."
    ),
    source=source,
)

# -----------------------------------------------------------------------------
# Figure 3: the same kernel against r = e^y.
# -----------------------------------------------------------------------------

mask = y <= math.log(30.0)
r = np.exp(y[mask])
K_r = K[mask]

fig = plt.figure(figsize=(8.0, 3.6))
ax = fig.add_subplot()
floor_r = np.floor(r)
jumps = np.flatnonzero(np.diff(floor_r)) + 1
for piece_r, piece_k in zip(np.split(r, jumps), np.split(K_r, jumps)):
    ax.plot(piece_r, piece_k, color=ui.BLUE, lw=1.2)
ax.axhline(0.0, color=ui.AXIS, lw=0.9)
ax.set_xticks([1, 5, 10, 15, 20, 25, 30])
ax.set_xlim(1.0, 30.0)
ax.set_xlabel(r"$r = e^y$")
ax.set_ylabel(r"$K(\log r)$")
ui.save(
    fig,
    "experiment_04_multiplicative_kernel.svg",
    title="In multiplicative coordinates every panel has unit width",
    subtitle=(
        r"With $u = e^{-y}$, eq. (42) reads $K(y) = \sqrt{u}\,\Sigma_{n \geq 1}\, h(nu)$ for the mean-zero seed "
        r"$h(t) = 2\pi(3t^2 - 2t)$ on $(0, 1]$:"
        "\n"
        r"a weighted Müntz transform, one copy of the seed per integer."
    ),
    source=source,
)
