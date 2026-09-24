"""Experiment 3: the absorbing derivative generator and Volterra resolvent.

Paper I, Section 2.2, eqs. (11)-(12).  The generator A_L f = f' has domain
{f in H^1(0, L) : f(L) = 0}.  Its resolvent integrates back from the absorbing
endpoint,

    R_b f(t) = int_t^L exp(-b(u - t)) f(u) du,     R_b = (b - A_L)^{-1},

so R_b f always vanishes at t = L and (b - A_L) R_b f = f.
"""

import matplotlib.pyplot as plt
import numpy as np

from common import volterra_resolvent
import presentation as ui


ui.use_style()
ui.banner(
    3,
    "The absorbing generator and its Volterra resolvent",
    status=ui.THEOREM,
    reference="Paper I, Section 2.2, eqs. (11)-(12)",
    claim=(
        "R_b f(t) = int_t^L exp(-b(u-t)) f(u) du vanishes at the absorbing "
        "endpoint t = L and inverts b - A_L, where A_L f = f'."
    ),
)

L = 3.0
t = np.linspace(0.0, L, 1600)
b = 1.3

f = 1.0 + 0.25 * np.cos(2.0 * np.pi * t / L)
R = volterra_resolvent(t, f, b)
R_derivative = np.gradient(R, t)
residual = b * R - R_derivative - f

print(f"R_b f at the absorbing endpoint: {R[-1]:.3e}")
print(f"max residual in (b-A)R_b f=f: {np.max(np.abs(residual[5:-5])):.3e}")

interior = np.max(np.abs(residual[5:-5]))
edge = max(np.max(np.abs(residual[:5])), np.max(np.abs(residual[-5:])))
ui.reading(
    f"R_b f is exactly zero at t = L.  The interior residual {interior:.1e} is "
    "discretization error: trapezoid integration and centred differences are "
    "both second order, and the residual drops about fourfold each time the "
    "grid is doubled.  The first and last five samples are excluded because "
    f"np.gradient uses first-order one-sided stencils there (residual {edge:.1e}).",
    figures=("experiment_03_volterra_resolvent.svg", "experiment_03_resolvent_residual.svg"),
)

source = "Paper I, Section 2.2, eqs. (11)-(12)  ·  L = 3, b = 1.3  ·  " + ui.THEOREM

# -----------------------------------------------------------------------------
# Figure 1: the input and its resolvent.
# -----------------------------------------------------------------------------

fig = plt.figure(figsize=(8.0, 3.8))
ax = fig.add_subplot()
ax.plot(t, f, color=ui.BLUE)
ax.plot(t, np.real(R), color=ui.ORANGE)
ui.label_end(ax, t[len(t) // 6], f[len(t) // 6], r"input $f$", dy=9, ha="center")
ui.label_end(ax, t[len(t) // 6], np.real(R[len(t) // 6]), r"$R_b f$", dy=-10, ha="center")
ax.axvline(L, color=ui.AXIS, lw=0.9)
ax.plot([L], [0.0], marker="o", color=ui.ORANGE, zorder=4, **ui.marker_ring())
ax.annotate(
    r"$R_b f(L) = 0$" "\nabsorbing endpoint",
    xy=(L, 0.0),
    xytext=(2.93, 0.66),
    textcoords="data",
    ha="right",
    fontsize=8.5,
    color=ui.INK_2,
    arrowprops={"arrowstyle": "-", "color": ui.INK_2, "lw": 0.8},
)
ax.annotate(
    "",
    xy=(1.55, 0.2),
    xytext=(2.45, 0.2),
    arrowprops={"arrowstyle": "-|>", "color": ui.INK_2, "lw": 0.9},
)
ui.note(ax, 2.0, 0.24, r"integrates from $L$ back to $t$", ha="center", va="bottom")
ax.set_xlim(0.0, L + 0.05)
ax.set_ylim(-0.05, 1.4)
ax.set_xlabel(r"$t$")
ax.set_ylabel("value")
ui.save(
    fig,
    "experiment_03_volterra_resolvent.svg",
    title="The resolvent integrates backward from the absorbing endpoint",
    subtitle=(
        r"$R_b f(t) = \int_t^{L} e^{-b(u-t)} f(u)\,du$ solves $(b - A_L)\,g = f$ with the "
        r"boundary condition $g(L) = 0$ built in."
    ),
    source=source,
)

# -----------------------------------------------------------------------------
# Figure 2: the residual of (b - A_L) R_b f = f.
# -----------------------------------------------------------------------------

fig = plt.figure(figsize=(8.0, 3.6))
ax = fig.add_subplot()
magnitude = np.maximum(np.abs(residual), 1.0e-16)
ax.semilogy(t[5:-5], magnitude[5:-5], color=ui.BLUE, lw=1.2)
ax.semilogy(t[:5], magnitude[:5], linestyle="none", marker="o", markersize=4.0, color=ui.MUTED)
ax.semilogy(t[-5:], magnitude[-5:], linestyle="none", marker="o", markersize=4.0, color=ui.MUTED)
ax.axhline(interior, color=ui.AXIS, lw=0.9)
ui.note(ax, L / 2.0, interior * 1.5, rf"interior maximum ${ui.sci(interior)}$", ha="center", va="bottom")
ui.note(ax, 0.06, edge, "one-sided end stencils\n(excluded)", va="center", fontsize=8.0)
ax.set_xlim(-0.05, L + 0.05)
ax.set_ylim(1.0e-9, edge * 4.0)
ax.set_xlabel(r"$t$")
ax.set_ylabel(r"$|\,(b - A_L) R_b f - f\,|$")
ui.save(
    fig,
    "experiment_03_resolvent_residual.svg",
    title="The resolvent identity holds to discretization accuracy",
    subtitle=(
        rf"Interior residual ${ui.sci(interior)}$: second-order error from the trapezoid rule and centred differences."
        "\n"
        r"The end samples use first-order one-sided differences, so the check excludes them."
    ),
    source=source,
)
