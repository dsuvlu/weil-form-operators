"""Experiment 1: integer multiplication as logarithmic translation.

Paper I, Section 2.1.  On L^2(0, L) the killed backward shift is
S_y f(t) = f(t + y), set to zero once t + y leaves the interval.  Writing
V_n = S_{log n} turns multiplication of integers into composition of shifts,
V_m V_n = V_{mn}, and V_n = 0 once n >= x = e^L.
"""

import math

import matplotlib.pyplot as plt
import numpy as np

import presentation as ui


ui.use_style()
ui.banner(
    1,
    "Integer multiplication as logarithmic translation",
    status=ui.IDENTITY,
    reference="Paper I, Section 2.1",
    claim=(
        "Killed shifts compose additively, S_a S_b = S_(a+b), so on the "
        "logarithmic interval (0, log 30) the operator for multiplication by 6 "
        "is the shift by log 2 followed by the shift by log 3."
    ),
)

L = math.log(30.0)
t = np.linspace(0.0, L, 1200)


def test_function(x):
    return np.exp(-((x - 2.4) / 0.35) ** 2)


def killed_shift(y):
    values = np.zeros_like(t)
    mask = t + y < L
    values[mask] = test_function(t[mask] + y)
    return values


f = test_function(t)
S2 = killed_shift(math.log(2.0))
S6_direct = killed_shift(math.log(6.0))

# Apply S_log(3) to S_log(2) by evaluating the already shifted function.
S2_then_3 = np.zeros_like(t)
shifted_points = t + math.log(3.0)
S2_then_3 = np.interp(shifted_points, t, S2, left=0.0, right=0.0)

error = np.max(np.abs(S2_then_3 - S6_direct))
print(f"max |S_log(3) S_log(2) f - S_log(6) f| = {error:.3e}")

# Where does the deviation come from?  The profile is not exactly zero at L,
# so killing it leaves a jump of size f(L).  Linear interpolation of that jump
# in the second shift is the one place the two routes differ at this size.
dt = t[1] - t[0]
jump_cell = np.abs(t - (L - math.log(6.0))) <= 2.0 * dt
interior_error = np.max(np.abs(S2_then_3 - S6_direct)[~jump_cell])

ui.reading(
    f"The two routes agree to {error:.1e}.  That whole deviation sits in the "
    f"single grid cell at the killed boundary t = L - log 6, where the shifted "
    f"profile drops from f(L) = {test_function(L):.1e} to zero between two "
    f"samples.  Elsewhere the difference is {interior_error:.1e}, the size of "
    f"ordinary linear-interpolation error on this grid.",
    figures=("experiment_01_shifted_functions.svg", "experiment_01_logarithmic_nodes.svg"),
)

# -----------------------------------------------------------------------------
# Figure 1: one profile, two shifts, and the composed shift.
# -----------------------------------------------------------------------------

fig = plt.figure(figsize=(8.0, 3.9))
ax = fig.add_subplot()
ax.plot(t, f, color=ui.BLUE, label=r"$f$")
ax.plot(t, S2, color=ui.ORANGE, label=r"$S_{\log 2}\, f$")
ax.plot(t, S6_direct, color=ui.AQUA, label=r"$S_{\log 6}\, f$")
every = np.arange(12, len(t), 24)
every = every[S2_then_3[every] > 1.0e-3]
ax.plot(
    t[every],
    S2_then_3[every],
    linestyle="none",
    marker="o",
    markersize=4.2,
    markerfacecolor="none",
    markeredgecolor=ui.INK,
    markeredgewidth=0.9,
    label=r"$S_{\log 3}\, S_{\log 2}\, f$ (sampled)",
)

peak = 2.4
for shift, color_y in ((math.log(2.0), 1.07), (math.log(6.0), 1.17)):
    ax.annotate(
        "",
        xy=(peak - shift, color_y),
        xytext=(peak, color_y),
        arrowprops={"arrowstyle": "-|>", "color": ui.INK_2, "lw": 0.9, "shrinkA": 0, "shrinkB": 0},
    )
ui.note(ax, peak - math.log(2.0) / 2.0, 1.09, r"$-\log 2$", ha="center", va="bottom")
ui.note(ax, peak - math.log(6.0) / 2.0, 1.19, r"$-\log 6 = -\log 2 - \log 3$", ha="center", va="bottom")

ax.axvline(L, color=ui.AXIS, lw=0.9)
ui.note(ax, L, 0.5, "killed\nbeyond $L$", ha="right", va="center", fontsize=8.0,
        bbox={"facecolor": ui.SURFACE, "edgecolor": "none", "pad": 1.5})
ax.set_xlim(0.0, L + 0.05)
ax.set_ylim(-0.03, 1.3)
ax.set_xlabel(r"$t$  (logarithmic coordinate, $L = \log 30$)")
ax.set_ylabel("value")
ax.legend(loc="upper left", ncols=2)
ui.save(
    fig,
    "experiment_01_shifted_functions.svg",
    title="Multiplying by n moves a profile left by log n",
    subtitle=(
        r"Shifting by $\log 2$ and then by $\log 3$ lands exactly on the shift by $\log 6$:"
        "\n"
        rf"$\max\,|S_{{\log 3}} S_{{\log 2}} f - S_{{\log 6}} f| = {ui.sci(error)}$, all of it from one grid cell at the killed boundary."
    ),
    source="Paper I, Section 2.1  ·  " + ui.IDENTITY,
)

# -----------------------------------------------------------------------------
# Figure 2: the arithmetic nodes t = log n inside (0, L).
# -----------------------------------------------------------------------------

fig = plt.figure(figsize=(8.0, 2.6))
ax = fig.add_subplot()
ax.grid(False)
ax.spines["left"].set_visible(False)
ax.axhline(0.0, color=ui.AXIS, lw=0.9, zorder=1)

nodes = [n for n in range(2, 30) if math.log(n) < L]
ax.plot([0.0], [0.0], marker="o", markersize=6.5, color=ui.INK_2, zorder=3, **ui.marker_ring())
ax.annotate("1", (0.0, 0.0), xytext=(0, 7), textcoords="offset points",
            ha="center", va="bottom", fontsize=8.5, color=ui.INK_2)
primes = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29}
for n in nodes:
    is_prime = n in primes
    ax.plot(
        [math.log(n)],
        [0.0],
        marker="o",
        markersize=6.5 if n < 16 else 4.5,
        color=ui.BLUE if is_prime else ui.MUTED,
        zorder=3,
        **ui.marker_ring(),
    )
    if n < 16:
        ax.annotate(str(n), (math.log(n), 0.0), xytext=(0, 7), textcoords="offset points",
                    ha="center", va="bottom", fontsize=8.5, color=ui.INK_2)

# log 6 = log 2 + log 3, drawn as two hops under the axis.
for start, stop, text in ((0.0, math.log(2.0), r"$\log 2$"), (math.log(2.0), math.log(6.0), r"$\log 3$")):
    ax.annotate("", xy=(stop, -0.42), xytext=(start, -0.42),
                arrowprops={"arrowstyle": "-|>", "color": ui.INK_2, "lw": 0.9,
                            "connectionstyle": "arc3,rad=0.25", "shrinkA": 1, "shrinkB": 1})
    ui.note(ax, (start + stop) / 2.0, -0.85, text, ha="center", va="top")

ax.axvline(L, color=ui.AXIS, lw=0.9)
ui.note(ax, L - 0.02, 0.55, r"$L = \log 30$", ha="right", va="bottom")
ax.plot([], [], "o", color=ui.BLUE, label="prime", **ui.marker_ring())
ax.plot([], [], "o", color=ui.MUTED, label="composite", **ui.marker_ring())
ax.legend(loc="upper left", ncols=2, bbox_to_anchor=(0.0, 1.08))
ax.set_yticks([])
ax.set_ylim(-1.35, 1.0)
ax.set_xlim(-0.05, L + 0.05)
ax.set_xlabel(r"$t = \log n$")
ui.save(
    fig,
    "experiment_01_logarithmic_nodes.svg",
    title="The arithmetic nodes crowd toward the end of the window",
    subtitle=(
        r"Every integer $n < 30$ sits at $t = \log n$; consecutive nodes are about $1/n$ apart."
        "\n"
        r"Composites are sums of prime hops: $\log 6 = \log 2 + \log 3$."
    ),
    source="Paper I, Section 2.1  ·  " + ui.IDENTITY,
)
