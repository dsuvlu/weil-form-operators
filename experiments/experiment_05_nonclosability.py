"""Experiment 5: the explicit nonclosability witness and its completed image.

Paper I, Section 3.1, eqs. (43)-(47).  The inputs

    f_T(t) = exp(-T/2) 1_[T, T+d](t)

shrink to zero, ||f_T||^2 = d exp(-T), yet the raw critical synthesis
Z_+(1/2) f_T converges to g(t) = 2(exp(d/2) - 1) exp(-t/2) != 0.  So Z_+(1/2)
has no closed extension.  Completion kills exactly this defect:
(I - 2 R_{3/2}) exp(-t/2) = 0, and the completed outputs X_+ f_T go to zero.
"""

import math

import matplotlib.pyplot as plt
import numpy as np

from common import critical_kernel
import presentation as ui


ui.use_style()
ui.banner(
    5,
    "The nonclosability witness and its completed image",
    status=ui.THEOREM,
    reference="Paper I, Section 3.1, eqs. (43)-(47)",
    claim=(
        "Inputs f_T -> 0 whose raw critical synthesis converges to the nonzero "
        "g(t) = 2(e^(d/2) - 1) e^(-t/2), so Z_+(1/2) is not closable; the "
        "completed operator sends the same inputs to zero."
    ),
)

d = 1.0
T_values = [3.0, 4.0, 5.0, 6.0, 7.0, 8.0]

max_integer = int(math.exp(max(T_values) + d)) + 2
prefix = np.zeros(max_integer + 1)
for n in range(1, max_integer + 1):
    prefix[n] = prefix[n - 1] + n ** (-0.5)

# Precompute an antiderivative of K for the completed output.
y_grid = np.linspace(0.0, max(T_values) + d + 1.0, 50000)
K = critical_kernel(y_grid)
K_antiderivative = np.zeros_like(y_grid)
K_antiderivative[1:] = np.cumsum(
    0.5 * (K[:-1] + K[1:]) * np.diff(y_grid)
)


def integral_K(a, b):
    if b <= a:
        return 0.0
    Fa = np.interp(a, y_grid, K_antiderivative)
    Fb = np.interp(b, y_grid, K_antiderivative)
    return Fb - Fa


input_norms = []
raw_norms = []
completed_norms = []
limit_errors = []

for T in T_values:
    t = np.linspace(0.0, T + d, 7000)
    scale = math.exp(-T / 2.0)

    raw = np.zeros_like(t)
    for i, ti in enumerate(t):
        lower = max(1, math.ceil(math.exp(T - ti)))
        upper = min(max_integer, math.floor(math.exp(T + d - ti)))
        if upper >= lower:
            raw[i] = scale * (prefix[upper] - prefix[lower - 1])

    limit = 2.0 * (math.exp(d / 2.0) - 1.0) * np.exp(-t / 2.0)

    completed = np.zeros_like(t)
    for i, ti in enumerate(t):
        a = max(0.0, T - ti)
        b = max(0.0, T + d - ti)
        completed[i] = scale * integral_K(a, b)

    input_norms.append(math.sqrt(d * math.exp(-T)))
    raw_norms.append(math.sqrt(np.trapezoid(raw * raw, t)))
    completed_norms.append(math.sqrt(np.trapezoid(completed * completed, t)))
    limit_errors.append(math.sqrt(np.trapezoid((raw - limit) ** 2, t)))

print("T    ||f_T||       ||Zf_T||      ||Xf_T||      ||Zf_T-g||")
for T, a, b, c, e in zip(T_values, input_norms, raw_norms, completed_norms, limit_errors):
    print(f"{T:>3.0f}  {a:12.4e}  {b:12.4e}  {c:12.4e}  {e:12.4e}")

# ||exp(-t/2)|| = 1 on the half-line, so ||g|| = 2(exp(d/2) - 1).
limit_norm = 2.0 * (math.exp(d / 2.0) - 1.0)
decay_rate = -np.polyfit(T_values, np.log(limit_errors), 1)[0]
ui.reading(
    f"The inputs shrink by e^(-1/2) per unit of T while ||Z f_T|| settles at "
    f"{raw_norms[-1]:.4f}, the norm ||g|| = 2(e^(1/2) - 1) = {limit_norm:.4f} of "
    f"the nonzero limit.  ||Z f_T - g|| decays at the fitted rate "
    f"exp(-{decay_rate:.3f} T), matching the O(e^(-T/2)) error in the proof.  "
    "The completed outputs track the inputs down to zero.",
    figures=("experiment_05_nonclosability_norms.svg", "experiment_05_raw_limit_error.svg"),
)

source = "Paper I, Section 3.1, eqs. (43)-(47)  ·  d = 1  ·  " + ui.THEOREM

# -----------------------------------------------------------------------------
# Figure 1: three norms against T.
# -----------------------------------------------------------------------------

fig = plt.figure(figsize=(8.0, 4.0))
ax = fig.add_subplot()
ax.axhline(limit_norm, color=ui.AXIS, lw=0.9)
ui.note(ax, T_values[0], limit_norm * 1.12, rf"$\|g\| = 2(e^{{1/2}} - 1) = {limit_norm:.4f}$",
        va="bottom")
series = (
    (raw_norms, ui.ORANGE, r"raw synthesis $\|Z_+(\frac{1}{2}) f_T\|$"),
    (input_norms, ui.BLUE, r"input $\|f_T\|$"),
    (completed_norms, ui.AQUA, r"completed $\|X_+ f_T\|$"),
)
for values, color, label in series:
    ax.semilogy(T_values, values, color=color, marker="o", label=label, **ui.marker_ring())
ui.label_end(ax, T_values[-1], raw_norms[-1], "raw", dx=8)
ui.label_end(ax, T_values[-1], input_norms[-1], "input", dx=8, dy=6)
ui.label_end(ax, T_values[-1], completed_norms[-1], "completed", dx=8, dy=-6)
ax.set_xlim(T_values[0] - 0.2, T_values[-1] + 0.9)
ax.set_ylim(1.0e-2, 4.0)
ax.set_xlabel(r"$T$")
ax.set_ylabel(r"$L^2$ norm")
ax.legend(loc="lower left")
ui.save(
    fig,
    "experiment_05_nonclosability_norms.svg",
    title="The input vanishes but the raw synthesis does not",
    subtitle=(
        r"$f_T = e^{-T/2}\,\mathbf{1}_{[T,\,T+d]} \to 0$, yet $Z_+(\frac{1}{2}) f_T \to g \neq 0$: "
        r"the uncompleted operator is not closable."
        "\n"
        r"Completion removes the defect, since $(I - 2R_{3/2})\,e^{-t/2} = 0$."
    ),
    source=source,
)

# -----------------------------------------------------------------------------
# Figure 2: convergence of the raw synthesis to its limit.
# -----------------------------------------------------------------------------

T_array = np.asarray(T_values)
# Drawn parallel to the data, offset upward, so both stay visible.
reference = 1.7 * limit_errors[0] * np.exp(-(T_array - T_array[0]) / 2.0)
fig = plt.figure(figsize=(8.0, 3.6))
ax = fig.add_subplot()
ax.semilogy(T_array, reference, color=ui.AXIS, lw=1.2)
ax.semilogy(T_values, limit_errors, color=ui.BLUE, marker="o", **ui.marker_ring())
ui.label_end(ax, T_array[-1], reference[-1], r"reference slope $e^{-T/2}$", dx=8)
ui.label_end(ax, T_array[-1], limit_errors[-1], rf"measured, rate $e^{{-{decay_rate:.3f}\,T}}$", dx=8)
ax.set_xlim(T_values[0] - 0.2, T_values[-1] + 1.6)
ax.set_xlabel(r"$T$")
ax.set_ylabel(r"$\|Z_+(\frac{1}{2}) f_T - g\|$")
ui.save(
    fig,
    "experiment_05_raw_limit_error.svg",
    title="The raw outputs converge to g at the predicted rate",
    subtitle=(
        r"The proof bounds the squared error by $O(e^{-T})$, i.e. the error by $O(e^{-T/2})$; "
        rf"the measured decay rate is ${decay_rate:.3f}$."
    ),
    source=source,
)
