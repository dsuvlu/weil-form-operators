"""Experiment 5: the explicit nonclosability witness and its completed image."""

import math

import matplotlib.pyplot as plt
import numpy as np

from common import FIGURE_DIR, critical_kernel


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

plt.figure(figsize=(8, 4.5))
plt.semilogy(T_values, input_norms, marker="o", label="||f_T||")
plt.semilogy(T_values, raw_norms, marker="o", label="||Z_+(1/2) f_T||")
plt.semilogy(T_values, completed_norms, marker="o", label="||X_+ f_T||")
plt.xlabel("T")
plt.ylabel("L2 norm")
plt.title("Raw synthesis retains a nonzero limit while the input vanishes")
plt.legend()
plt.tight_layout()
plt.savefig(FIGURE_DIR / "experiment_05_nonclosability_norms.svg")
plt.close()

plt.figure(figsize=(8, 4.5))
plt.semilogy(T_values, limit_errors, marker="o")
plt.xlabel("T")
plt.ylabel("||Z f_T - g||")
plt.title("Convergence of the raw synthesis to the explicit nonzero limit")
plt.tight_layout()
plt.savefig(FIGURE_DIR / "experiment_05_raw_limit_error.svg")
plt.close()
