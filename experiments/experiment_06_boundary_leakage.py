"""Experiment 6: boundary leakage and the critical source-Gram derivative.

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
    FIGURE_DIR,
    critical_kernel,
    escaped_output,
    finite_completed_output_product,
    l2_norm,
    retained_output,
    weil_form_same_vector,
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

negative_t = -r_grid[::-1]
negative_values = critical_escaped[::-1]

plt.figure(figsize=(9, 4.5))
plt.plot(negative_t, np.real(negative_values), label="escaped output")
plt.plot(source_grid, np.real(critical_retained), label="retained output")
plt.axvline(0.0)
plt.axvline(L)
plt.xlabel("t")
plt.ylabel("completed output")
plt.title("The critical full-line output splits at the finite boundary")
plt.legend()
plt.tight_layout()
plt.savefig(FIGURE_DIR / "experiment_06_boundary_leakage.svg")
plt.close()

plt.figure(figsize=(8, 4.5))
labels = ["retained derivative", "direct Weil form"]
values = [retained_derivative, weil_direct]
plt.bar(labels, values)
plt.ylabel("value")
plt.title("Numerical check: retained source-Gram derivative = Weil form")
plt.tight_layout()
plt.savefig(FIGURE_DIR / "experiment_06_retained_derivative.svg")
plt.close()
