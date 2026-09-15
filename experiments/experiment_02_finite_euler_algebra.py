"""Experiment 2: exact finite Euler synthesis, Mobius inversion, and current."""

import matplotlib.pyplot as plt
import numpy as np

from common import (
    FIGURE_DIR,
    derivative_of_synthesis,
    direct_euler_synthesis,
    euler_product_synthesis,
    maximum_dictionary_error,
    mobius_inverse_coefficients,
    multiply_shift_algebra,
    prime_current_coefficients,
)


x = 30.0
s = 0.75 + 0.20j

Z_direct = direct_euler_synthesis(x, s)
Z_product = euler_product_synthesis(x, s)
Z_inverse = mobius_inverse_coefficients(x, s)
Z_derivative = derivative_of_synthesis(x, s)
current_expected = prime_current_coefficients(x, s)

identity = multiply_shift_algebra(Z_product, Z_inverse, x)
current_from_log_derivative = multiply_shift_algebra(Z_inverse, Z_derivative, x)
current_from_log_derivative = {n: -c for n, c in current_from_log_derivative.items()}

print("finite Euler product error:", maximum_dictionary_error(Z_direct, Z_product))
print("finite inverse error:", maximum_dictionary_error(identity, {1: 1.0}))
print(
    "logarithmic derivative error:",
    maximum_dictionary_error(current_from_log_derivative, current_expected),
)

integers = np.arange(1, int(x))
z_magnitude = np.array([abs(Z_direct.get(int(n), 0.0)) for n in integers])
mu_magnitude = np.array([abs(Z_inverse.get(int(n), 0.0)) for n in integers])
current_magnitude = np.array([abs(current_expected.get(int(n), 0.0)) for n in integers])

plt.figure(figsize=(9, 4.5))
plt.stem(integers, z_magnitude, label="Euler synthesis")
plt.xlabel("n")
plt.ylabel("coefficient magnitude")
plt.title("All integers appear in the finite Euler synthesis")
plt.tight_layout()
plt.savefig(FIGURE_DIR / "experiment_02_euler_coefficients.svg")
plt.close()

plt.figure(figsize=(9, 4.5))
plt.stem(integers, mu_magnitude)
plt.xlabel("n")
plt.ylabel("coefficient magnitude")
plt.title("The finite inverse carries Mobius signs and squarefree support")
plt.tight_layout()
plt.savefig(FIGURE_DIR / "experiment_02_mobius_coefficients.svg")
plt.close()

plt.figure(figsize=(9, 4.5))
plt.stem(integers, current_magnitude)
plt.xlabel("n")
plt.ylabel("coefficient magnitude")
plt.title("The logarithmic derivative isolates prime powers")
plt.tight_layout()
plt.savefig(FIGURE_DIR / "experiment_02_current_coefficients.svg")
plt.close()
