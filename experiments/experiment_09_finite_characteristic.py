"""Experiment 9: build the finite characteristic in two independent ways.

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
    FIGURE_DIR,
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


parser = argparse.ArgumentParser(description=__doc__)
add_precision_arguments(parser)
args = parser.parse_args()
precision = resolve_precision(args)

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

# Figures deliberately use the fast entire transform evaluator.  Extra digits
# are diagnostic; a screen-resolution plot cannot display them.
z_real = np.linspace(-28.0, 28.0, 1800)
theta_real = np.array(
    [
        characteristic_from_transform(coefficients, indices, omegas, L_float, complex(z))
        for z in z_real
    ]
)

plt.figure(figsize=(9, 4.5))
plt.plot(z_real, np.real(theta_real))
for root in sorted(np.real(roots)):
    if z_real[0] <= root <= z_real[-1]:
        plt.axvline(root, alpha=0.15)
plt.axhline(0.0, alpha=0.4)
plt.xlabel("real z")
plt.ylabel("Theta_N(z)")
plt.title("Finite boundary characteristic and its real zeros")
plt.tight_layout()
plt.savefig(FIGURE_DIR / "experiment_09_characteristic_real_axis.svg")
plt.close()

x_values = np.linspace(-22.0, 22.0, 260)
y_values = np.linspace(-3.0, 3.0, 150)
log_modulus = np.empty((len(y_values), len(x_values)))

for row, y in enumerate(y_values):
    for column, xr in enumerate(x_values):
        value = characteristic_from_transform(
            coefficients, indices, omegas, L_float, complex(xr, y)
        )
        log_modulus[row, column] = math.log10(max(abs(value), 1.0e-14))

plt.figure(figsize=(9, 4.8))
plt.imshow(
    log_modulus,
    origin="lower",
    aspect="auto",
    extent=[x_values[0], x_values[-1], y_values[0], y_values[-1]],
)
plt.colorbar(label="log10 |Theta_N(z)|")
plt.axhline(0.0)
plt.xlabel("Re z")
plt.ylabel("Im z")
plt.title("Complex-plane modulus of the finite characteristic")
plt.tight_layout()
plt.savefig(FIGURE_DIR / "experiment_09_characteristic_complex_plane.svg")
plt.close()
