"""Experiment 8: finite spectral selection of the least eigenline.

Use ordinary float64 by default.  Add ``--precision mp50``, ``mp100`` or
``mp200`` to repeat the matrix construction and Hermitian eigensolve with
mpmath.  The plots are still drawn from float conversions of the final small
vectors; extra digits are for diagnostics, not for prettier figures.
"""

import argparse
import math

import matplotlib.pyplot as plt
import numpy as np

from common import FIGURE_DIR, fourier_series_values, ground_state_data
from high_precision import mp_ground_state_data, mp_to_complex_array
from precision import add_precision_arguments, configure_mpmath, resolve_precision


parser = argparse.ArgumentParser(description=__doc__)
add_precision_arguments(parser)
args = parser.parse_args()
precision = resolve_precision(args)

x = 2.0
N = 4
L = math.log(x)

if precision.uses_mpmath:
    mp = configure_mpmath(precision.dps)
    data = mp_ground_state_data(x, N, dps=precision.dps)
    indices = np.array(data["indices"], dtype=int)
    eigenvalues = data["eigenvalues"]
    coefficients = mp_to_complex_array(data["ground_coefficients"])

    print(f"precision profile              = {precision.name}")
    print(f"least eigenvalue               = {mp.nstr(eigenvalues[0], 30)}")
    print(f"first spectral gap             = {mp.nstr(eigenvalues[1]-eigenvalues[0], 30)}")
    print(f"even-parity error              = {mp.nstr(data['parity_error_even'], 8)}")
    print(f"odd-parity error               = {mp.nstr(data['parity_error_odd'], 8)}")
    print(
        "endpoint before normalization  = "
        f"{mp.nstr(data['endpoint_before_normalization'], 30)}"
    )
    print(f"eigenpair residual             = {mp.nstr(data['eigenpair_residual'], 8)}")
    eigenvalues_for_plot = np.array([float(value) for value in eigenvalues])
else:
    data = ground_state_data(x, N, gamma_terms=6000)
    indices = data["indices"]
    eigenvalues = data["eigenvalues"]
    coefficients = data["ground_coefficients"]

    print("precision profile              = float64")
    print(f"least eigenvalue               = {eigenvalues[0]:.12e}")
    print(f"first spectral gap             = {eigenvalues[1]-eigenvalues[0]:.12e}")
    print(f"even-parity error              = {data['parity_error_even']:.3e}")
    print(f"odd-parity error               = {data['parity_error_odd']:.3e}")
    print(
        "endpoint before normalization  = "
        f"{data['endpoint_before_normalization']:.12e}"
    )
    eigenvalues_for_plot = eigenvalues

endpoint_after = np.sum(coefficients) / math.sqrt(L)
print(f"endpoint after normalization   = {endpoint_after:.12e}")

t = np.linspace(0.0, L, 1200)
xi = fourier_series_values(coefficients, indices, t, L)

plt.figure(figsize=(8, 4.5))
plt.plot(t, np.real(xi))
plt.axvline(L / 2.0, alpha=0.4)
plt.xlabel("t")
plt.ylabel("xi_N(t)")
plt.title("Endpoint-normalized least eigenvector")
plt.tight_layout()
plt.savefig(FIGURE_DIR / "experiment_08_ground_state.svg")
plt.close()

count = min(12, len(eigenvalues_for_plot))
plt.figure(figsize=(8, 4.5))
plt.plot(np.arange(count), eigenvalues_for_plot[:count], marker="o")
plt.xlabel("ordered eigenvalue index")
plt.ylabel("eigenvalue")
plt.title("Lowest eigenvalues of the finite Weil matrix")
plt.tight_layout()
plt.savefig(FIGURE_DIR / "experiment_08_low_spectrum.svg")
plt.close()

plt.figure(figsize=(8, 4.5))
plt.stem(indices, np.real(coefficients))
plt.xlabel("Fourier index j")
plt.ylabel("coefficient")
plt.title("Fourier coefficients of the selected ground state")
plt.tight_layout()
plt.savefig(FIGURE_DIR / "experiment_08_ground_coefficients.svg")
plt.close()
