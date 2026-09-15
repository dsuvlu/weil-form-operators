"""Experiment 11: deliberately scoped exploration of a small moving family.

This script does NOT prove compactness, noncollapse, zero retention, or any
limiting theorem.  It records finite diagnostics along a predetermined list
of pairs (x,N).

The default run is float64.  A high-precision profile can be requested to
recompute the small matrices and anchor values with mpmath while leaving the
plots in ordinary floating point.
"""

import argparse
import csv
import math
from pathlib import Path

import matplotlib.pyplot as plt
import numpy as np

from common import FIGURE_DIR, characteristic_from_transform, ground_state_data
from high_precision import (
    mp_characteristic_from_transform,
    mp_ground_state_data,
    mp_to_complex_array,
)
from precision import add_precision_arguments, configure_mpmath, resolve_precision


parser = argparse.ArgumentParser(description=__doc__)
add_precision_arguments(parser)
args = parser.parse_args()
precision = resolve_precision(args)

pairs = [
    (1.50, 3),
    (1.75, 3),
    (2.00, 4),
    (2.25, 4),
    (2.50, 4),
    (2.75, 4),
    (3.00, 4),
]

rows = []
curves = []
z_real = np.linspace(-20.0, 20.0, 900)
anchor = 0.25j

print(f"precision profile = {precision.name}")

for x, N in pairs:
    L = math.log(x)

    if precision.uses_mpmath:
        mp = configure_mpmath(precision.dps)
        data_mp = mp_ground_state_data(x, N, dps=precision.dps)
        eigenvalues_mp = data_mp["eigenvalues"]
        coefficients = mp_to_complex_array(data_mp["ground_coefficients"])
        indices = np.array(data_mp["indices"], dtype=int)
        omegas = np.array([float(value) for value in data_mp["omegas"]])

        gap = float(eigenvalues_mp[1] - eigenvalues_mp[0])
        ground_energy = float(eigenvalues_mp[0])
        raw_endpoint = float(abs(data_mp["endpoint_before_normalization"]))
        even_error = float(data_mp["parity_error_even"])

        L_mp = mp.log(mp.mpf(str(x)))
        anchor_mp = mp_characteristic_from_transform(
            data_mp["ground_coefficients"],
            data_mp["indices"],
            data_mp["omegas"],
            L_mp,
            anchor,
            dps=precision.dps,
        )
        anchor_value = complex(anchor_mp)
    else:
        data = ground_state_data(x, N, gamma_terms=5000)
        eigenvalues = data["eigenvalues"]
        coefficients = data["ground_coefficients"]
        indices = data["indices"]
        omegas = data["omegas"]

        gap = float(eigenvalues[1] - eigenvalues[0])
        ground_energy = float(eigenvalues[0])
        raw_endpoint = abs(complex(data["endpoint_before_normalization"]))
        even_error = float(data["parity_error_even"])
        anchor_value = characteristic_from_transform(
            coefficients, indices, omegas, L, anchor
        )

    q_N = raw_endpoint * raw_endpoint

    normalized = np.array(
        [
            characteristic_from_transform(
                coefficients, indices, omegas, L, complex(z)
            )
            / anchor_value
            for z in z_real
        ]
    )
    curves.append((x, N, normalized))

    rows.append(
        {
            "x": x,
            "L": L,
            "N": N,
            "precision": precision.name,
            "ground_energy": ground_energy,
            "gap": gap,
            "even_parity_error": even_error,
            "unit_ground_endpoint_abs": raw_endpoint,
            "q_N": q_N,
            "anchor_real": float(np.real(anchor_value)),
            "anchor_imag": float(np.imag(anchor_value)),
            "anchor_abs": float(abs(anchor_value)),
        }
    )

output_csv = Path(__file__).with_name("moving_family_diagnostics.csv")
with output_csv.open("w", newline="") as handle:
    writer = csv.DictWriter(handle, fieldnames=list(rows[0]))
    writer.writeheader()
    writer.writerows(rows)

print(f"wrote {output_csv}")
for row in rows:
    print(row)

plt.figure(figsize=(9, 4.8))
for x, N, curve in curves:
    plt.plot(z_real, np.real(curve), label=f"x={x:g}, N={N}")
plt.xlabel("real z")
plt.ylabel("Re[Theta_N(z) / Theta_N(i/4)]")
plt.title("Exploratory normalized finite characteristics")
plt.legend()
plt.tight_layout()
plt.savefig(FIGURE_DIR / "experiment_11_normalized_characteristics.svg")
plt.close()

plt.figure(figsize=(8, 4.5))
plt.plot([row["L"] for row in rows], [row["ground_energy"] for row in rows], marker="o")
plt.xlabel("L = log x")
plt.ylabel("least eigenvalue")
plt.title("Finite least eigenvalues along the predetermined family")
plt.tight_layout()
plt.savefig(FIGURE_DIR / "experiment_11_ground_energy.svg")
plt.close()

plt.figure(figsize=(8, 4.5))
plt.semilogy([row["L"] for row in rows], [row["gap"] for row in rows], marker="o")
plt.xlabel("L = log x")
plt.ylabel("first spectral gap")
plt.title("Finite spectral gaps along the predetermined family")
plt.tight_layout()
plt.savefig(FIGURE_DIR / "experiment_11_spectral_gap.svg")
plt.close()
