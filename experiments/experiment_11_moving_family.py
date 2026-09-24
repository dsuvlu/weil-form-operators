"""Experiment 11: deliberately scoped exploration of a small moving family.

Paper I, Section 6 and Proposition 14.  The moving question asks whether the
finite characteristics of a family (L_j, N_j) with L_j, N_j -> oo converge to
a nonzero entire function retaining the zeros of Xi.  This script only
records finite diagnostics along a predetermined list of pairs (x, N).

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

from common import characteristic_from_transform, ground_state_data
from high_precision import (
    mp_characteristic_from_transform,
    mp_ground_state_data,
    mp_to_complex_array,
)
from precision import add_precision_arguments, configure_mpmath, resolve_precision
import presentation as ui


parser = argparse.ArgumentParser(description=__doc__)
add_precision_arguments(parser)
args = parser.parse_args()
precision = resolve_precision(args)

ui.use_style()
ui.banner(
    11,
    "A small predetermined moving family",
    status=ui.EXPLORATORY,
    reference="Paper I, Section 6, Proposition 14",
    claim=(
        "None.  This records finite diagnostics (least eigenvalue, gap, "
        "endpoint weight, anchor value, normalized characteristic) along seven "
        "fixed carriers.  It proves no compactness, noncollapse, or zero "
        "retention."
    ),
)

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

print(f"wrote {output_csv.name} (full precision; the table below is rounded)")
print()
print("    x      L   N   least eigenvalue         gap    |endpoint|         q_N   |Theta(i/4)|")
for row in rows:
    print(
        f"{row['x']:5.2f} {row['L']:6.3f} {row['N']:3d}   {row['ground_energy']:16.6e}"
        f" {row['gap']:11.4e} {row['unit_ground_endpoint_abs']:13.6f}"
        f" {row['q_N']:11.4e} {row['anchor_abs']:14.6f}"
    )

admitted = all(
    row["gap"] > 0.0 and row["even_parity_error"] < 1.0e-8 and row["unit_ground_endpoint_abs"] > 1.0e-6
    for row in rows
)
status = (
    "Every carrier in this list has a positive gap and an endpoint-bright even "
    "ground state, so its normalized characteristic is defined."
    if admitted
    else "At least one carrier fails the gap, parity, or endpoint check; inspect the table."
)
ui.reading(
    f"{status}  These are {len(rows)} finite data points; the scripts draw no "
    "conclusion about the moving limit, whose hypotheses remain open.",
    figures=(
        "experiment_11_normalized_characteristics.svg",
        "experiment_11_ground_energy.svg",
        "experiment_11_spectral_gap.svg",
    ),
)

source = "Paper I, Section 6, Proposition 14  ·  " + ui.EXPLORATORY + " (finite data, no limiting claim)"

# -----------------------------------------------------------------------------
# Figure 1: small multiples, one carrier highlighted per panel.
# -----------------------------------------------------------------------------

fig = plt.figure(figsize=(8.0, 4.6))
panels = fig.subplots(2, 4, sharex=True, sharey=True)
for index, ax in enumerate(panels.flat):
    if index >= len(curves):
        ax.axis("off")
        continue
    for other_x, other_N, other in curves:
        ax.plot(z_real, np.real(other), color=ui.AXIS, lw=0.7, alpha=0.8)
    x, N, curve = curves[index]
    ax.axhline(0.0, color=ui.AXIS, lw=0.8)
    ax.plot(z_real, np.real(curve), color=ui.BLUE, lw=1.4)
    ax.set_title(rf"$x = {x:g}$, $N = {N}$", color=ui.INK_2, fontsize=8.5, pad=3)
    ax.grid(False)
    ax.tick_params(labelsize=7.5)
    if index % 4 == 0:
        ax.set_ylabel(r"Re $\Theta_N(z) / \Theta_N(i/4)$", fontsize=8.0)
    if index >= 3:
        ax.set_xlabel(r"real $z$", fontsize=8.0)
        ax.tick_params(labelbottom=True)
panels.flat[-1].text(
    0.02,
    0.5,
    "Each panel highlights one\ncarrier; the others are\nshown in grey.  The anchor\n"
    r"normalization makes every" "\n" r"curve equal 1 at $z = i/4$.",
    transform=panels.flat[-1].transAxes,
    va="center",
    fontsize=8.0,
    color=ui.INK_2,
)
ui.save(
    fig,
    "experiment_11_normalized_characteristics.svg",
    title="Normalized characteristics along a predetermined family",
    subtitle=(
        r"Seven fixed carriers $(x, N)$, $1.5 \leq x \leq 3$.  Exploratory: finite data only, no limiting claim."
    ),
    source=source,
)

# -----------------------------------------------------------------------------
# Figures 2-3: least eigenvalue and first gap against L.
# -----------------------------------------------------------------------------

L_values = [row["L"] for row in rows]


def label_carriers(ax, values):
    for row, value in zip(rows, values):
        ax.annotate(f"N={row['N']}", (row["L"], value), xytext=(0, 8), textcoords="offset points",
                    ha="center", va="bottom", fontsize=7.5, color=ui.MUTED)


fig = plt.figure(figsize=(8.0, 3.6))
ax = fig.add_subplot()
energies = [row["ground_energy"] for row in rows]
ax.semilogy(L_values, energies, color=ui.BLUE, marker="o", **ui.marker_ring())
label_carriers(ax, energies)
ax.set_xlabel(r"$L = \log x$")
ax.set_ylabel(r"least eigenvalue $\varepsilon_N$")
ui.save(
    fig,
    "experiment_11_ground_energy.svg",
    title="Least eigenvalues along the family",
    subtitle=(
        rf"The full least eigenvalue of $H_N$ at each carrier, from ${ui.sci(energies[0])}$ at $x = {rows[0]['x']:g}$ "
        rf"to ${ui.sci(energies[-1])}$ at $x = {rows[-1]['x']:g}$."
        "\n"
        r"The step from $N = 3$ to $N = 4$ is part of the predetermined list."
    ),
    source=source,
)

fig = plt.figure(figsize=(8.0, 3.6))
ax = fig.add_subplot()
gaps = [row["gap"] for row in rows]
ax.semilogy(L_values, gaps, color=ui.BLUE, marker="o", **ui.marker_ring())
label_carriers(ax, gaps)
ax.set_xlabel(r"$L = \log x$")
ax.set_ylabel("first spectral gap")
ui.save(
    fig,
    "experiment_11_spectral_gap.svg",
    title="The first spectral gap stays positive on every carrier",
    subtitle=(
        r"A positive gap is the simplicity half of the simple-even hypothesis; Proposition 14 needs it at every member"
        "\n"
        r"of an unbounded family.  Seven carriers say nothing about that limit."
    ),
    source=source,
)
