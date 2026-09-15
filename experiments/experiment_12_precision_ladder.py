"""Experiment 12: show how the same finite calculation stabilizes with precision.

This is a diagnostic demo, not a benchmark.  It repeats one small admitted
carrier at float64, 50, 100, and 200 decimal digits and prints a compact table
for four quantities:

* least eigenvalue,
* first spectral gap,
* endpoint value of the unit ground state,
* finite characteristic at z=i/4.

The point is methodological: increase precision only when the quantities you
care about have not stabilized yet.
"""

import math

from common import characteristic_from_transform, ground_state_data
from high_precision import mp_characteristic_from_transform, mp_ground_state_data
from precision import configure_mpmath


x = 2.0
N = 4
anchor = 0.25j

print("Finite carrier: x=2, N=4")
print()
print(
    f"{'profile':<10} {'ground energy':>24} {'gap':>24} "
    f"{'|endpoint|':>20} {'Theta(i/4)':>28}"
)
print("-" * 114)

# Ordinary double precision.
data = ground_state_data(x, N, gamma_terms=6000)
anchor_value = characteristic_from_transform(
    data["ground_coefficients"],
    data["indices"],
    data["omegas"],
    math.log(x),
    anchor,
)
print(
    f"{'float64':<10} "
    f"{data['eigenvalues'][0]:>24.15e} "
    f"{(data['eigenvalues'][1]-data['eigenvalues'][0]):>24.15e} "
    f"{abs(data['endpoint_before_normalization']):>20.12e} "
    f"{anchor_value.real:>13.6e}{anchor_value.imag:+13.6e}j"
)

for dps in (50, 100, 200):
    mp = configure_mpmath(dps)
    data_mp = mp_ground_state_data(x, N, dps=dps)
    L_mp = mp.log(mp.mpf(str(x)))
    anchor_mp = mp_characteristic_from_transform(
        data_mp["ground_coefficients"],
        data_mp["indices"],
        data_mp["omegas"],
        L_mp,
        anchor,
        dps=dps,
    )

    energy = mp.nstr(data_mp["eigenvalues"][0], 17)
    gap = mp.nstr(data_mp["eigenvalues"][1] - data_mp["eigenvalues"][0], 17)
    endpoint = mp.nstr(abs(data_mp["endpoint_before_normalization"]), 15)
    anchor_text = mp.nstr(anchor_mp, 17)

    print(
        f"{('mp'+str(dps)):<10} {energy:>24} {gap:>24} "
        f"{endpoint:>20} {anchor_text:>28}"
    )

print()
print("Interpretation: once the displayed digits stop changing, more precision")
print("does not improve the demo.  Use higher profiles only when a gap, residual,")
print("or cancellation is small enough to make the float64 result ambiguous.")
