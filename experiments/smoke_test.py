"""Quick dependency and implementation smoke test.

No pytest dependency is required.  Run:

    python smoke_test.py

The checks are intentionally small and should finish quickly.
"""

import numpy as np

from common import build_weil_matrix
from high_precision import (
    mp_build_weil_matrix,
    mp_characteristic_from_determinants,
    mp_characteristic_from_transform,
    mp_ground_state_data,
    mp_to_float_matrix,
)
from precision import configure_mpmath


# Float64 and 50-digit matrix implementations should agree to ordinary
# double-precision accuracy on a small carrier.
H_float, _, _ = build_weil_matrix(2.0, 3)
H_mp, _, _ = mp_build_weil_matrix(2.0, 3, dps=50)
H_mp_float = mp_to_float_matrix(H_mp)
matrix_error = np.max(np.abs(H_float - H_mp_float))
assert matrix_error < 1.0e-11, matrix_error

# The two finite-characteristic formulas should agree to many digits away
# from the free Fourier lattice.
mp = configure_mpmath(50)
data = mp_ground_state_data(2.0, 3, dps=50)
L = mp.log(2)
z = mp.mpc("1.1", "0.3")
a = mp_characteristic_from_transform(
    data["ground_coefficients"], data["indices"], data["omegas"], L, z, dps=50
)
b = mp_characteristic_from_determinants(
    data["ground_coefficients"], data["omegas"], L, z, dps=50
)
characteristic_error = abs(a - b)
assert characteristic_error < mp.mpf("1e-40"), characteristic_error

print(f"matrix float64/mp50 agreement: {matrix_error:.3e}")
print(f"characteristic identity error: {mp.nstr(characteristic_error, 8)}")
print("smoke test: PASS")
