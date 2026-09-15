"""Readable mpmath versions of the numerically delicate core calculations.

This module deliberately duplicates a small amount of ``common.py`` instead
of hiding the mathematics behind a generic backend abstraction.  The float64
and mpmath implementations can therefore be read side by side and serve as
independent checks of one another.

Only the parts that benefit materially from extra precision live here:

* the completed critical kernel and its L1 integral,
* the explicit Fourier/Weil matrix,
* least-eigenline selection,
* the finite characteristic.

The plotting code remains NumPy/Matplotlib because figures do not need dozens
of significant digits.
"""

from __future__ import annotations

import math

from precision import configure_mpmath



def _prime_power_base(n: int) -> int | None:
    """Return p when n is a positive power of the prime p, else None.

    The routine is intentionally elementary.  It keeps the support of the
    von Mangoldt function exact while allowing mpmath to evaluate log(p) at
    whatever precision the caller requested.
    """

    for p in range(2, n + 1):
        # primality test
        is_prime = True
        divisor = 2
        while divisor * divisor <= p:
            if p % divisor == 0:
                is_prime = False
                break
            divisor += 1
        if not is_prime:
            continue

        power = p
        while power < n:
            power *= p
        if power == n:
            return p
    return None

def mp_critical_kernel(y, dps: int = 50):
    """Evaluate the exact critical kernel with mpmath arithmetic."""

    mp = configure_mpmath(dps)
    y = mp.mpf(y)
    r = mp.exp(y)
    m = mp.floor(r)
    theta = r - m
    return mp.pi * mp.exp(-mp.mpf("2.5") * y) * m * (m + 1) * (1 - 2 * theta)


def _kernel_antiderivative(y, n, mp):
    """Antiderivative of K(y) on log(n) <= y < log(n+1)."""

    n = mp.mpf(n)
    return (
        mp.pi
        * n
        * (n + 1)
        * (
            -mp.mpf(2) / 5 * (1 + 2 * n) * mp.exp(-mp.mpf("2.5") * y)
            + mp.mpf(4) / 3 * mp.exp(-mp.mpf("1.5") * y)
        )
    )


def mp_completed_kernel_l1(y_max, dps: int = 50):
    """Integrate |K(y)| from 0 to ``y_max`` exactly panel by panel.

    On each arithmetic panel ``[log n, log(n+1))`` the kernel has one sign
    change at ``log(n+1/2)``.  Using the closed antiderivative is both simpler
    and more accurate than asking a quadrature routine to discover thousands
    of discontinuous derivatives on its own.
    """

    mp = configure_mpmath(dps)
    y_max = mp.mpf(y_max)
    if y_max <= 0:
        return mp.mpf(0)

    n_max = int(mp.floor(mp.exp(y_max)))
    total = mp.mpf(0)

    for n in range(1, n_max + 1):
        left = mp.log(n)
        right = min(y_max, mp.log(n + 1))
        if right <= left:
            continue

        zero = mp.log(mp.mpf(n) + mp.mpf("0.5"))
        F_left = _kernel_antiderivative(left, n, mp)
        F_right = _kernel_antiderivative(right, n, mp)

        if zero <= left or zero >= right:
            total += abs(F_right - F_left)
        else:
            F_zero = _kernel_antiderivative(zero, n, mp)
            total += abs(F_zero - F_left) + abs(F_right - F_zero)

    return total


def mp_arithmetic_interpolation_and_derivative(x, xi, dps: int = 50):
    """High-precision version of the manuscript interpolation a_x and a_x'."""

    mp = configure_mpmath(dps)
    x = mp.mpf(x)
    xi = mp.mpf(xi)

    max_n = max(2, int(mp.ceil(x)) - 1)

    prime_terms = []
    derivative_terms = []
    for n in range(2, max_n + 1):
        prime_base = _prime_power_base(n)
        if n < x and prime_base is not None:
            log_ratio = mp.log(x / n)
            weight = mp.log(prime_base) / mp.sqrt(n)
            prime_terms.append(-weight * mp.sin(xi * log_ratio))
            derivative_terms.append(-weight * log_ratio * mp.cos(xi * log_ratio))

    prime = mp.fsum(prime_terms) if prime_terms else mp.mpf(0)
    prime_derivative = mp.fsum(derivative_terms) if derivative_terms else mp.mpf(0)

    denominator = xi * xi + mp.mpf(1) / 4
    continuum = (mp.sqrt(x) - 1) * xi / denominator
    continuum_derivative = (
        (mp.sqrt(x) - 1)
        * (mp.mpf(1) / 4 - xi * xi)
        / (denominator * denominator)
    )

    z = mp.mpf(5) / 4 + mp.j * xi / 2
    gamma_sum = mp.im(mp.digamma(z)) / 2
    gamma_derivative = mp.re(mp.polygamma(1, z)) / 4

    # The x^{-lambda_k} correction is geometric.  Stop only once it is well
    # below the requested working precision.
    tolerance = mp.power(10, -(dps - 10))
    k = 1
    correction = mp.mpf(0)
    correction_derivative = mp.mpf(0)
    while True:
        lam = 2 * k + mp.mpf(1) / 2
        x_power = x ** (-lam)
        denom = lam * lam + xi * xi
        correction += xi * x_power / denom
        correction_derivative += x_power * (lam * lam - xi * xi) / (denom * denom)
        if abs(x_power) < tolerance:
            break
        k += 1
        if k > 100000:
            raise RuntimeError("gamma correction did not converge")

    return (
        prime + continuum + gamma_sum - correction,
        prime_derivative + continuum_derivative + gamma_derivative - correction_derivative,
    )


def mp_gamma_multiplier(xi, dps: int = 50):
    """a_Gamma(xi) = Re psi(1/4+i xi/2) - log(pi)."""

    mp = configure_mpmath(dps)
    xi = mp.mpf(xi)
    z = mp.mpf(1) / 4 + mp.j * xi / 2
    return mp.re(mp.digamma(z)) - mp.log(mp.pi)


def mp_build_weil_matrix(x: float, N: int, dps: int = 50):
    """Build the explicit finite Weil matrix with arbitrary precision."""

    mp = configure_mpmath(dps)
    x_mp = mp.mpf(str(x))
    L = mp.log(x_mp)
    indices = list(range(-N, N + 1))
    omegas = [2 * mp.pi * j / L for j in indices]

    a_values = []
    a_derivatives = []
    gamma_values = []
    for omega in omegas:
        value, derivative = mp_arithmetic_interpolation_and_derivative(
            x_mp, omega, dps=dps
        )
        a_values.append(value)
        a_derivatives.append(derivative)
        gamma_values.append(mp_gamma_multiplier(omega, dps=dps))

    size = len(indices)
    H = mp.matrix(size, size)
    for row in range(size):
        for column in range(size):
            if row == column:
                H[row, column] = gamma_values[row] + 2 * a_derivatives[row] / L
            else:
                H[row, column] = (
                    2
                    / L
                    * (a_values[row] - a_values[column])
                    / (omegas[row] - omegas[column])
                )

    return H, indices, omegas


def _mp_vector_norm(values, mp):
    return mp.sqrt(mp.fsum([abs(value) ** 2 for value in values]))


def mp_ground_state_data(x: float, N: int, dps: int = 50):
    """Diagonalize the high-precision Weil matrix and normalize at t=0."""

    mp = configure_mpmath(dps)
    H, indices, omegas = mp_build_weil_matrix(x, N, dps=dps)
    eigenvalues, eigenvectors = mp.eigsy(H)

    raw_ground = [eigenvectors[row, 0] for row in range(len(indices))]
    L = mp.log(mp.mpf(str(x)))
    endpoint = mp.fsum(raw_ground) / mp.sqrt(L)
    ground = [value / endpoint for value in raw_ground]

    reversed_ground = list(reversed(raw_ground))
    even_error = _mp_vector_norm(
        [a - b for a, b in zip(raw_ground, reversed_ground)], mp
    )
    odd_error = _mp_vector_norm(
        [a + b for a, b in zip(raw_ground, reversed_ground)], mp
    )

    residual = []
    lam0 = eigenvalues[0]
    for row in range(len(indices)):
        Hv = mp.fsum(H[row, col] * raw_ground[col] for col in range(len(indices)))
        residual.append(Hv - lam0 * raw_ground[row])

    return {
        "H": H,
        "indices": indices,
        "omegas": omegas,
        "eigenvalues": [eigenvalues[j] for j in range(len(indices))],
        "ground_coefficients": ground,
        "raw_ground": raw_ground,
        "endpoint_before_normalization": endpoint,
        "parity_error_even": even_error,
        "parity_error_odd": odd_error,
        "eigenpair_residual": _mp_vector_norm(residual, mp),
    }


def mp_centered_fourier_transform(coefficients, indices, omegas, L, z, dps=50):
    """Evaluate the selected Fourier transform term by term."""

    mp = configure_mpmath(dps)
    z = mp.mpc(z)
    L = mp.mpf(L)
    numerator = 2 * mp.sin(L * z / 2)
    total = mp.mpc(0)
    tolerance = mp.power(10, -(dps - 8))

    for coefficient, j, omega in zip(coefficients, indices, omegas):
        difference = z - omega
        if abs(difference) < tolerance:
            integral = ((-1) ** int(j)) * mp.sqrt(L)
        else:
            integral = numerator / (mp.sqrt(L) * difference)
        total += coefficient * integral

    return total


def mp_characteristic_from_transform(coefficients, indices, omegas, L, z, dps=50):
    """Theta_N(z) from the entire Fourier-transform formula."""

    mp = configure_mpmath(dps)
    return mp_centered_fourier_transform(
        coefficients, indices, omegas, L, z, dps=dps
    ) / mp.mpf(L)


def mp_corrected_derivative_matrix(coefficients, omegas, L, dps=50):
    """D'_N = D_N - (D_N xi_N) ev_0 with mpmath matrices."""

    mp = configure_mpmath(dps)
    size = len(coefficients)
    D_prime = mp.matrix(size, size)
    endpoint_factor = 1 / mp.sqrt(L)

    for row in range(size):
        for column in range(size):
            diagonal = omegas[row] if row == column else 0
            D_prime[row, column] = (
                diagonal - omegas[row] * coefficients[row] * endpoint_factor
            )
    return D_prime


def _mp_sinc(w, mp):
    if abs(w) < mp.eps:
        return mp.mpf(1)
    return mp.sin(w) / w


def mp_characteristic_from_determinants(coefficients, omegas, L, z, dps=50):
    """Theta_N(z) from the determinant ratio, away from the free lattice."""

    mp = configure_mpmath(dps)
    z = mp.mpc(z)
    size = len(omegas)
    D = mp.matrix(size, size)
    for j in range(size):
        D[j, j] = omegas[j]

    D_prime = mp_corrected_derivative_matrix(coefficients, omegas, L, dps=dps)
    numerator = mp.det(D_prime - z * mp.eye(size))
    denominator = mp.det(D - z * mp.eye(size))
    return _mp_sinc(L * z / 2, mp) * numerator / denominator


def mp_to_float_matrix(matrix):
    """Convert a small real mpmath matrix to a NumPy array for plotting."""

    import numpy as np

    return np.array(
        [[float(matrix[row, col]) for col in range(matrix.cols)] for row in range(matrix.rows)],
        dtype=float,
    )


def mp_to_complex_array(values):
    """Convert a small mpmath vector/list to a NumPy complex array."""

    import numpy as np

    return np.array([complex(value) for value in values], dtype=complex)
