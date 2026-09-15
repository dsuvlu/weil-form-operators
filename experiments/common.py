"""Shared helpers for the arithmetic-current experiments.

Dependencies are deliberately small:

* Python standard library
* NumPy
* Matplotlib (used by the experiment scripts, not by this module)

No SciPy, SymPy, pandas, or project-specific package is required.

The formulas implemented here follow the public manuscript
"Arithmetic currents and boundary characteristics for finite Weil forms".
The code is intended as a readable computational companion, not as a
replacement for the manuscript's analytic proofs.
"""

from __future__ import annotations

import cmath
import math
from pathlib import Path
from typing import Callable

import numpy as np


FIGURE_DIR = Path(__file__).with_name("figures")
FIGURE_DIR.mkdir(exist_ok=True)


# -----------------------------------------------------------------------------
# Basic numerical helpers
# -----------------------------------------------------------------------------


def trapezoid(values: np.ndarray, grid: np.ndarray) -> complex:
    """Integrate sampled values over a one-dimensional grid."""

    return np.trapezoid(values, grid)


def l2_norm(values: np.ndarray, grid: np.ndarray) -> float:
    """Discrete approximation to the L2 norm on a one-dimensional grid."""

    return float(np.sqrt(np.real(trapezoid(np.conjugate(values) * values, grid))))


def interpolate_complex(
    x_new: np.ndarray | float,
    x: np.ndarray,
    values: np.ndarray,
    *,
    left: complex = 0.0,
    right: complex = 0.0,
) -> np.ndarray:
    """Linear interpolation for possibly complex sampled values."""

    real = np.interp(x_new, x, np.real(values), left=np.real(left), right=np.real(right))
    imag = np.interp(x_new, x, np.imag(values), left=np.imag(left), right=np.imag(right))
    return real + 1j * imag


def midpoint_integral(
    function: Callable[[float], complex],
    a: float,
    b: float,
    steps: int = 400,
) -> complex:
    """Simple midpoint quadrature.

    Midpoints are convenient here because several manuscript kernels have
    integrable endpoint singularities.  Avoiding the endpoints makes the
    implementation both simple and robust enough for visualization.
    """

    if b <= a:
        return 0.0

    width = (b - a) / steps
    total = 0.0 + 0.0j
    for j in range(steps):
        x = a + (j + 0.5) * width
        total += function(x)
    return total * width


# -----------------------------------------------------------------------------
# Elementary arithmetic functions
# -----------------------------------------------------------------------------


def primes_below(limit: int) -> list[int]:
    """Return all primes strictly below ``limit`` using a small sieve."""

    if limit <= 2:
        return []

    is_prime = [True] * limit
    is_prime[0] = False
    is_prime[1] = False

    p = 2
    while p * p < limit:
        if is_prime[p]:
            for multiple in range(p * p, limit, p):
                is_prime[multiple] = False
        p += 1

    return [n for n in range(2, limit) if is_prime[n]]


def mobius_table(max_n: int) -> np.ndarray:
    """Compute mu(n) for 0 <= n <= max_n by direct factorization.

    This is intentionally straightforward rather than optimized.
    """

    mu = np.ones(max_n + 1, dtype=int)
    mu[0] = 0

    for n in range(2, max_n + 1):
        remaining = n
        sign = 1
        square_factor = False

        p = 2
        while p * p <= remaining:
            if remaining % p == 0:
                exponent = 0
                while remaining % p == 0:
                    remaining //= p
                    exponent += 1
                if exponent >= 2:
                    square_factor = True
                    break
                sign *= -1
            p += 1

        if square_factor:
            mu[n] = 0
        else:
            if remaining > 1:
                sign *= -1
            mu[n] = sign

    return mu


def von_mangoldt_table(max_n: int) -> np.ndarray:
    """Compute Lambda(n) for 0 <= n <= max_n."""

    values = np.zeros(max_n + 1, dtype=float)
    for p in primes_below(max_n + 1):
        power = p
        while power <= max_n:
            values[power] = math.log(p)
            if power > max_n // p:
                break
            power *= p
    return values


# -----------------------------------------------------------------------------
# The finite shift algebra V_m V_n = V_{mn}
# -----------------------------------------------------------------------------


def multiply_shift_algebra(
    left: dict[int, complex],
    right: dict[int, complex],
    x: float,
) -> dict[int, complex]:
    """Multiply two finite shift-algebra elements.

    A dictionary entry ``n: c`` represents c * V_n with V_n = S_{log n}.
    Products with mn >= x vanish on the finite window.
    """

    result: dict[int, complex] = {}
    for m, a in left.items():
        for n, b in right.items():
            product = m * n
            if product < x:
                result[product] = result.get(product, 0.0) + a * b
    return result


def direct_euler_synthesis(x: float, s: complex) -> dict[int, complex]:
    """Coefficients of sum_{n<x} n^{-s} V_n."""

    return {n: n ** (-s) for n in range(1, math.ceil(x)) if n < x}


def euler_product_synthesis(x: float, s: complex) -> dict[int, complex]:
    """Build the same synthesis from the terminating prime Euler factors."""

    result: dict[int, complex] = {1: 1.0}
    for p in primes_below(math.ceil(x)):
        factor: dict[int, complex] = {}
        power = 1
        exponent = 0
        while power < x:
            factor[power] = p ** (-exponent * s)
            exponent += 1
            power *= p
        result = multiply_shift_algebra(result, factor, x)
    return result


def mobius_inverse_coefficients(x: float, s: complex) -> dict[int, complex]:
    """Coefficients of the finite Mobius inverse."""

    max_n = math.ceil(x) - 1
    mu = mobius_table(max_n)
    return {
        n: complex(mu[n]) * n ** (-s)
        for n in range(1, max_n + 1)
        if n < x and mu[n] != 0
    }


def derivative_of_synthesis(x: float, s: complex) -> dict[int, complex]:
    """Derivative d/ds of sum n^{-s} V_n."""

    return {
        n: -math.log(n) * n ** (-s)
        for n in range(2, math.ceil(x))
        if n < x
    }


def prime_current_coefficients(x: float, s: complex) -> dict[int, complex]:
    """Coefficients Lambda(n) n^{-s}."""

    max_n = math.ceil(x) - 1
    mangoldt = von_mangoldt_table(max_n)
    return {
        n: mangoldt[n] * n ** (-s)
        for n in range(2, max_n + 1)
        if n < x and mangoldt[n] != 0.0
    }


def maximum_dictionary_error(
    first: dict[int, complex],
    second: dict[int, complex],
) -> float:
    """Maximum absolute coefficient difference between two sparse dictionaries."""

    keys = set(first) | set(second)
    if not keys:
        return 0.0
    return max(abs(first.get(k, 0.0) - second.get(k, 0.0)) for k in keys)


# -----------------------------------------------------------------------------
# Killed shifts and the absorbing Volterra resolvent
# -----------------------------------------------------------------------------


def killed_shift_samples(
    grid: np.ndarray,
    values: np.ndarray,
    y: float,
    L: float,
) -> np.ndarray:
    """Sample S_y f(t)=f(t+y), with zero outside (0,L)."""

    shifted_points = grid + y
    return interpolate_complex(shifted_points, grid, values, left=0.0, right=0.0)


def volterra_resolvent(
    grid: np.ndarray,
    values: np.ndarray,
    b: complex,
) -> np.ndarray:
    """Compute R_b f(t) = integral_t^L exp[-b(u-t)] f(u) du."""

    result = np.zeros_like(values, dtype=complex)
    for i, t in enumerate(grid):
        u = grid[i:]
        integrand = np.exp(-b * (u - t)) * values[i:]
        result[i] = trapezoid(integrand, u)
    return result


# -----------------------------------------------------------------------------
# Critical and parameter-dependent completed kernels
# -----------------------------------------------------------------------------


def critical_kernel_scalar(y: float) -> float:
    """Theorem 1 critical half-line kernel K(y)."""

    if y < 0.0:
        return 0.0
    A = math.exp(y)
    m = math.floor(A)
    theta = A - m
    return math.pi * math.exp(-2.5 * y) * m * (m + 1) * (1.0 - 2.0 * theta)


def critical_kernel(grid: np.ndarray) -> np.ndarray:
    """Vectorized wrapper for the critical kernel."""

    return np.array([critical_kernel_scalar(float(y)) for y in grid], dtype=float)


def completed_seed_h_alpha(
    u: float,
    alpha: float,
    integration_steps: int = 180,
) -> float:
    """The mean-zero seed h_alpha from equation (49), for real alpha.

    The notebook only differentiates along the real s-axis near s=1/2, so
    alpha is real and ``math.gamma`` is sufficient.
    """

    if u <= 0.0 or u >= 1.0:
        return 0.0

    c_alpha = 2.0 * math.pi**alpha / math.gamma(alpha)

    first = u * u * (1.0 - u * u) ** (alpha - 1.0)

    def integrand(t: float) -> float:
        return t ** (2.0 - 2.0 * alpha) * (1.0 - t * t) ** (alpha - 1.0)

    integral = midpoint_integral(integrand, u, 1.0, integration_steps)
    second = 2.0 * alpha * u ** (2.0 * alpha - 1.0) * float(np.real(integral))

    return c_alpha * (first - second)


def parameter_kernel_scalar(
    s: float,
    y: float,
    seed_integration_steps: int = 180,
) -> float:
    """The real-parameter kernel k_s(y) from equations (49)-(50)."""

    if y < 0.0:
        return 0.0

    # At the critical point, use the exact closed formula.
    if abs(s - 0.5) < 1.0e-14:
        return critical_kernel_scalar(y)

    alpha = (2.5 - s) / 2.0
    A = math.exp(y)

    total = 0.0
    for n in range(1, math.ceil(A)):
        if n < A:
            u = n / A
            total += completed_seed_h_alpha(u, alpha, seed_integration_steps)

    return math.exp(-s * y) * total


def parameter_kernel(
    s: float,
    grid: np.ndarray,
    seed_integration_steps: int = 180,
) -> np.ndarray:
    """Sample k_s on a grid."""

    return np.array(
        [
            parameter_kernel_scalar(s, float(y), seed_integration_steps)
            for y in grid
        ],
        dtype=float,
    )


def retained_output(
    source_grid: np.ndarray,
    source_values: np.ndarray,
    kernel_grid: np.ndarray,
    kernel_values: np.ndarray,
) -> np.ndarray:
    """Compute the completed output on the retained interval (0,L)."""

    result = np.zeros_like(source_values, dtype=complex)
    for i, t in enumerate(source_grid):
        q = source_grid[i:]
        y = q - t
        k = interpolate_complex(y, kernel_grid, kernel_values)
        result[i] = trapezoid(k * source_values[i:], q)
    return result


def escaped_output(
    source_grid: np.ndarray,
    source_values: np.ndarray,
    r_grid: np.ndarray,
    kernel_grid: np.ndarray,
    kernel_values: np.ndarray,
) -> np.ndarray:
    """Compute the reflected causal leakage L_L(s)u(r), r>0."""

    result = np.zeros(len(r_grid), dtype=complex)
    for i, r in enumerate(r_grid):
        y = r + source_grid
        k = interpolate_complex(y, kernel_grid, kernel_values)
        result[i] = trapezoid(k * source_values, source_grid)
    return result


# -----------------------------------------------------------------------------
# Localized Weil form
# -----------------------------------------------------------------------------


def correlation_same_vector(
    values: np.ndarray,
    grid: np.ndarray,
    y: float,
) -> float:
    """q_{f,f}(y)=<f,(S_y+S_y*)f> for sampled f."""

    shifted = killed_shift_samples(grid, values, y, float(grid[-1]))
    inner = trapezoid(np.conjugate(values) * shifted, grid)
    return float(2.0 * np.real(inner))


def weil_form_same_vector(
    values: np.ndarray,
    grid: np.ndarray,
    y_steps: int = 1200,
) -> float:
    """Numerically evaluate equation (67) for W_L(f,f).

    Midpoint quadrature avoids evaluating the subtracted real-place integrand
    at y=0, where its two terms are individually singular but their
    combination is finite.
    """

    L = float(grid[-1])
    x = math.exp(L)
    norm_squared = float(np.real(trapezoid(np.conjugate(values) * values, grid)))
    c_L = np.euler_gamma + math.log(4.0 * math.pi * math.tanh(L / 2.0))

    width = L / y_steps
    polar = 0.0
    archimedean = 0.0

    for j in range(y_steps):
        y = (j + 0.5) * width
        q = correlation_same_vector(values, grid, y)
        polar += 2.0 * math.cosh(y / 2.0) * q

        denominator = math.exp(y) - math.exp(-y)
        rho = math.exp(y / 2.0) / denominator
        archimedean += rho * q - 2.0 * norm_squared / denominator

    polar *= width
    archimedean *= width

    max_n = math.ceil(x) - 1
    mangoldt = von_mangoldt_table(max_n)
    prime = 0.0
    for n in range(2, max_n + 1):
        if n < x and mangoldt[n] != 0.0:
            prime += (
                mangoldt[n]
                / math.sqrt(n)
                * correlation_same_vector(values, grid, math.log(n))
            )

    return polar - c_L * norm_squared - archimedean - prime


# -----------------------------------------------------------------------------
# Fourier matrix: equations (82)-(85)
# -----------------------------------------------------------------------------


def digamma_complex(z: complex) -> complex:
    """A small self-contained complex digamma implementation.

    We shift to the right half-plane using psi(z+1)=psi(z)+1/z and then
    use the classical asymptotic expansion.  This is more accurate and much
    faster than truncating the slowly convergent series in equation (82).
    """

    result = 0.0 + 0.0j
    while abs(z) < 12.0 or z.real < 10.0:
        result -= 1.0 / z
        z += 1.0

    inv = 1.0 / z
    inv2 = inv * inv
    result += cmath.log(z) - 0.5 * inv
    result -= inv2 / 12.0
    result += inv2**2 / 120.0
    result -= inv2**3 / 252.0
    result += inv2**4 / 240.0
    result -= inv2**5 / 132.0
    result += 691.0 * inv2**6 / 32760.0
    return result


def trigamma_complex(z: complex) -> complex:
    """Complex trigamma, implemented by recurrence plus asymptotics."""

    result = 0.0 + 0.0j
    while abs(z) < 12.0 or z.real < 10.0:
        result += 1.0 / (z * z)
        z += 1.0

    inv = 1.0 / z
    result += inv
    result += 0.5 * inv**2
    result += (1.0 / 6.0) * inv**3
    result -= (1.0 / 30.0) * inv**5
    result += (1.0 / 42.0) * inv**7
    result -= (1.0 / 30.0) * inv**9
    result += (5.0 / 66.0) * inv**11
    result -= (691.0 / 2730.0) * inv**13
    return result


def arithmetic_interpolation_and_derivative(
    x: float,
    xi: float,
    gamma_terms: int = 4000,
) -> tuple[float, float]:
    """Return a_x(xi) and a_x'(xi) from equation (83).

    The infinite unweighted Gamma series is summed in closed form with
    digamma/trigamma functions.  Only the exponentially small x^{-lambda_k}
    correction is summed directly.

    ``gamma_terms`` is retained in the public function signature so older
    experiment scripts remain compatible; the closed-form evaluation no
    longer needs a large truncation count.
    """

    max_n = max(2, math.ceil(x) - 1)
    mangoldt = von_mangoldt_table(max_n)

    prime = 0.0
    prime_derivative = 0.0
    for n in range(2, max_n + 1):
        if n < x and mangoldt[n] != 0.0:
            log_ratio = math.log(x / n)
            weight = mangoldt[n] / math.sqrt(n)
            prime -= weight * math.sin(xi * log_ratio)
            prime_derivative -= weight * log_ratio * math.cos(xi * log_ratio)

    denominator = xi * xi + 0.25
    continuum = (math.sqrt(x) - 1.0) * xi / denominator
    continuum_derivative = (
        (math.sqrt(x) - 1.0)
        * (0.25 - xi * xi)
        / (denominator * denominator)
    )

    # lambda_k = 2k + 1/2, k >= 1.  The unweighted sums have the closed forms
    #
    #   xi * sum 1/(lambda_k^2+xi^2)
    #       = 1/2 Im psi(5/4 + i xi/2),
    #
    #   sum (lambda_k^2-xi^2)/(lambda_k^2+xi^2)^2
    #       = 1/4 Re psi_1(5/4 + i xi/2).
    z = 1.25 + 0.5j * xi
    gamma_sum = 0.5 * digamma_complex(z).imag
    gamma_derivative = 0.25 * trigamma_complex(z).real

    # Subtract the x^{-lambda_k} correction.  It decays geometrically, so a
    # small direct loop is enough even when the unweighted series is delicate.
    k = 1
    while True:
        lam = 2.0 * k + 0.5
        x_power = x ** (-lam)
        denom = lam * lam + xi * xi
        gamma_sum -= xi * x_power / denom
        gamma_derivative -= x_power * (lam * lam - xi * xi) / (denom * denom)

        if x_power < 1.0e-16:
            break
        k += 1

    return (
        prime + continuum + gamma_sum,
        prime_derivative + continuum_derivative + gamma_derivative,
    )


def gamma_multiplier(xi: float, gamma_terms: int = 4000) -> float:
    """a_Gamma(xi)=Re psi(1/4+i xi/2)-log pi from equation (82)."""

    z = 0.25 + 0.5j * xi
    return float(digamma_complex(z).real - math.log(math.pi))


def build_weil_matrix(
    x: float,
    N: int,
    gamma_terms: int = 4000,
) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    """Build H_N from Theorem 9."""

    L = math.log(x)
    indices = np.arange(-N, N + 1)
    omegas = 2.0 * math.pi * indices / L

    a_values = np.zeros(len(indices), dtype=float)
    a_derivatives = np.zeros(len(indices), dtype=float)
    gamma_values = np.zeros(len(indices), dtype=float)

    for i, omega in enumerate(omegas):
        a_values[i], a_derivatives[i] = arithmetic_interpolation_and_derivative(
            x, float(omega), gamma_terms
        )
        gamma_values[i] = gamma_multiplier(float(omega), gamma_terms)

    H = np.zeros((len(indices), len(indices)), dtype=float)
    for j in range(len(indices)):
        for k in range(len(indices)):
            if j == k:
                H[j, k] = gamma_values[j] + (2.0 / L) * a_derivatives[j]
            else:
                H[j, k] = (
                    (2.0 / L)
                    * (a_values[j] - a_values[k])
                    / (omegas[j] - omegas[k])
                )

    return H, indices, omegas


def fourier_pair_correlation(j: int, k: int, y: float, L: float) -> float:
    """Equation (86) for q_{U_j,U_k}(y), 0 <= y <= L."""

    if y < 0.0 or y > L:
        return 0.0

    omega_j = 2.0 * math.pi * j / L
    omega_k = 2.0 * math.pi * k / L

    if j == k:
        return 2.0 * (1.0 - y / L) * math.cos(omega_j * y)

    return (
        -(2.0 / L)
        * (math.sin(omega_j * y) - math.sin(omega_k * y))
        / (omega_j - omega_k)
    )


def direct_weil_entry(
    x: float,
    j: int,
    k: int,
    y_steps: int = 6000,
) -> float:
    """Compute W_L(U_j,U_k) directly from equation (67)."""

    L = math.log(x)
    delta = 1.0 if j == k else 0.0
    c_L = np.euler_gamma + math.log(4.0 * math.pi * math.tanh(L / 2.0))

    width = L / y_steps
    polar = 0.0
    archimedean = 0.0

    for m in range(y_steps):
        y = (m + 0.5) * width
        q = fourier_pair_correlation(j, k, y, L)

        polar += 2.0 * math.cosh(y / 2.0) * q

        denominator = math.exp(y) - math.exp(-y)
        rho = math.exp(y / 2.0) / denominator
        archimedean += rho * q - 2.0 * delta / denominator

    polar *= width
    archimedean *= width

    max_n = math.ceil(x) - 1
    mangoldt = von_mangoldt_table(max_n)
    prime = 0.0
    for n in range(2, max_n + 1):
        if n < x and mangoldt[n] != 0.0:
            prime += (
                mangoldt[n]
                / math.sqrt(n)
                * fourier_pair_correlation(j, k, math.log(n), L)
            )

    return polar - c_L * delta - archimedean - prime


def direct_weil_matrix(x: float, N: int, y_steps: int = 6000) -> np.ndarray:
    """Build the finite Fourier matrix directly from equation (67)."""

    indices = np.arange(-N, N + 1)
    H = np.zeros((len(indices), len(indices)), dtype=float)
    for row, j in enumerate(indices):
        for column, k in enumerate(indices):
            H[row, column] = direct_weil_entry(x, int(j), int(k), y_steps)
    return H


# -----------------------------------------------------------------------------
# Spectral selection and the finite characteristic
# -----------------------------------------------------------------------------


def ground_state_data(
    x: float,
    N: int,
    gamma_terms: int = 4000,
) -> dict[str, object]:
    """Diagonalize H_N and endpoint-normalize its least eigenvector."""

    H, indices, omegas = build_weil_matrix(x, N, gamma_terms)
    eigenvalues, eigenvectors = np.linalg.eigh(H)

    raw_ground = eigenvectors[:, 0]
    L = math.log(x)
    endpoint = np.sum(raw_ground) / math.sqrt(L)
    ground = raw_ground / endpoint

    # Test parity on the unit eigenvector, before endpoint normalization.
    # This keeps the diagnostic scale-invariant even when the endpoint is small.
    parity_error_even = float(np.linalg.norm(raw_ground - raw_ground[::-1]))
    parity_error_odd = float(np.linalg.norm(raw_ground + raw_ground[::-1]))

    return {
        "H": H,
        "indices": indices,
        "omegas": omegas,
        "eigenvalues": eigenvalues,
        "ground_coefficients": ground,
        "endpoint_before_normalization": endpoint,
        "parity_error_even": parity_error_even,
        "parity_error_odd": parity_error_odd,
    }


def fourier_series_values(
    coefficients: np.ndarray,
    indices: np.ndarray,
    t_grid: np.ndarray,
    L: float,
) -> np.ndarray:
    """Evaluate sum c_j U_j(t)."""

    values = np.zeros(len(t_grid), dtype=complex)
    for coefficient, j in zip(coefficients, indices):
        omega = 2.0 * math.pi * int(j) / L
        values += coefficient * np.exp(1j * omega * t_grid) / math.sqrt(L)
    return values


def corrected_derivative_matrix(
    coefficients: np.ndarray,
    omegas: np.ndarray,
    L: float,
) -> np.ndarray:
    """D'_N = D_N - (D_N xi_N) ev_0 in Fourier coordinates."""

    D = np.diag(omegas.astype(complex))
    D_xi = omegas * coefficients
    endpoint_row = np.ones(len(coefficients), dtype=complex) / math.sqrt(L)
    return D - np.outer(D_xi, endpoint_row)


def centered_fourier_transform(
    coefficients: np.ndarray,
    indices: np.ndarray,
    omegas: np.ndarray,
    L: float,
    z: complex,
) -> complex:
    """Compute xi_hat_N(z) from equation (101) using Fourier coefficients."""

    total = 0.0 + 0.0j
    numerator = 2.0 * cmath.sin(L * z / 2.0)

    for coefficient, j, omega in zip(coefficients, indices, omegas):
        difference = z - omega
        if abs(difference) < 1.0e-10:
            integral = ((-1) ** int(j)) * math.sqrt(L)
        else:
            integral = numerator / (math.sqrt(L) * difference)
        total += coefficient * integral

    return total


def sinc_complex(w: complex) -> complex:
    """sin(w)/w with the removable value at zero."""

    if abs(w) < 1.0e-12:
        return 1.0 + 0.0j
    return cmath.sin(w) / w


def characteristic_from_transform(
    coefficients: np.ndarray,
    indices: np.ndarray,
    omegas: np.ndarray,
    L: float,
    z: complex,
) -> complex:
    """Theta_N(z)=xi_hat_N(z)/L."""

    return centered_fourier_transform(coefficients, indices, omegas, L, z) / L


def characteristic_from_determinants(
    coefficients: np.ndarray,
    omegas: np.ndarray,
    L: float,
    z: complex,
) -> complex:
    """The determinant-ratio representation from equations (100)-(102)."""

    D = np.diag(omegas.astype(complex))
    D_prime = corrected_derivative_matrix(coefficients, omegas, L)
    identity = np.eye(len(omegas), dtype=complex)

    numerator = np.linalg.det(D_prime - z * identity)
    denominator = np.linalg.det(D - z * identity)

    return sinc_complex(L * z / 2.0) * numerator / denominator

# -----------------------------------------------------------------------------
# Faster, still-readable parameter-kernel helper for visualization
# -----------------------------------------------------------------------------


def make_completed_seed_table(
    s: float,
    points: int = 500,
    integration_steps: int = 80,
) -> tuple[np.ndarray, np.ndarray]:
    """Precompute h_alpha(u) for repeated kernel evaluations.

    This is useful for Experiment 6.  The seed is the expensive part of the
    parameter kernel, while a single seed is reused at every arithmetic
    threshold.  We tabulate it once and then use linear interpolation.
    """

    alpha = (2.5 - s) / 2.0

    # Put extra points near u=1, where nearby parameter seeds can have a mild
    # integrable endpoint singularity.
    coarse = np.linspace(1.0e-6, 0.95, max(20, points * 3 // 4))
    near_one = 1.0 - np.geomspace(1.0e-5, 0.05, max(20, points // 4))
    u_grid = np.unique(np.sort(np.concatenate([coarse, near_one])))

    h_values = np.array(
        [
            completed_seed_h_alpha(float(u), alpha, integration_steps)
            for u in u_grid
        ],
        dtype=float,
    )
    return u_grid, h_values


def parameter_kernel_from_seed_table(
    s: float,
    y_grid: np.ndarray,
    u_grid: np.ndarray,
    h_values: np.ndarray,
) -> np.ndarray:
    """Evaluate equation (50) using a precomputed seed table."""

    values = np.zeros(len(y_grid), dtype=float)
    for i, y in enumerate(y_grid):
        if abs(s - 0.5) < 1.0e-14:
            values[i] = critical_kernel_scalar(float(y))
            continue

        A = math.exp(float(y))
        total = 0.0
        for n in range(1, math.ceil(A)):
            if n < A:
                u = n / A
                h = np.interp(u, u_grid, h_values, left=0.0, right=h_values[-1])
                total += h
        values[i] = math.exp(-s * float(y)) * total

    return values

# -----------------------------------------------------------------------------
# Direct finite-window completion from the factorization in Section 2
# -----------------------------------------------------------------------------


def finite_euler_output(
    s: float,
    grid: np.ndarray,
    source_values: np.ndarray,
) -> np.ndarray:
    """Apply Z_L(s)=sum_{n<e^L} n^{-s} S_{log n} to sampled data."""

    L = float(grid[-1])
    x = math.exp(L)
    result = np.zeros_like(source_values, dtype=complex)

    for n in range(1, math.ceil(x)):
        if n < x:
            result += n ** (-s) * killed_shift_samples(
                grid, source_values, math.log(n), L
            )
    return result


def finite_gamma_output(
    s: float,
    grid: np.ndarray,
    values: np.ndarray,
    y_steps: int = 500,
) -> np.ndarray:
    """Apply the finite-window Gamma-ratio operator E_{infty,L}(s)."""

    L = float(grid[-1])
    alpha = (2.5 - s) / 2.0
    prefactor = 2.0 * math.pi**alpha / math.gamma(alpha)

    result = np.zeros_like(values, dtype=complex)
    width = L / y_steps

    for j in range(y_steps):
        y = (j + 0.5) * width
        scalar = (
            prefactor
            * math.exp(-s * y)
            * (1.0 - math.exp(-2.0 * y)) ** (alpha - 1.0)
        )
        result += scalar * killed_shift_samples(grid, values, y, L) * width

    return result


def finite_completed_output_product(
    s: float,
    grid: np.ndarray,
    source_values: np.ndarray,
    gamma_y_steps: int = 500,
) -> np.ndarray:
    """Apply X_L(s)=P_L(s) E_{infty,L}(s) Z_L(s) literally."""

    zeta_part = finite_euler_output(s, grid, source_values)
    gamma_part = finite_gamma_output(s, grid, zeta_part, gamma_y_steps)

    coefficient = s - 2.5

    first = gamma_part + coefficient * volterra_resolvent(
        grid, gamma_part, 2.5
    )
    second = first + coefficient * volterra_resolvent(grid, first, 1.5)
    return second
