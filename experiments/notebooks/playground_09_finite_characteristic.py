import marimo

__generated_with = "0.24.2"
app = marimo.App()


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    # 09. Two finite-characteristic formulas

    Compare the entire Fourier evaluator with the determinant ratio away from the free Fourier frequencies.

    Open this file with **`marimo edit`** to inspect and change the code. Each calculation and plot has its own cell; edits rerun dependent cells. The numerical method definitions are editable cells at the end, not a hidden script runner.

    Start with the defaults, then change one parameter or one algorithm at a time. These are numerical experiments, not certified proofs.
    """)
    return


@app.cell
def _():
    import marimo as mo
    import math
    import cmath
    from typing import Callable
    from dataclasses import dataclass
    import numpy as np
    import matplotlib.pyplot as plt

    return cmath, dataclass, math, mo, np, plt


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## Parameters

    The controls set the parameter dictionary below. You can also edit either cell to add a new input. Numerical controls update on submission/focus loss rather than on every keystroke.
    """)
    return


@app.cell
def _(mo):
    controls = mo.ui.dictionary({
        'x': mo.ui.number(start=1.25, stop=3.0, step=0.25, value=2.0, debounce=True, label='x'),
        'N': mo.ui.number(start=1, stop=6, step=1, value=4, debounce=True, label='N'),
        'z_real': mo.ui.number(start=-20.0, stop=20.0, step=0.1, value=1.1, debounce=True, label='z_real'),
        'z_imag': mo.ui.number(start=0.05, stop=2.0, step=0.05, value=0.3, debounce=True, label='z_imag'),
        'plot_points': mo.ui.number(start=300, stop=2400, step=300, value=1800, debounce=True, label='plot_points'),
        'precision': mo.ui.dropdown(options=["float64", "mp50", "mp100", "mp200"], value='float64', label='Precision profile'),
    })
    controls
    return (controls,)


@app.cell
def _(controls):
    settings = controls.value
    return (settings,)


@app.cell
def _(PrecisionChoice, math, settings):
    precision = PrecisionChoice(name=settings["precision"], dps=None if settings["precision"] == "float64" else int(settings["precision"][2:]))
    x = settings["x"]
    N = int(settings["N"])
    L_float = math.log(x)
    test_points = [-12.3+0.35j, -4.7+0.2j, complex(settings["z_real"],settings["z_imag"]), 7.4+0.25j, 14.2+0.4j]
    return L_float, N, precision, test_points, x


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## Compare scalar evaluations and the corrected derivative

    The evaluator, rank-one correction and determinant implementations are editable below. The nonzero imaginary test coordinates avoid the real free spectrum.
    """)
    return


@app.cell
def _(
    L_float,
    N,
    characteristic_from_determinants,
    characteristic_from_transform,
    corrected_derivative_matrix,
    ground_state_data,
    np,
    precision,
    test_points,
    x,
):
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
    return coefficients, indices, omegas, roots


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## Sample the real axis

    The curves use float64 conversions even when the preceding comparison uses arbitrary precision.
    """)
    return


@app.cell
def _(
    L_float,
    characteristic_from_transform,
    coefficients,
    indices,
    np,
    omegas,
    settings,
):
    z_real = np.linspace(-28.0, 28.0, int(settings["plot_points"]))
    theta_real = np.array(
        [
            characteristic_from_transform(coefficients, indices, omegas, L_float, complex(z))
            for z in z_real
        ]
    )
    return theta_real, z_real


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## Sample the complex plane

    Edit the grid and the modulus floor to inspect the picture at a different scale.
    """)
    return


@app.cell
def _(
    L_float,
    characteristic_from_transform,
    coefficients,
    indices,
    math,
    np,
    omegas,
):
    x_values = np.linspace(-22.0, 22.0, 260)
    y_values = np.linspace(-3.0, 3.0, 150)
    log_modulus = np.empty((len(y_values), len(x_values)))

    for row, y in enumerate(y_values):
        for column, xr in enumerate(x_values):
            value = characteristic_from_transform(
                coefficients, indices, omegas, L_float, complex(xr, y)
            )
            log_modulus[row, column] = math.log10(max(abs(value), 1.0e-14))
    return log_modulus, x_values, y_values


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## Plot 1

    Change the plotting code here to inspect another aspect of the same calculation. The figure is displayed inline; no SVG is overwritten.
    """)
    return


@app.cell
def _(np, plt, roots, theta_real, z_real):
    __figure = plt.figure(figsize=(9, 4.5))
    plt.plot(z_real, np.real(theta_real))
    for _root in sorted(np.real(roots)):
        if z_real[0] <= _root <= z_real[-1]:
            plt.axvline(_root, alpha=0.15)
    plt.axhline(0.0, alpha=0.4)
    plt.xlabel('real z')
    plt.ylabel('Θ_N(z)')
    plt.title('Finite boundary characteristic and its real zeros')
    plt.tight_layout()
    plt.close(__figure)
    __figure
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## Plot 2

    Change the plotting code here to inspect another aspect of the same calculation. The figure is displayed inline; no SVG is overwritten.
    """)
    return


@app.cell
def _(log_modulus, plt, x_values, y_values):
    __figure_1 = plt.figure(figsize=(9, 4.8))
    plt.imshow(log_modulus, origin='lower', aspect='auto', extent=[x_values[0], x_values[-1], y_values[0], y_values[-1]])
    plt.colorbar(label='log10 |Θ_N(z)|')
    plt.axhline(0.0)
    plt.xlabel('Re z')
    plt.ylabel('Im z')
    plt.title('Complex-plane modulus of the finite characteristic')
    plt.tight_layout()
    plt.close(__figure_1)
    __figure_1
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## Things to try

    - Change the off-real test point and compare the identity discrepancy.
    - Inspect what the sine factor cancels in the determinant evaluator.
    - Check parity and the full ground hypotheses in playground 08 before treating a plot as an instance of the finite theorem.
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## Numerical method definitions

    These cells contain the methods used above, copied from the companion’s shared numerical modules. Marimo resolves their dependencies even though they appear below their uses. Edit a definition here to experiment without changing the command-line scripts. Leading underscores on a few helper names are removed because marimo reserves them for cell-local variables.

    The module/line notes identify the original implementation; the original scripts remain the reference baseline. The copies are intentionally independent playground code, and are checked against the reference at their defaults.
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ### `primes_below`

    Reference: `common.py:92`.
    """)
    return


@app.function
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
        p = p + 1
    return [n for n in range(2, limit) if is_prime[n]]


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ### `von_mangoldt_table`

    Reference: `common.py:149`.
    """)
    return


@app.cell
def _(math, np):
    def von_mangoldt_table(max_n: int) -> np.ndarray:
        """Compute Lambda(n) for 0 <= n <= max_n."""
        values = np.zeros(max_n + 1, dtype=float)
        for p in primes_below(max_n + 1):
            power = p
            while power <= max_n:
                values[power] = math.log(p)
                if power > max_n // p:
                    break
                power = power * p
        return values

    return (von_mangoldt_table,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ### `digamma_complex`

    Reference: `common.py:482`.
    """)
    return


@app.cell
def _(cmath):
    def digamma_complex(z: complex) -> complex:
        """A small self-contained complex digamma implementation.

        We shift to the right half-plane using psi(z+1)=psi(z)+1/z and then
        use the classical asymptotic expansion.  This is more accurate and much
        faster than truncating the slowly convergent series in equation (82).
        """
        result = 0.0 + 0j
        while abs(z) < 12.0 or z.real < 10.0:
            result = result - 1.0 / z
            z = z + 1.0
        inv = 1.0 / z
        inv2 = inv * inv
        result = result + (cmath.log(z) - 0.5 * inv)
        result = result - inv2 / 12.0
        result = result + inv2 ** 2 / 120.0
        result = result - inv2 ** 3 / 252.0
        result = result + inv2 ** 4 / 240.0
        result = result - inv2 ** 5 / 132.0
        result = result + 691.0 * inv2 ** 6 / 32760.0
        return result

    return (digamma_complex,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ### `trigamma_complex`

    Reference: `common.py:507`.
    """)
    return


@app.function
def trigamma_complex(z: complex) -> complex:
    """Complex trigamma, implemented by recurrence plus asymptotics."""
    result = 0.0 + 0j
    while abs(z) < 12.0 or z.real < 10.0:
        result = result + 1.0 / (z * z)
        z = z + 1.0
    inv = 1.0 / z
    result = result + inv
    result = result + 0.5 * inv ** 2
    result = result + 1.0 / 6.0 * inv ** 3
    result = result - 1.0 / 30.0 * inv ** 5
    result = result + 1.0 / 42.0 * inv ** 7
    result = result - 1.0 / 30.0 * inv ** 9
    result = result + 5.0 / 66.0 * inv ** 11
    result = result - 691.0 / 2730.0 * inv ** 13
    return result


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ### `arithmetic_interpolation_and_derivative`

    Reference: `common.py:527`.
    """)
    return


@app.cell
def _(digamma_complex, math, von_mangoldt_table):
    def arithmetic_interpolation_and_derivative(x: float, xi: float, gamma_terms: int=4000) -> tuple[float, float]:
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
                prime = prime - weight * math.sin(xi * log_ratio)
                prime_derivative = prime_derivative - weight * log_ratio * math.cos(xi * log_ratio)
        denominator = xi * xi + 0.25
        continuum = (math.sqrt(x) - 1.0) * xi / denominator
        continuum_derivative = (math.sqrt(x) - 1.0) * (0.25 - xi * xi) / (denominator * denominator)
        z = 1.25 + 0.5j * xi
        gamma_sum = 0.5 * digamma_complex(z).imag
        gamma_derivative = 0.25 * trigamma_complex(z).real
        k = 1
        while True:
            lam = 2.0 * k + 0.5
            x_power = x ** (-lam)
            denom = lam * lam + xi * xi
            gamma_sum = gamma_sum - xi * x_power / denom
            gamma_derivative = gamma_derivative - x_power * (lam * lam - xi * xi) / (denom * denom)
            if x_power < 1e-16:
                break
            k = k + 1  # lambda_k = 2k + 1/2, k >= 1.  The unweighted sums have the closed forms
        return (prime + continuum + gamma_sum, prime_derivative + continuum_derivative + gamma_derivative)  #  #   xi * sum 1/(lambda_k^2+xi^2)  #       = 1/2 Im psi(5/4 + i xi/2),  #  #   sum (lambda_k^2-xi^2)/(lambda_k^2+xi^2)^2  #       = 1/4 Re psi_1(5/4 + i xi/2).  # Subtract the x^{-lambda_k} correction.  It decays geometrically, so a  # small direct loop is enough even when the unweighted series is delicate.

    return (arithmetic_interpolation_and_derivative,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ### `gamma_multiplier`

    Reference: `common.py:594`.
    """)
    return


@app.cell
def _(digamma_complex, math):
    def gamma_multiplier(xi: float, gamma_terms: int = 4000) -> float:
        """a_Gamma(xi)=Re psi(1/4+i xi/2)-log pi from equation (82)."""

        z = 0.25 + 0.5j * xi
        return float(digamma_complex(z).real - math.log(math.pi))

    return (gamma_multiplier,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ### `build_weil_matrix`

    Reference: `common.py:601`.
    """)
    return


@app.cell
def _(arithmetic_interpolation_and_derivative, gamma_multiplier, math, np):
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

    return (build_weil_matrix,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ### `ground_state_data`

    Reference: `common.py:715`.
    """)
    return


@app.cell
def _(build_weil_matrix, math, np):
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

    return (ground_state_data,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ### `corrected_derivative_matrix`

    Reference: `common.py:762`.
    """)
    return


@app.cell
def _(math, np):
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

    return (corrected_derivative_matrix,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ### `centered_fourier_transform`

    Reference: `common.py:775`.
    """)
    return


@app.cell
def _(cmath, math, np):
    def centered_fourier_transform(coefficients: np.ndarray, indices: np.ndarray, omegas: np.ndarray, L: float, z: complex) -> complex:
        """Compute xi_hat_N(z) from equation (101) using Fourier coefficients."""
        total = 0.0 + 0j
        numerator = 2.0 * cmath.sin(L * z / 2.0)
        for (coefficient, j, omega) in zip(coefficients, indices, omegas):
            difference = z - omega
            if abs(difference) < 1e-10:
                integral = (-1) ** int(j) * math.sqrt(L)
            else:
                integral = numerator / (math.sqrt(L) * difference)
            total = total + coefficient * integral
        return total

    return (centered_fourier_transform,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ### `sinc_complex`

    Reference: `common.py:798`.
    """)
    return


@app.cell
def _(cmath):
    def sinc_complex(w: complex) -> complex:
        """sin(w)/w with the removable value at zero."""

        if abs(w) < 1.0e-12:
            return 1.0 + 0.0j
        return cmath.sin(w) / w

    return (sinc_complex,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ### `characteristic_from_transform`

    Reference: `common.py:806`.
    """)
    return


@app.cell
def _(centered_fourier_transform, np):
    def characteristic_from_transform(
        coefficients: np.ndarray,
        indices: np.ndarray,
        omegas: np.ndarray,
        L: float,
        z: complex,
    ) -> complex:
        """Theta_N(z)=xi_hat_N(z)/L."""

        return centered_fourier_transform(coefficients, indices, omegas, L, z) / L

    return (characteristic_from_transform,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ### `characteristic_from_determinants`

    Reference: `common.py:818`.
    """)
    return


@app.cell
def _(corrected_derivative_matrix, np, sinc_complex):
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

    return (characteristic_from_determinants,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ### `prime_power_base`

    Reference: `high_precision.py:27`.
    """)
    return


@app.function
def prime_power_base(n: int) -> int | None:
    """Return p when n is a positive power of the prime p, else None.

    The routine is intentionally elementary.  It keeps the support of the
    von Mangoldt function exact while allowing mpmath to evaluate log(p) at
    whatever precision the caller requested.
    """
    for p in range(2, n + 1):
        is_prime = True
        divisor = 2  # primality test
        while divisor * divisor <= p:
            if p % divisor == 0:
                is_prime = False
                break
            divisor = divisor + 1
        if not is_prime:
            continue
        power = p
        while power < n:
            power = power * p
        if power == n:
            return p
    return None


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ### `mp_arithmetic_interpolation_and_derivative`

    Reference: `high_precision.py:116`.
    """)
    return


@app.function
def mp_arithmetic_interpolation_and_derivative(x, xi, dps: int=50):
    """High-precision version of the manuscript interpolation a_x and a_x'."""
    mp = configure_mpmath(dps)
    x = mp.mpf(x)
    xi = mp.mpf(xi)
    max_n = max(2, int(mp.ceil(x)) - 1)
    prime_terms = []
    derivative_terms = []
    for n in range(2, max_n + 1):
        prime_base = prime_power_base(n)
        if n < x and prime_base is not None:
            log_ratio = mp.log(x / n)
            weight = mp.log(prime_base) / mp.sqrt(n)
            prime_terms.append(-weight * mp.sin(xi * log_ratio))
            derivative_terms.append(-weight * log_ratio * mp.cos(xi * log_ratio))
    prime = mp.fsum(prime_terms) if prime_terms else mp.mpf(0)
    prime_derivative = mp.fsum(derivative_terms) if derivative_terms else mp.mpf(0)
    denominator = xi * xi + mp.mpf(1) / 4
    continuum = (mp.sqrt(x) - 1) * xi / denominator
    continuum_derivative = (mp.sqrt(x) - 1) * (mp.mpf(1) / 4 - xi * xi) / (denominator * denominator)
    z = mp.mpf(5) / 4 + mp.j * xi / 2
    gamma_sum = mp.im(mp.digamma(z)) / 2
    gamma_derivative = mp.re(mp.polygamma(1, z)) / 4
    tolerance = mp.power(10, -(dps - 10))
    k = 1
    correction = mp.mpf(0)
    correction_derivative = mp.mpf(0)
    while True:
        lam = 2 * k + mp.mpf(1) / 2
        x_power = x ** (-lam)
        denom = lam * lam + xi * xi
        correction = correction + xi * x_power / denom
        correction_derivative = correction_derivative + x_power * (lam * lam - xi * xi) / (denom * denom)
        if abs(x_power) < tolerance:
            break  # The x^{-lambda_k} correction is geometric.  Stop only once it is well
        k = k + 1  # below the requested working precision.
        if k > 100000:
            raise RuntimeError('gamma correction did not converge')
    return (prime + continuum + gamma_sum - correction, prime_derivative + continuum_derivative + gamma_derivative - correction_derivative)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ### `mp_gamma_multiplier`

    Reference: `high_precision.py:174`.
    """)
    return


@app.function
def mp_gamma_multiplier(xi, dps: int = 50):
    """a_Gamma(xi) = Re psi(1/4+i xi/2) - log(pi)."""

    mp = configure_mpmath(dps)
    xi = mp.mpf(xi)
    z = mp.mpf(1) / 4 + mp.j * xi / 2
    return mp.re(mp.digamma(z)) - mp.log(mp.pi)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ### `mp_build_weil_matrix`

    Reference: `high_precision.py:183`.
    """)
    return


@app.function
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


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ### `mp_vector_norm`

    Reference: `high_precision.py:220`.
    """)
    return


@app.function
def mp_vector_norm(values, mp):
    return mp.sqrt(mp.fsum([abs(value) ** 2 for value in values]))


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ### `mp_ground_state_data`

    Reference: `high_precision.py:224`.
    """)
    return


@app.function
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
    even_error = mp_vector_norm(
        [a - b for a, b in zip(raw_ground, reversed_ground)], mp
    )
    odd_error = mp_vector_norm(
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
        "eigenpair_residual": mp_vector_norm(residual, mp),
    }


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ### `mp_centered_fourier_transform`

    Reference: `high_precision.py:264`.
    """)
    return


@app.function
def mp_centered_fourier_transform(coefficients, indices, omegas, L, z, dps=50):
    """Evaluate the selected Fourier transform term by term."""
    mp = configure_mpmath(dps)
    z = mp.mpc(z)
    L = mp.mpf(L)
    numerator = 2 * mp.sin(L * z / 2)
    total = mp.mpc(0)
    tolerance = mp.power(10, -(dps - 8))
    for (coefficient, j, omega) in zip(coefficients, indices, omegas):
        difference = z - omega
        if abs(difference) < tolerance:
            integral = (-1) ** int(j) * mp.sqrt(L)
        else:
            integral = numerator / (mp.sqrt(L) * difference)
        total = total + coefficient * integral
    return total


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ### `mp_characteristic_from_transform`

    Reference: `high_precision.py:285`.
    """)
    return


@app.function
def mp_characteristic_from_transform(coefficients, indices, omegas, L, z, dps=50):
    """Theta_N(z) from the entire Fourier-transform formula."""

    mp = configure_mpmath(dps)
    return mp_centered_fourier_transform(
        coefficients, indices, omegas, L, z, dps=dps
    ) / mp.mpf(L)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ### `mp_corrected_derivative_matrix`

    Reference: `high_precision.py:294`.
    """)
    return


@app.function
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


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ### `mp_sinc`

    Reference: `high_precision.py:311`.
    """)
    return


@app.function
def mp_sinc(w, mp):
    if abs(w) < mp.eps:
        return mp.mpf(1)
    return mp.sin(w) / w


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ### `mp_characteristic_from_determinants`

    Reference: `high_precision.py:317`.
    """)
    return


@app.function
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
    return mp_sinc(L * z / 2, mp) * numerator / denominator


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ### `mp_to_complex_array`

    Reference: `high_precision.py:344`.
    """)
    return


@app.function
def mp_to_complex_array(values):
    """Convert a small mpmath vector/list to a NumPy complex array."""

    import numpy as np

    return np.array([complex(value) for value in values], dtype=complex)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ### `PrecisionChoice`

    Reference: `precision.py:33`.
    """)
    return


@app.cell
def _(dataclass):
    @dataclass(frozen=True)
    class PrecisionChoice:
        """Resolved precision choice for one experiment."""

        name: str
        dps: int | None

        @property
        def uses_mpmath(self) -> bool:
            return self.dps is not None

    return (PrecisionChoice,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ### `configure_mpmath`

    Reference: `precision.py:72`.
    """)
    return


@app.function
def configure_mpmath(dps: int):
    """Import mpmath lazily and set its working precision."""

    try:
        import mpmath as mp
    except ImportError as exc:  # pragma: no cover - friendly public-repo error
        raise RuntimeError(
            "High-precision mode needs mpmath. Install it with "
            "`python -m pip install mpmath`."
        ) from exc

    mp.mp.dps = dps
    return mp


if __name__ == "__main__":
    app.run()
