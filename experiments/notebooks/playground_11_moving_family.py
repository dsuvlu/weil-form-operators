import marimo

__generated_with = "0.24.2"
app = marimo.App()


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    # 11. A small exploratory family

    Record finite diagnostics along an explicitly chosen list of carriers. The list is editable; no finite plot establishes compactness or zero retention.

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
        'precision': mo.ui.dropdown(options=["float64", "mp50", "mp100", "mp200"], value='float64', label='Precision profile'),
    })
    controls
    return (controls,)


@app.cell
def _(controls):
    settings = controls.value
    return (settings,)


@app.cell
def _(PrecisionChoice, settings):
    precision = PrecisionChoice(name=settings["precision"], dps=None if settings["precision"] == "float64" else int(settings["precision"][2:]))
    return (precision,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## Choose the family before computing

    Edit the list directly. Keep x>1 and integer N≥1; this cell specifies the inputs independently of the measured outputs.
    """)
    return


@app.cell
def _():
    pairs = [
        (1.50, 3),
        (1.75, 3),
        (2.00, 4),
        (2.25, 4),
        (2.50, 4),
        (2.75, 4),
        (3.00, 4),
    ]
    return (pairs,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## Compute each carrier and its anchor

    The loop is visible so you can add a diagnostic or inspect one carrier. Normalizing by the computed anchor is a finite operation, not a uniform anchor bound.
    """)
    return


@app.cell
def _(
    characteristic_from_transform,
    ground_state_data,
    math,
    np,
    pairs,
    precision,
):
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
    return curves, rows, z_real


@app.cell
def _(mo, rows):
    mo.ui.table(rows)
    return


@app.cell
def _(mo, rows):
    import csv
    import io
    _csv_buffer = io.StringIO()
    _writer = csv.DictWriter(_csv_buffer, fieldnames=list(rows[0]))
    _writer.writeheader()
    _writer.writerows(rows)
    mo.download(_csv_buffer.getvalue(), filename="moving_family_diagnostics.csv", label="Download this table")
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## Plot 1

    Change the plotting code here to inspect another aspect of the same calculation. The figure is displayed inline; no SVG is overwritten.
    """)
    return


@app.cell
def _(curves, np, plt, z_real):
    __figure = plt.figure(figsize=(9, 4.8))
    for (_x, _N, _curve) in curves:
        plt.plot(z_real, np.real(_curve), label=f'x={_x:g}, N={_N}')
    plt.xlabel('real z')
    plt.ylabel('Re[Θ_N(z) / Θ_N(i/4)]')
    plt.title('Exploratory normalized finite characteristics')
    plt.legend()
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
def _(plt, rows):
    __figure_1 = plt.figure(figsize=(8, 4.5))
    plt.plot([_row['L'] for _row in rows], [_row['ground_energy'] for _row in rows], marker='o')
    plt.xlabel('L = log x')
    plt.ylabel('least eigenvalue')
    plt.title('Finite least eigenvalues along the predetermined family')
    plt.tight_layout()
    plt.close(__figure_1)
    __figure_1
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## Plot 3

    Change the plotting code here to inspect another aspect of the same calculation. The figure is displayed inline; no SVG is overwritten.
    """)
    return


@app.cell
def _(plt, rows):
    __figure_2 = plt.figure(figsize=(8, 4.5))
    plt.semilogy([_row['L'] for _row in rows], [_row['gap'] for _row in rows], marker='o')
    plt.xlabel('L = log x')
    plt.ylabel('first spectral gap')
    plt.title('Finite spectral gaps along the predetermined family')
    plt.tight_layout()
    plt.close(__figure_2)
    __figure_2
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## Things to try

    - Add an eigenpair residual or a second off-real evaluation to each row.
    - Repeat a small subset at mp50 before enlarging the list.
    - Distinguish numerical instability from an actual change in the selected finite eigenline.
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
