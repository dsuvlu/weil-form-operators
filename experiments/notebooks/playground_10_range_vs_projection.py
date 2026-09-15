import marimo

__generated_with = "0.24.2"
app = marimo.App()


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    # 10. Absorbing range versus Fourier projection

    Build terminal-zero columns, project them, and inspect whether they span the periodic finite section.

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

    return cmath, math, mo, np, plt


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
        'width_fraction': mo.ui.number(start=0.05, stop=0.8, step=0.05, value=0.18, debounce=True, label='width_fraction'),
        'points': mo.ui.number(start=1000, stop=10000, step=1000, value=6000, debounce=True, label='points'),
    })
    controls
    return (controls,)


@app.cell
def _(controls):
    settings = controls.value
    return (settings,)


@app.cell
def _(math, np, settings):
    x = settings["x"]
    N = int(settings["N"])
    L = math.log(x)
    indices = np.arange(-N,N+1)
    omegas = 2.0*math.pi*indices/L
    t = np.linspace(0.0,L,int(settings["points"]))
    return L, N, indices, t, x


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## Choose the terminal taper

    This function is an editable cell; it enforces the endpoint condition before projection.
    """)
    return


@app.cell
def _(L, math, np):
    def terminal_taper(t_values, width):
        """Equal to one away from L and smoothly decreases to zero at L."""

        chi = np.ones_like(t_values)
        start = L - width
        mask = t_values > start
        phase = (t_values[mask] - start) / width
        chi[mask] = 0.5 * (1.0 + np.cos(math.pi * phase))
        return chi

    return (terminal_taper,)


@app.cell
def _(L, settings, t, terminal_taper):
    width = settings["width_fraction"]*L
    chi = terminal_taper(t,width)
    return (chi,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## Assemble the projected columns

    Inspect the quadrature for each coefficient ⟨U_k,χU_j⟩.
    """)
    return


@app.cell
def _(L, chi, indices, math, np, t):
    projection_matrix = np.zeros((len(indices), len(indices)), dtype=complex)
    for column, j in enumerate(indices):
        U_j = np.exp(1j * (2.0 * math.pi * j / L) * t) / math.sqrt(L)
        f_j = chi * U_j

        for row, k in enumerate(indices):
            U_k = np.exp(1j * (2.0 * math.pi * k / L) * t) / math.sqrt(L)
            projection_matrix[row, column] = np.trapezoid(np.conjugate(U_k) * f_j, t)
    return (projection_matrix,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## Inspect numerical rank

    Singular values quantify this finite discretization. Existence of a projected source does not give a uniform inverse estimate.
    """)
    return


@app.cell
def _(indices, np, projection_matrix):
    singular_values = np.linalg.svd(projection_matrix, compute_uv=False)
    print(f"smallest singular value of projected terminal-zero family = {singular_values[-1]:.6e}")
    print(f"numerical rank = {np.linalg.matrix_rank(projection_matrix)} of {len(indices)}")
    return (singular_values,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## Compare the selected periodic vector

    A boundary-bright periodic vector does not itself satisfy the absorbing endpoint condition.
    """)
    return


@app.cell
def _(L, N, fourier_series_values, ground_state_data, t, x):
    data = ground_state_data(x, N, gamma_terms=6000)
    ground_coefficients = data["ground_coefficients"]
    ground = fourier_series_values(ground_coefficients, data["indices"], t, L)
    print(f"ground endpoint xi_N(L) = {ground[-1]:.8e}")
    return (ground,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## Plot 1

    Change the plotting code here to inspect another aspect of the same calculation. The figure is displayed inline; no SVG is overwritten.
    """)
    return


@app.cell
def _(L, chi, plt, t):
    __figure = plt.figure(figsize=(8, 4.5))
    plt.plot(t, chi)
    plt.axvline(L)
    plt.xlabel('t')
    plt.ylabel('taper')
    plt.title('A terminal-zero H1 taper used to generate the projected section')
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
def _(np, plt, singular_values):
    __figure_1 = plt.figure(figsize=(8, 4.5))
    plt.plot(np.arange(len(singular_values)), singular_values, marker='o')
    plt.xlabel('singular-value index')
    plt.ylabel('singular value')
    plt.title('Projection of terminal-zero modes spans the whole finite Fourier section')
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
def _(L, chi, ground, np, plt, t):
    __figure_2 = plt.figure(figsize=(8, 4.5))
    plt.plot(t, np.real(ground), label='periodic selected ground')
    plt.plot(t, np.real(chi * ground), label='terminal-zero tapered ground')
    plt.axvline(L)
    plt.xlabel('t')
    plt.ylabel('value')
    plt.title('Literal absorbing range and periodic selection impose different endpoints')
    plt.legend()
    plt.tight_layout()
    plt.close(__figure_2)
    __figure_2
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## Things to try

    - Narrow the taper and watch the projected singular values.
    - Increase the integration grid before trusting a very small singular value.
    - Replace the cosine taper by another terminal-zero profile.
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
    ### `fourier_series_values`

    Reference: `common.py:747`.
    """)
    return


@app.cell
def _(math, np):
    def fourier_series_values(coefficients: np.ndarray, indices: np.ndarray, t_grid: np.ndarray, L: float) -> np.ndarray:
        """Evaluate sum c_j U_j(t)."""
        values = np.zeros(len(t_grid), dtype=complex)
        for (coefficient, j) in zip(coefficients, indices):
            omega = 2.0 * math.pi * int(j) / L
            values = values + coefficient * np.exp(1j * omega * t_grid) / math.sqrt(L)
        return values

    return (fourier_series_values,)


if __name__ == "__main__":
    app.run()
