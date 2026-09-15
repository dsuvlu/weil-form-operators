import marimo

__generated_with = "0.24.2"
app = marimo.App()


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    # 06. Boundary leakage and the Weil pairing

    Hold the source fixed while differentiating the retained completed energy. Compare that derivative with an independent localized Weil pairing.

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

    return math, mo, np, plt


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
        'x': mo.ui.number(start=1.25, stop=4.0, step=0.25, value=2.0, debounce=True, label='x'),
        'h': mo.ui.number(start=0.0005, stop=0.02, step=0.0005, value=0.002, debounce=True, label='h'),
        'points': mo.ui.number(start=200, stop=1200, step=100, value=600, debounce=True, label='points'),
        'gamma_steps': mo.ui.number(start=400, stop=2400, step=100, value=1100, debounce=True, label='gamma_steps'),
    })
    controls
    return (controls,)


@app.cell
def _(controls):
    settings = controls.value
    return (settings,)


@app.cell
def _(math, np, settings):
    L = math.log(settings["x"])
    h = settings["h"]
    gamma_steps = int(settings["gamma_steps"])
    source_grid = np.linspace(0.0, L, int(settings["points"]))
    r_grid = np.linspace(0.0, 4.0, 500)
    return L, gamma_steps, h, r_grid, source_grid


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## A frozen source

    The same source is used at 1/2−h and 1/2+h. Edit its profile here.
    """)
    return


@app.cell
def _(L, l2_norm, math, np, source_grid):
    source = np.sin(math.pi * source_grid / L) ** 2
    source = source / l2_norm(source, source_grid)
    return (source,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## Retained and escaped critical outputs

    The escaped output is plotted on a finite negative interval. That plot does not integrate its infinite tail.
    """)
    return


@app.cell
def _(
    L,
    critical_kernel,
    escaped_output,
    np,
    r_grid,
    retained_output,
    source,
    source_grid,
):
    y_grid = np.linspace(0.0, r_grid[-1] + L, 1800)
    K = critical_kernel(y_grid)
    critical_retained = retained_output(source_grid, source, y_grid, K)
    critical_escaped = escaped_output(source_grid, source, r_grid, y_grid, K)
    return critical_escaped, critical_retained


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## Check the critical factorization

    Compare the explicit kernel against the ordered Euler, Γ and polar factors.
    """)
    return


@app.cell
def _(
    critical_retained,
    finite_completed_output_product,
    gamma_steps,
    l2_norm,
    source,
    source_grid,
):
    critical_product = finite_completed_output_product(
        0.5, source_grid, source, gamma_y_steps=gamma_steps
    )
    critical_difference = l2_norm(critical_product - critical_retained, source_grid)
    print(f"||critical product output - critical kernel output|| = {critical_difference:.3e}")
    return (critical_product,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## Differentiate the energy

    Inspect the two completed outputs before taking the centered finite difference.
    """)
    return


@app.cell
def _(
    finite_completed_output_product,
    gamma_steps,
    h,
    l2_norm,
    source,
    source_grid,
):
    minus = finite_completed_output_product(
        0.5 - h, source_grid, source, gamma_y_steps=gamma_steps
    )
    plus = finite_completed_output_product(
        0.5 + h, source_grid, source, gamma_y_steps=gamma_steps
    )

    energy_minus = l2_norm(minus, source_grid) ** 2
    energy_plus = l2_norm(plus, source_grid) ** 2
    retained_derivative = (energy_plus - energy_minus) / (2.0 * h)
    return (retained_derivative,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## Compare with the Weil form

    The opposite escaped-energy derivative is a prediction of the paper’s theorem here, not an independently differentiated escaped-tail calculation.
    """)
    return


@app.cell
def _(
    critical_product,
    retained_derivative,
    source_grid,
    weil_form_same_vector,
):
    weil_direct = weil_form_same_vector(critical_product, source_grid, y_steps=2200)

    print(f"d/ds retained energy at 1/2 = {retained_derivative:+.8e}")
    print(f"direct localized Weil form  = {weil_direct:+.8e}")
    print(f"difference                  = {retained_derivative - weil_direct:+.8e}")
    print(f"The theorem predicts escaped-energy derivative = {-retained_derivative:+.8e}")
    return (weil_direct,)


@app.cell
def _(critical_escaped, r_grid):
    negative_t = -r_grid[::-1]
    negative_values = critical_escaped[::-1]
    return negative_t, negative_values


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## Plot 1

    Change the plotting code here to inspect another aspect of the same calculation. The figure is displayed inline; no SVG is overwritten.
    """)
    return


@app.cell
def _(L, critical_retained, negative_t, negative_values, np, plt, source_grid):
    __figure = plt.figure(figsize=(9, 4.5))
    plt.plot(negative_t, np.real(negative_values), label='escaped output')
    plt.plot(source_grid, np.real(critical_retained), label='retained output')
    plt.axvline(0.0)
    plt.axvline(L)
    plt.xlabel('t')
    plt.ylabel('completed output')
    plt.title('The critical full-line output splits at the finite boundary')
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
def _(plt, retained_derivative, weil_direct):
    __figure_1 = plt.figure(figsize=(8, 4.5))
    _labels = ['retained derivative', 'direct Weil form']
    _values = [retained_derivative, weil_direct]
    plt.bar(_labels, _values)
    plt.ylabel('value')
    plt.title('Numerical check: retained source-Gram derivative = Weil form')
    plt.tight_layout()
    plt.close(__figure_1)
    __figure_1
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## Things to try

    - Vary h while keeping the quadrature fixed; look for an error floor.
    - Increase source and Γ grids together before attributing discrepancies to h.
    - Change the source while keeping it frozen across the two parameter values.
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
    ### `trapezoid`

    Reference: `common.py:36`.
    """)
    return


@app.cell
def _(np):
    def trapezoid(values: np.ndarray, grid: np.ndarray) -> complex:
        """Integrate sampled values over a one-dimensional grid."""

        return np.trapezoid(values, grid)

    return (trapezoid,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ### `l2_norm`

    Reference: `common.py:42`.
    """)
    return


@app.cell
def _(np, trapezoid):
    def l2_norm(values: np.ndarray, grid: np.ndarray) -> float:
        """Discrete approximation to the L2 norm on a one-dimensional grid."""

        return float(np.sqrt(np.real(trapezoid(np.conjugate(values) * values, grid))))

    return (l2_norm,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ### `interpolate_complex`

    Reference: `common.py:48`.
    """)
    return


@app.cell
def _(np):
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

    return (interpolate_complex,)


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
    ### `killed_shift_samples`

    Reference: `common.py:261`.
    """)
    return


@app.cell
def _(interpolate_complex, np):
    def killed_shift_samples(
        grid: np.ndarray,
        values: np.ndarray,
        y: float,
        L: float,
    ) -> np.ndarray:
        """Sample S_y f(t)=f(t+y), with zero outside (0,L)."""

        shifted_points = grid + y
        return interpolate_complex(shifted_points, grid, values, left=0.0, right=0.0)

    return (killed_shift_samples,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ### `volterra_resolvent`

    Reference: `common.py:273`.
    """)
    return


@app.cell
def _(np, trapezoid):
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

    return (volterra_resolvent,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ### `critical_kernel_scalar`

    Reference: `common.py:293`.
    """)
    return


@app.cell
def _(math):
    def critical_kernel_scalar(y: float) -> float:
        """Theorem 1 critical half-line kernel K(y)."""

        if y < 0.0:
            return 0.0
        A = math.exp(y)
        m = math.floor(A)
        theta = A - m
        return math.pi * math.exp(-2.5 * y) * m * (m + 1) * (1.0 - 2.0 * theta)

    return (critical_kernel_scalar,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ### `critical_kernel`

    Reference: `common.py:304`.
    """)
    return


@app.cell
def _(critical_kernel_scalar, np):
    def critical_kernel(grid: np.ndarray) -> np.ndarray:
        """Vectorized wrapper for the critical kernel."""

        return np.array([critical_kernel_scalar(float(y)) for y in grid], dtype=float)

    return (critical_kernel,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ### `retained_output`

    Reference: `common.py:379`.
    """)
    return


@app.cell
def _(interpolate_complex, np, trapezoid):
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

    return (retained_output,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ### `escaped_output`

    Reference: `common.py:396`.
    """)
    return


@app.cell
def _(interpolate_complex, np, trapezoid):
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

    return (escaped_output,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ### `correlation_same_vector`

    Reference: `common.py:418`.
    """)
    return


@app.cell
def _(killed_shift_samples, np, trapezoid):
    def correlation_same_vector(
        values: np.ndarray,
        grid: np.ndarray,
        y: float,
    ) -> float:
        """q_{f,f}(y)=<f,(S_y+S_y*)f> for sampled f."""

        shifted = killed_shift_samples(grid, values, y, float(grid[-1]))
        inner = trapezoid(np.conjugate(values) * shifted, grid)
        return float(2.0 * np.real(inner))

    return (correlation_same_vector,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ### `weil_form_same_vector`

    Reference: `common.py:430`.
    """)
    return


@app.cell
def _(correlation_same_vector, math, np, trapezoid, von_mangoldt_table):
    def weil_form_same_vector(values: np.ndarray, grid: np.ndarray, y_steps: int=1200) -> float:
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
            polar = polar + 2.0 * math.cosh(y / 2.0) * q
            denominator = math.exp(y) - math.exp(-y)
            rho = math.exp(y / 2.0) / denominator
            archimedean = archimedean + (rho * q - 2.0 * norm_squared / denominator)
        polar = polar * width
        archimedean = archimedean * width
        max_n = math.ceil(x) - 1
        mangoldt = von_mangoldt_table(max_n)
        prime = 0.0
        for n in range(2, max_n + 1):
            if n < x and mangoldt[n] != 0.0:
                prime = prime + mangoldt[n] / math.sqrt(n) * correlation_same_vector(values, grid, math.log(n))
        return polar - c_L * norm_squared - archimedean - prime

    return (weil_form_same_vector,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ### `finite_euler_output`

    Reference: `common.py:900`.
    """)
    return


@app.cell
def _(killed_shift_samples, math, np):
    def finite_euler_output(s: float, grid: np.ndarray, source_values: np.ndarray) -> np.ndarray:
        """Apply Z_L(s)=sum_{n<e^L} n^{-s} S_{log n} to sampled data."""
        L = float(grid[-1])
        x = math.exp(L)
        result = np.zeros_like(source_values, dtype=complex)
        for n in range(1, math.ceil(x)):
            if n < x:
                result = result + n ** (-s) * killed_shift_samples(grid, source_values, math.log(n), L)
        return result

    return (finite_euler_output,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ### `finite_gamma_output`

    Reference: `common.py:919`.
    """)
    return


@app.cell
def _(killed_shift_samples, math, np):
    def finite_gamma_output(s: float, grid: np.ndarray, values: np.ndarray, y_steps: int=500) -> np.ndarray:
        """Apply the finite-window Gamma-ratio operator E_{infty,L}(s)."""
        L = float(grid[-1])
        alpha = (2.5 - s) / 2.0
        prefactor = 2.0 * math.pi ** alpha / math.gamma(alpha)
        result = np.zeros_like(values, dtype=complex)
        width = L / y_steps
        for j in range(y_steps):
            y = (j + 0.5) * width
            scalar = prefactor * math.exp(-s * y) * (1.0 - math.exp(-2.0 * y)) ** (alpha - 1.0)
            result = result + scalar * killed_shift_samples(grid, values, y, L) * width
        return result

    return (finite_gamma_output,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ### `finite_completed_output_product`

    Reference: `common.py:946`.
    """)
    return


@app.cell
def _(finite_euler_output, finite_gamma_output, np, volterra_resolvent):
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

    return (finite_completed_output_product,)


if __name__ == "__main__":
    app.run()
