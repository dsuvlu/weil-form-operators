import marimo

__generated_with = "0.24.2"
app = marimo.App()


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    # 02. Finite Euler algebra

    Inspect the coefficient dictionaries for Euler synthesis, its Möbius inverse, and the von Mangoldt current.

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
        'x': mo.ui.number(start=2.0, stop=100.0, step=1.0, value=30.0, debounce=True, label='Arithmetic cutoff x'),
        'sigma': mo.ui.number(start=-1.0, stop=2.0, step=0.05, value=0.75, debounce=True, label='Real part of s'),
        'tau': mo.ui.number(start=-2.0, stop=2.0, step=0.05, value=0.2, debounce=True, label='Imaginary part of s'),
    })
    controls
    return (controls,)


@app.cell
def _(controls):
    settings = controls.value
    return (settings,)


@app.cell
def _(settings):
    x = settings["x"]
    s = complex(settings["sigma"], settings["tau"])
    return s, x


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## Synthesis coefficients

    The product uses terminating geometric factors in the killed shift algebra.
    """)
    return


@app.cell
def _(
    derivative_of_synthesis,
    direct_euler_synthesis,
    euler_product_synthesis,
    mobius_inverse_coefficients,
    prime_current_coefficients,
    s,
    x,
):
    Z_direct = direct_euler_synthesis(x, s)
    Z_product = euler_product_synthesis(x, s)
    Z_inverse = mobius_inverse_coefficients(x, s)
    Z_derivative = derivative_of_synthesis(x, s)
    current_expected = prime_current_coefficients(x, s)
    return Z_derivative, Z_direct, Z_inverse, Z_product, current_expected


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## Multiply and differentiate

    Inspect the dictionaries directly; all reported errors are floating-point diagnostics for exact finite identities.
    """)
    return


@app.cell
def _(Z_derivative, Z_direct, Z_inverse, Z_product, current_expected, x):
    identity = multiply_shift_algebra(Z_product, Z_inverse, x)
    current_from_log_derivative = multiply_shift_algebra(Z_inverse, Z_derivative, x)
    current_from_log_derivative = {n: -c for n, c in current_from_log_derivative.items()}

    print("finite Euler product error:", maximum_dictionary_error(Z_direct, Z_product))
    print("finite inverse error:", maximum_dictionary_error(identity, {1: 1.0}))
    print(
        "logarithmic derivative error:",
        maximum_dictionary_error(current_from_log_derivative, current_expected),
    )
    return


@app.cell
def _(Z_direct, Z_inverse, current_expected, mo):
    mo.ui.table([{ "n": n, "Euler": str(Z_direct.get(n, 0)), "Möbius inverse": str(Z_inverse.get(n, 0)), "current": str(current_expected.get(n, 0))} for n in sorted(Z_direct)])
    return


@app.cell
def _(Z_direct, Z_inverse, current_expected, np):
    integers = np.array(sorted(Z_direct), dtype=int)
    z_magnitude = np.array([abs(Z_direct.get(int(n), 0.0)) for n in integers])
    mu_magnitude = np.array([abs(Z_inverse.get(int(n), 0.0)) for n in integers])
    current_magnitude = np.array([abs(current_expected.get(int(n), 0.0)) for n in integers])
    return current_magnitude, integers, mu_magnitude, z_magnitude


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## Plot 1

    Change the plotting code here to inspect another aspect of the same calculation. The figure is displayed inline; no SVG is overwritten.
    """)
    return


@app.cell
def _(integers, plt, z_magnitude):
    __figure = plt.figure(figsize=(9, 4.5))
    plt.stem(integers, z_magnitude, label='Euler synthesis')
    plt.xlabel('n')
    plt.ylabel('coefficient magnitude')
    plt.title('All integers appear in the finite Euler synthesis')
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
def _(integers, mu_magnitude, plt):
    __figure_1 = plt.figure(figsize=(9, 4.5))
    plt.stem(integers, mu_magnitude)
    plt.xlabel('n')
    plt.ylabel('coefficient magnitude')
    plt.title('The finite inverse carries Möbius signs and squarefree support')
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
def _(current_magnitude, integers, plt):
    __figure_2 = plt.figure(figsize=(9, 4.5))
    plt.stem(integers, current_magnitude)
    plt.xlabel('n')
    plt.ylabel('coefficient magnitude')
    plt.title('The logarithmic derivative isolates prime powers')
    plt.tight_layout()
    plt.close(__figure_2)
    __figure_2
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## Things to try

    - Move x across an integer and inspect which coefficients enter the strict support.
    - Edit multiply_shift_algebra to see why discarding products beyond the cutoff matters.
    - Inspect the prime-power support of the current alongside squarefree support of the inverse.
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
    ### `mobius_table`

    Reference: `common.py:112`.
    """)
    return


@app.cell
def _(np):
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
                        remaining = remaining // p
                        exponent = exponent + 1
                    if exponent >= 2:
                        square_factor = True
                        break
                    sign = sign * -1
                p = p + 1
            if square_factor:
                mu[n] = 0
            else:
                if remaining > 1:
                    sign = sign * -1
                mu[n] = sign
        return mu

    return (mobius_table,)


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
    ### `multiply_shift_algebra`

    Reference: `common.py:168`.
    """)
    return


@app.function
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


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ### `direct_euler_synthesis`

    Reference: `common.py:188`.
    """)
    return


@app.cell
def _(math):
    def direct_euler_synthesis(x: float, s: complex) -> dict[int, complex]:
        """Coefficients of sum_{n<x} n^{-s} V_n."""

        return {n: n ** (-s) for n in range(1, math.ceil(x)) if n < x}

    return (direct_euler_synthesis,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ### `euler_product_synthesis`

    Reference: `common.py:194`.
    """)
    return


@app.cell
def _(math):
    def euler_product_synthesis(x: float, s: complex) -> dict[int, complex]:
        """Build the same synthesis from the terminating prime Euler factors."""
        result: dict[int, complex] = {1: 1.0}
        for p in primes_below(math.ceil(x)):
            factor: dict[int, complex] = {}
            power = 1
            exponent = 0
            while power < x:
                factor[power] = p ** (-exponent * s)
                exponent = exponent + 1
                power = power * p
            result = multiply_shift_algebra(result, factor, x)
        return result

    return (euler_product_synthesis,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ### `mobius_inverse_coefficients`

    Reference: `common.py:210`.
    """)
    return


@app.cell
def _(math, mobius_table):
    def mobius_inverse_coefficients(x: float, s: complex) -> dict[int, complex]:
        """Coefficients of the finite Mobius inverse."""

        max_n = math.ceil(x) - 1
        mu = mobius_table(max_n)
        return {
            n: complex(mu[n]) * n ** (-s)
            for n in range(1, max_n + 1)
            if n < x and mu[n] != 0
        }

    return (mobius_inverse_coefficients,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ### `derivative_of_synthesis`

    Reference: `common.py:222`.
    """)
    return


@app.cell
def _(math):
    def derivative_of_synthesis(x: float, s: complex) -> dict[int, complex]:
        """Derivative d/ds of sum n^{-s} V_n."""

        return {
            n: -math.log(n) * n ** (-s)
            for n in range(2, math.ceil(x))
            if n < x
        }

    return (derivative_of_synthesis,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ### `prime_current_coefficients`

    Reference: `common.py:232`.
    """)
    return


@app.cell
def _(math, von_mangoldt_table):
    def prime_current_coefficients(x: float, s: complex) -> dict[int, complex]:
        """Coefficients Lambda(n) n^{-s}."""

        max_n = math.ceil(x) - 1
        mangoldt = von_mangoldt_table(max_n)
        return {
            n: mangoldt[n] * n ** (-s)
            for n in range(2, max_n + 1)
            if n < x and mangoldt[n] != 0.0
        }

    return (prime_current_coefficients,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ### `maximum_dictionary_error`

    Reference: `common.py:244`.
    """)
    return


@app.function
def maximum_dictionary_error(
    first: dict[int, complex],
    second: dict[int, complex],
) -> float:
    """Maximum absolute coefficient difference between two sparse dictionaries."""

    keys = set(first) | set(second)
    if not keys:
        return 0.0
    return max(abs(first.get(k, 0.0) - second.get(k, 0.0)) for k in keys)


if __name__ == "__main__":
    app.run()
