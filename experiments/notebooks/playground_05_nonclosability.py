import marimo

__generated_with = "0.24.2"
app = marimo.App()


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    # 05. A raw graph-defect sequence

    Follow the explicit small-input sequence, its nonzero raw output limit, and its completed image.

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
        'd': mo.ui.number(start=0.25, stop=1.5, step=0.25, value=1.0, debounce=True, label='d'),
        'T_max': mo.ui.number(start=4, stop=8, step=1, value=8, debounce=True, label='T_max'),
        'points': mo.ui.number(start=1000, stop=10000, step=1000, value=7000, debounce=True, label='points'),
    })
    controls
    return (controls,)


@app.cell
def _(controls):
    settings = controls.value
    return (settings,)


@app.cell
def _(settings):
    d = settings["d"]
    T_values = list(range(3, int(settings["T_max"])+1))
    points = int(settings["points"])
    return T_values, d, points


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## Arithmetic prefix sums

    Inspect how a translated indicator becomes a finite interval sum of n⁻¹ᐟ².
    """)
    return


@app.cell
def _(T_values, d, math, np):
    max_integer = int(math.exp(max(T_values) + d)) + 2
    prefix = np.zeros(max_integer + 1)
    for n in range(1, max_integer + 1):
        prefix[n] = prefix[n - 1] + n ** (-0.5)
    return max_integer, prefix


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## Integrate the completed kernel

    This grid antiderivative is an approximation; increase its resolution by editing the cell.
    """)
    return


@app.cell
def _(T_values, critical_kernel, d, np):
    y_grid = np.linspace(0.0, max(T_values) + d + 1.0, 50000)
    K = critical_kernel(y_grid)
    K_antiderivative = np.zeros_like(y_grid)
    K_antiderivative[1:] = np.cumsum(
        0.5 * (K[:-1] + K[1:]) * np.diff(y_grid)
    )


    def integral_K(a, b):
        if b <= a:
            return 0.0
        Fa = np.interp(a, y_grid, K_antiderivative)
        Fb = np.interp(b, y_grid, K_antiderivative)
        return Fb - Fa

    return (integral_K,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## Apply both operators to each input

    The error integral below is truncated at T+d. The nonzero limiting exponential also has a tail beyond that interval; these finite diagnostics are not the full analytic nonclosability proof.
    """)
    return


@app.cell
def _(T_values, d, integral_K, math, max_integer, np, points, prefix):
    input_norms = []
    raw_norms = []
    completed_norms = []
    limit_errors = []

    for T in T_values:
        t = np.linspace(0.0, T + d, points)
        scale = math.exp(-T / 2.0)

        raw = np.zeros_like(t)
        for i, ti in enumerate(t):
            lower = max(1, math.ceil(math.exp(T - ti)))
            upper = min(max_integer, math.floor(math.exp(T + d - ti)))
            if upper >= lower:
                raw[i] = scale * (prefix[upper] - prefix[lower - 1])

        limit = 2.0 * (math.exp(d / 2.0) - 1.0) * np.exp(-t / 2.0)

        completed = np.zeros_like(t)
        for i, ti in enumerate(t):
            a = max(0.0, T - ti)
            b = max(0.0, T + d - ti)
            completed[i] = scale * integral_K(a, b)

        input_norms.append(math.sqrt(d * math.exp(-T)))
        raw_norms.append(math.sqrt(np.trapezoid(raw * raw, t)))
        completed_norms.append(math.sqrt(np.trapezoid(completed * completed, t)))
        limit_errors.append(math.sqrt(np.trapezoid((raw - limit) ** 2, t)))
    return completed_norms, input_norms, limit_errors, raw_norms


@app.cell
def _(T_values, completed_norms, input_norms, limit_errors, raw_norms):
    print('T    ||f_T||       ||Zf_T||      ||Xf_T||      ||Zf_T-g||')
    for (_T, _a, _b, _c, _e) in zip(T_values, input_norms, raw_norms, completed_norms, limit_errors):
        print(f'{_T:>3.0f}  {_a:12.4e}  {_b:12.4e}  {_c:12.4e}  {_e:12.4e}')
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## Plot 1

    Change the plotting code here to inspect another aspect of the same calculation. The figure is displayed inline; no SVG is overwritten.
    """)
    return


@app.cell
def _(T_values, completed_norms, input_norms, plt, raw_norms):
    __figure = plt.figure(figsize=(8, 4.5))
    plt.semilogy(T_values, input_norms, marker='o', label='||f_T||')
    plt.semilogy(T_values, raw_norms, marker='o', label='||Z_+(1/2) f_T||')
    plt.semilogy(T_values, completed_norms, marker='o', label='||X_+ f_T||')
    plt.xlabel('T')
    plt.ylabel('L2 norm')
    plt.title('Raw synthesis retains a nonzero limit while the input vanishes')
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
def _(T_values, limit_errors, plt):
    __figure_1 = plt.figure(figsize=(8, 4.5))
    plt.semilogy(T_values, limit_errors, marker='o')
    plt.xlabel('T')
    plt.ylabel('||Z f_T - g||')
    plt.title('Convergence of the raw synthesis to the explicit nonzero limit')
    plt.tight_layout()
    plt.close(__figure_1)
    __figure_1
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## Things to try

    - Change the indicator width d and compare the raw limiting scale.
    - Inspect the ceil/floor boundaries in the raw arithmetic sum.
    - Add the limiting exponential’s remaining tail integral to the displayed error diagnostic.
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


if __name__ == "__main__":
    app.run()
