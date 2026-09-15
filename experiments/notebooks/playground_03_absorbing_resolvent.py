import marimo

__generated_with = "0.24.2"
app = marimo.App()


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    # 03. Absorbing Volterra resolvent

    Check the directed derivative +d/dt and the terminal boundary condition in (b−A)R_b f=f.

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

    return mo, np, plt


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
        'L': mo.ui.number(start=0.5, stop=5.0, step=0.25, value=3.0, debounce=True, label='L'),
        'b': mo.ui.number(start=-1.0, stop=3.0, step=0.1, value=1.3, debounce=True, label='b'),
        'points': mo.ui.number(start=200, stop=4000, step=200, value=1600, debounce=True, label='points'),
    })
    controls
    return (controls,)


@app.cell
def _(controls):
    settings = controls.value
    return (settings,)


@app.cell
def _(np, settings):
    L = settings["L"]
    b = settings["b"]
    t = np.linspace(0.0, L, int(settings["points"]))
    return L, b, t


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## The input and its Volterra integral

    Change the input profile or edit the integration routine below.
    """)
    return


@app.cell
def _(L, b, np, t, volterra_resolvent):
    f = 1.0 + 0.25 * np.cos(2.0 * np.pi * t / L)
    R = volterra_resolvent(t, f, b)
    return R, f


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## Differentiate and measure the residual

    The reported maximum omits five grid points at each end to separate interior finite-difference error from endpoint stencils.
    """)
    return


@app.cell
def _(R, b, f, np, t):
    R_derivative = np.gradient(R, t)
    residual = b * R - R_derivative - f

    print(f"R_b f at the absorbing endpoint: {R[-1]:.3e}")
    print(f"max residual in (b-A)R_b f=f: {np.max(np.abs(residual[5:-5])):.3e}")
    return (residual,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## Plot 1

    Change the plotting code here to inspect another aspect of the same calculation. The figure is displayed inline; no SVG is overwritten.
    """)
    return


@app.cell
def _(L, R, f, np, plt, t):
    __figure = plt.figure(figsize=(8, 4.5))
    plt.plot(t, f, label='f')
    plt.plot(t, np.real(R), label='R_b f')
    plt.axvline(L)
    plt.xlabel('t')
    plt.ylabel('value')
    plt.title('The Volterra resolvent integrates backward from the absorbing endpoint')
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
def _(np, plt, residual, t):
    __figure_1 = plt.figure(figsize=(8, 4.5))
    plt.plot(t, np.real(residual))
    plt.xlabel('t')
    plt.ylabel('residual')
    plt.title('Numerical check of (b - A_L) R_b f = f')
    plt.tight_layout()
    plt.close(__figure_1)
    __figure_1
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## Things to try

    - Try negative b: the finite interval integral still exists.
    - Double the grid resolution to examine the interior residual.
    - Change the sign of the derivative in the residual and compare.
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


if __name__ == "__main__":
    app.run()
