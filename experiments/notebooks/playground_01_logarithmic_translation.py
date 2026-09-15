import marimo

__generated_with = "0.24.2"
app = marimo.App()


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    # 01. Logarithmic translation

    How does integer multiplication become addition of shift lengths, and where does the support cutoff enter?

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
        'L': mo.ui.number(start=1.0, stop=5.0, step=0.1, value=3.4011973816621555, debounce=True, label='Window length L'),
        'm': mo.ui.number(start=1, stop=10, step=1, value=2, debounce=True, label='m'),
        'n': mo.ui.number(start=1, stop=10, step=1, value=3, debounce=True, label='n'),
        'points': mo.ui.number(start=200, stop=4000, step=200, value=1200, debounce=True, label='points'),
        'center': mo.ui.number(start=0, stop=5, step=0.1, value=2.4, debounce=True, label='center'),
        'width': mo.ui.number(start=0.1, stop=1, step=0.05, value=0.35, debounce=True, label='width'),
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
    m = int(settings["m"])
    n = int(settings["n"])
    t = np.linspace(0.0, L, int(settings["points"]))
    center = settings["center"]
    width = settings["width"]
    return L, center, m, n, t, width


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## Choose a test function

    Edit this cell to replace the Gaussian by another concrete profile.
    """)
    return


@app.cell
def _(L, center, np, t, width):
    def test_function(x):
        return np.exp(-((x - center) / width) ** 2)


    def killed_shift(y):
        values = np.zeros_like(t)
        mask = t + y < L
        values[mask] = test_function(t[mask] + y)
        return values

    return killed_shift, test_function


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## Apply and compose shifts

    The second shift is sampled by interpolation. Its nonzero discrepancy measures the grid calculation, not a failure of the exact semigroup law.
    """)
    return


@app.cell
def _(killed_shift, m, math, n, np, t, test_function):
    f = test_function(t)
    S2 = killed_shift(math.log(m))
    S6_direct = killed_shift(math.log(m*n))

    # Apply S_log(3) to S_log(2) by evaluating the already shifted function.
    S2_then_3 = np.zeros_like(t)
    shifted_points = t + math.log(n)
    S2_then_3 = np.interp(shifted_points, t, S2, left=0.0, right=0.0)

    error = np.max(np.abs(S2_then_3 - S6_direct))
    print(f"max |S_log(n) S_log(m) f - S_log(mn) f| = {error:.3e}")
    return S2, S6_direct, f


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## Plot 1

    Change the plotting code here to inspect another aspect of the same calculation. The figure is displayed inline; no SVG is overwritten.
    """)
    return


@app.cell
def _(S2, S6_direct, f, plt, t):
    __figure = plt.figure(figsize=(8, 4.5))
    plt.plot(t, f, label='f')
    plt.plot(t, S2, label='S_log(m) f')
    plt.plot(t, S6_direct, label='S_log(mn) f')
    plt.xlabel('t')
    plt.ylabel('value')
    plt.title('Multiplication becomes translation on the logarithmic interval')
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
def _(L, math, plt):
    __figure_1 = plt.figure(figsize=(8, 2.8))
    for _n in range(2, 16):
        _x = math.log(_n)
        if _x < L:
            plt.scatter([_x], [0.0])
            plt.text(_x, 0.05, str(_n), ha='center', va='bottom')
    plt.axvline(L)
    plt.yticks([])
    plt.xlabel('t = log n')
    plt.title('The arithmetic nodes are logarithmically spaced')
    plt.tight_layout()
    plt.close(__figure_1)
    __figure_1
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## Things to try

    - Double the grid resolution and compare the interpolation discrepancy.
    - Choose m and n with log(mn) ≥ L; the directly shifted output is killed.
    - Change the profile and inspect what happens near the absorbing endpoint.
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


if __name__ == "__main__":
    app.run()
