import marimo

__generated_with = "0.24.2"
app = marimo.App()


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    # 04. The completed critical kernel

    Build the arithmetic floor/fractional-part kernel, remove its envelope, and inspect its L¹ diagnostic.

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

    return dataclass, math, mo, np, plt


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
        'y_max': mo.ui.number(start=1.0, stop=10.0, step=0.5, value=10.0, debounce=True, label='y_max'),
        'points': mo.ui.number(start=1000, stop=24000, step=1000, value=12000, debounce=True, label='points'),
        'precision': mo.ui.dropdown(options=["float64", "mp50", "mp100", "mp200"], value='float64', label='Precision profile'),
    })
    controls
    return (controls,)


@app.cell
def _(controls):
    settings = controls.value
    return (settings,)


@app.cell
def _(PrecisionChoice, np, settings):
    precision = PrecisionChoice(name=settings["precision"], dps=None if settings["precision"] == "float64" else int(settings["precision"][2:]))
    y_max = settings["y_max"]
    y = np.linspace(0.0, y_max, int(settings["points"]))
    return precision, y, y_max


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## Evaluate K

    The scalar and vectorized kernel definitions below are editable cells. Integer thresholds are visible in the plots.
    """)
    return


@app.cell
def _(critical_kernel, y):
    K = critical_kernel(y)
    return (K,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## Compare with the analytic upper bound

    The integral stops at y_max; the bound applies to the full half-line. The high-precision routine integrates separate arithmetic panels.
    """)
    return


@app.cell
def _(K, math, np, precision, y, y_max):
    if precision.uses_mpmath:
        absolute_integral = mp_completed_kernel_l1(y_max, dps=precision.dps)
        print(f"precision profile           = {precision.name}")
        print(f"truncated integral |K(y)| dy    = {absolute_integral}")
    else:
        absolute_integral = np.trapezoid(np.abs(K), y)
        print("precision profile           = float64")
        print(f"truncated integral |K(y)| dy    = {absolute_integral:.12f}")

    theoretical_bound = 8.0 * math.pi / 3.0
    print(f"theoretical L1 bound       = {theoretical_bound:.12f}")
    return


@app.cell
def _(K, math, np, y):
    mask = y <= math.log(30.0)
    r = np.exp(y[mask])
    K_r = K[mask]
    return K_r, r


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## Plot 1

    Change the plotting code here to inspect another aspect of the same calculation. The figure is displayed inline; no SVG is overwritten.
    """)
    return


@app.cell
def _(K, math, plt, y):
    __figure = plt.figure(figsize=(9, 4.5))
    plt.plot(y, K)
    for _n in range(2, 20):
        _location = math.log(_n)
        if _location <= y[-1]:
            plt.axvline(_location, alpha=0.15)
    plt.xlabel('y')
    plt.ylabel('K(y)')
    plt.title('Critical completed kernel with arithmetic thresholds y = log n')
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
def _(K, math, np, plt, y):
    __figure_1 = plt.figure(figsize=(9, 4.5))
    plt.plot(y, np.exp(2.5 * y) * K / math.pi)
    plt.xlim(0.0, 4.0)
    plt.xlabel('y')
    plt.ylabel('exp(5y/2) K(y) / pi')
    plt.title('Removing the exponential envelope exposes the arithmetic sawtooth')
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
def _(K_r, plt, r):
    __figure_2 = plt.figure(figsize=(9, 4.5))
    plt.plot(r, K_r)
    plt.xlabel('r = exp(y)')
    plt.ylabel('K(log r)')
    plt.title('The same kernel in multiplicative coordinates')
    plt.tight_layout()
    plt.close(__figure_2)
    __figure_2
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## Things to try

    - Zoom below y=4 to inspect individual log(n) jumps.
    - Compare the grid L¹ diagnostic with mp50 panel integration.
    - Edit the kernel cell and observe which envelope or cancellation is lost.
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


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ### `kernel_antiderivative`

    Reference: `high_precision.py:65`.
    """)
    return


@app.function
def kernel_antiderivative(y, n, mp):
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


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ### `mp_completed_kernel_l1`

    Reference: `high_precision.py:80`.
    """)
    return


@app.function
def mp_completed_kernel_l1(y_max, dps: int=50):
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
        zero = mp.log(mp.mpf(n) + mp.mpf('0.5'))
        F_left = kernel_antiderivative(left, n, mp)
        F_right = kernel_antiderivative(right, n, mp)
        if zero <= left or zero >= right:
            total = total + abs(F_right - F_left)
        else:
            F_zero = kernel_antiderivative(zero, n, mp)
            total = total + (abs(F_zero - F_left) + abs(F_right - F_zero))
    return total


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
