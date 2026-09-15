# Computational experiments

These scripts are a readable computational companion to **An operator-theoretic representation of the Weil quadratic form**.

The default path uses familiar NumPy/Matplotlib calculations.  A small optional `mpmath` layer lets the same core calculations be repeated at higher precision when a reader wants to inspect stability or cancellation.

## Dependencies

[uv](https://docs.astral.sh/uv/getting-started/installation/) manages the Python
environment. From this directory or the repository root, run:

```sh
uv sync --locked
```

The base environment contains NumPy, Matplotlib and mpmath. Python 3.10 is the
default; Python 3.10–3.13 is supported by the current dependency pins. Run scripts
with `uv run --locked python ...`; no environment activation is needed.

For an existing pip workflow, `python -m pip install -r requirements-lock.txt`
remains available from this directory. The requirements files are preserved
compatibility snapshots; `../pyproject.toml` and `../uv.lock` govern uv.

There is no SciPy, SymPy, pandas, seaborn, JAX, or project-specific runtime dependency.

## Precision ladder

The default is intentionally ordinary double precision:

```text
float64  -> fast NumPy calculation and all plots
mp50     -> 50 decimal digits
mp100    -> 100 decimal digits
mp200    -> 200 decimal digits
```

For experiments that support it:

```bash
uv run --locked python experiment_08_ground_selection.py --precision mp50
uv run --locked python experiment_09_finite_characteristic.py --precision mp100
uv run --locked python experiment_07_fourier_matrix.py --dps 80
```

A custom `--dps N` overrides the named profile.

The higher-precision path is deliberately small and explicit.  It lives in:

```text
precision.py       command-line precision profiles
high_precision.py  readable mpmath versions of the delicate formulas
```

The float64 implementation remains in `common.py`.  Some duplication between `common.py` and `high_precision.py` is intentional: the two versions are easier to audit side by side than a clever generic numerical-backend abstraction.

### What uses higher precision?

Higher precision is most useful for:

- the completed-kernel integral,
- the explicit finite Weil matrix,
- least-eigenline selection,
- the finite characteristic,
- the small exploratory moving family.

Experiments whose point is an exact finite arithmetic identity or a visual theorem illustration remain simple NumPy code.  More digits would not make those demonstrations more informative.

### What this ladder is *not*

`mpmath` gives arbitrary precision, not proof-certified interval arithmetic.  This repository does not attempt rigorous ball arithmetic or large-scale certification.  If a later project needs proof-grade numerical bounds, an Arb/python-flint layer should be a separate package rather than complicating these teaching examples.

## Experiments

1. `experiment_01_logarithmic_translation.py`  
   Demonstrates `S_log(m) S_log(n) = S_log(mn)` and the logarithmic placement of arithmetic nodes.

2. `experiment_02_finite_euler_algebra.py`  
   Builds the terminating Euler product in the finite shift algebra, verifies its Möbius inverse, and verifies that the negative logarithmic derivative has von Mangoldt coefficients.

3. `experiment_03_absorbing_resolvent.py`  
   Visualizes the absorbing generator and checks `(b - A_L) R_b f = f` numerically.

4. `experiment_04_completed_kernel.py`  
   Plots the exact critical kernel
   `K(y) = pi exp(-5y/2) m(m+1)(1-2 theta)` and its arithmetic threshold structure.  In high-precision mode, the L1 diagnostic is integrated panel by panel with an exact antiderivative rather than generic quadrature.

5. `experiment_05_nonclosability.py`  
   Implements the manuscript's explicit nonclosability witness `f_T`, compares the raw critical synthesis with its nonzero limiting function, and shows the completed output becoming small.

6. `experiment_06_boundary_leakage.py`  
   Splits the exact critical full-line output into retained and escaped pieces.  For the parameter derivative it evaluates the finite-window completed family directly from the Euler, Gamma, and polar factors, then compares the retained energy derivative with a direct numerical evaluation of the localized Weil form.  This remains a readable float64 theorem visualization.

7. `experiment_07_fourier_matrix.py`  
   Constructs the finite Weil matrix two ways: directly from the localized form and from the arithmetic interpolation/divided-difference formula.  High-precision mode recomputes the explicit formula with mpmath while retaining the simple direct float64 quadrature as an independent route.

8. `experiment_08_ground_selection.py`  
   Diagonalizes a finite arithmetic Weil matrix, checks parity and boundary brightness, endpoint-normalizes the least eigenvector, and plots its physical and Fourier representations.  High-precision mode also reports the eigenpair residual.

9. `experiment_09_finite_characteristic.py`  
   Computes the finite characteristic from the selected Fourier transform and independently from the determinant ratio.  High precision is used for the scalar identity check; plots remain fast float64 renderings of the same finite object.

10. `experiment_10_range_vs_projection.py`  
    Illustrates the distinction between the literal absorbing range and its surjective projection onto a periodic finite Fourier section.

11. `experiment_11_moving_family.py`  
    Records a small **predetermined exploratory family** of finite carriers.  `--precision mp50` or higher can be used to check that the finite diagnostics are stable, but the family is intentionally modest and makes no limiting claim.

12. `experiment_12_precision_ladder.py`  
    Repeats one small admitted carrier at float64, 50, 100, and 200 decimal digits and prints a compact stabilization table.  This is the easiest place to see when extra precision matters and when it does not.

## Why the high-precision code is structured this way

Several practices make a bigger difference than merely asking for more digits:

- arithmetic support is kept exact with integer logic;
- the critical kernel is integrated between the known `log(n)` thresholds;
- prime, continuum, and Gamma pieces are assembled explicitly;
- the finite characteristic is evaluated primarily as an entire Fourier transform;
- the determinant formula is treated as an independent check away from its removable free-spectrum singularities;
- selected eigenvectors are checked by parity, endpoint brightness, spectral gap, and residual.

These are structural choices, not performance tricks.

## Status language

The scripts should be read with four distinct statuses:

- **Numerical check of an exact finite identity:** floating-point agreement illustrates the algebra; it is not an exact-arithmetic certificate.
- **Theorem visualization:** the analytic theorem is proved in the paper; the script only illustrates it.
- **Finite diagnostic:** a statement about one chosen `(x,N)` pair.
- **Exploratory moving experiment:** finite data along a predetermined family, with no compactness or convergence conclusion.

Numerical agreement is not a substitute for the analytic arguments or the remaining moving-limit mathematics.

## Generated figures

Figures are written to `figures/` as SVG files.  

## Reproduction and provenance

Run from this directory:

```sh
uv run --locked python smoke_test.py
uv run --locked python run_all.py
uv run --locked python run_all.py --include-precision-ladder
```

The Python files are byte-identical to the supplied precision-ladder archive.
`source-hashes.json` records each script. `PROVENANCE.md` identifies the archive
and the packaging changes. `requirements.txt` pins the three direct numerical
packages; `requirements-lock.txt` preserves the original tested pip environment.
The repository-root `uv.lock` is the maintained cross-platform dependency lock.
Generated figures and diagnostic CSV files are excluded from the source release.
Experiment 11 is exploratory; it does not establish moving spectral convergence.
The optional notebook regression test is described below.

## Editable marimo playgrounds

[Open the notebook guide](notebooks/README.md) for one playground per experiment.
Their cells expose the calculations and copied numerical method definitions;
plots render inline. Editing a notebook does not change the original scripts.

From the repository root:

```sh
uv sync --locked --group notebooks
uv run --locked --group notebooks marimo edit experiments/notebooks/playground_04_completed_kernel.py
```

The original smoke test and `run_all.py` remain available with the original
numerical dependencies. Marimo is an optional additional dependency.
