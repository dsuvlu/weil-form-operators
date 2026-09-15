# Editable experiment playgrounds

Each notebook develops one experiment through visible Python cells: parameters,
intermediate arrays or coefficients, numerical diagnostics, plots, and the
underlying method definitions. You can edit a test function, replace a quadrature
rule, inspect a matrix, or change the eigensolve. No notebook invokes another
script or hides its computation behind a subprocess.

## Open a playground

From the repository root, with [uv](https://docs.astral.sh/uv/getting-started/installation/) installed:

```sh
uv sync --locked --group notebooks
uv run --locked --group notebooks marimo edit experiments/notebooks/playground_01_logarithmic_translation.py
```

The `notebooks` dependency group adds marimo to the base numerical environment.
Keep `--group notebooks` on notebook commands so uv includes that group.

Use **`marimo edit`** to see and change code. `marimo run` gives an app view and
is less useful for inspecting the calculations. To browse all notebooks, run
`uv run --locked --group notebooks marimo edit` from this directory and select a file in the notebook browser.

Start with the defaults. Change a control, or edit a cell and run it; marimo
recomputes its dependents. The numerical controls use debounce so typing a
number does not rerun an expensive calculation at every keystroke. For larger
experiments, marimo's lazy execution mode lets you choose when to run stale cells.

The parameter dictionary is a separate cell. The calculation cells expose
intermediate values, so you can add another cell to inspect, for example,
`H_formula`, `residual`, or `projection_matrix`. The **Numerical method definitions**
section at the end contains editable definitions of every project helper used
by that notebook. Marimo resolves those dependencies before their uses.

## Choose an experiment

| Notebook | What you can inspect and change |
|---|---|
| [01 — Logarithmic translation](playground_01_logarithmic_translation.py) | Test profile, two arithmetic shifts, interpolation grid, killed boundary |
| [02 — Finite Euler algebra](playground_02_finite_euler_algebra.py) | Coefficient dictionaries, terminating product, Möbius inverse, current |
| [03 — Absorbing resolvent](playground_03_absorbing_resolvent.py) | Input profile, finite Volterra integral, derivative stencil, residual |
| [04 — Completed kernel](playground_04_completed_kernel.py) | Floor/fractional-part formula, arithmetic panels, envelope and L¹ diagnostic |
| [05 — Nonclosability witness](playground_05_nonclosability.py) | Indicator width, translation sequence, raw sums, completed output |
| [06 — Boundary leakage](playground_06_boundary_leakage.py) | Frozen source, factorized output, finite-difference step, direct Weil pairing |
| [07 — Fourier matrix](playground_07_fourier_matrix.py) | Interpolation and direct integration routes, diagonal entries, numerical precision |
| [08 — Ground selection](playground_08_ground_selection.py) | Full eigensolve, parity, gap, endpoint normalization |
| [09 — Finite characteristic](playground_09_finite_characteristic.py) | Fourier and determinant formulas, off-real comparison point, complex-plane grid |
| [10 — Range and projection](playground_10_range_vs_projection.py) | Terminal taper, projected columns, singular values, periodic ground |
| [11 — Exploratory family](playground_11_moving_family.py) | Editable carrier list, anchor normalization, diagnostic table and CSV download |
| [12 — Precision ladder](playground_12_precision_ladder.py) | Fixed carrier, repeated matrix/eigensolve, 50/100/200-digit comparisons |

Plots appear inline and do not overwrite the scripts' SVG files. Notebook 11
provides a download button for its current table. To save a plot, add a cell
calling `figure.savefig(...)` on a figure you give a public name in its plot cell.

## Relationship to the scripts

The original `experiment_*.py`, `common.py`, `high_precision.py`, and `precision.py`
are unchanged. `uv run --locked python experiments/run_all.py` and the existing smoke test work
as before, without installing marimo.

The notebooks deliberately contain **editable copies** of the small numerical
methods they need. This makes an algorithm change local to a playground rather
than changing the command-line baseline. `NOTEBOOK_MAP.json` identifies the
corresponding script, default parameters, and the original location of each
copied helper. A few leading underscores are removed from helper names because
marimo uses them to designate cell-local variables. There is no automatic
regeneration that overwrites notebook edits.

For an exploratory fork, copy a notebook to a new filename before editing.
The reference regression tests compare the distributed playground defaults with
the original scripts; an intentional change of calculation may naturally stop
matching that reference. The scripts remain independently runnable.

## Check and export

From the repository root:

```sh
uv run --locked --group notebooks marimo check --strict experiments/notebooks/playground_*.py
uv run --locked --group notebooks python scripts/test_notebooks.py
```

The tests execute every notebook, compare its default numerical outputs with
the matching original script, check plot counts, and exercise changed parameters
and arbitrary-precision branches. They do not certify the numerical results.

A local HTML export includes the code and computed outputs:

```sh
mkdir -p experiments/notebooks/exports
uv run --locked --group notebooks marimo export html experiments/notebooks/playground_04_completed_kernel.py \
  -o experiments/notebooks/exports/kernel.html
```

An HTML export is a static snapshot; use the Python notebook for recomputation.
Notebook caches and local exports are ignored by Git.

The mathematical qualifications belong with each experiment. In particular,
finite-grid checks are not proofs, arbitrary precision is not interval arithmetic,
and the moving-family playground establishes no convergence or RH conclusion.
