# Weil form operators

Companion repository for **An operator-theoretic representation of the Weil
quadratic form**.

[Read the paper](paper/weil-form-operators.pdf) ·
[Lean theorem map](verification/THEOREM_MAP.md) ·
[Python experiments](experiments/README.md)

The paper constructs completed arithmetic translation operators, identifies the
localized Weil form through their logarithmic derivative and boundary leakage,
and derives the finite Fourier matrix used in the CCM characteristic construction.
The repository supplies the paper PDF, its precisely scoped Lean counterparts,
and numerical experiments.

## Contents

- **paper/** — the paper PDF, revised 15 September 2026 with the Suzuki
  comparison; Typst sources remain with the author.
- **verification/** — the full paper-linked Lean source snapshot, pinned
  dependencies, theorem map, exact declaration types and archived audit evidence.
- **experiments/** — twelve numerical demonstrations, including an optional
  arbitrary-precision ladder.

## Check the Lean development

Install [elan](https://github.com/leanprover/elan), then run:

```sh
cd verification
lake exe cache get
lake build
python3 audit/check.py
python3 audit/check.py --compiled
```

`lean-toolchain` pins Lean 4.32.1. `lake-manifest.json` pins mathlib and its
transitive dependencies. Keep the lockfile; no dependency update is needed.
The existing `Riemann` namespace is retained so exported proof sources stay
byte-identical. See [verification/README.md](verification/README.md).

## Run the experiments

Install [uv](https://docs.astral.sh/uv/getting-started/installation/), then run
from the repository root:

```sh
uv sync --locked
uv run --locked python experiments/smoke_test.py
uv run --locked python experiments/run_all.py
```

uv manages `.venv` automatically; activation is unnecessary. `.python-version`
selects Python 3.10, and `uv.lock` records the resolved dependencies. The project
supports Python 3.10–3.13 with the current numerical package pins.
To include the precision ladder, use
`uv run --locked python experiments/run_all.py --include-precision-ladder`.
Figures and diagnostic tables are generated locally. Higher precision is not
certified interval arithmetic. Numerical agreement does not prove a theorem.

## Editable notebooks

Each experiment also has an editable [marimo playground](experiments/notebooks/README.md).
The calculations, plots and numerical helper definitions are separate visible
cells. You can change the algorithms locally without modifying the CLI scripts.

```sh
uv sync --locked --group notebooks
uv run --locked --group notebooks marimo edit experiments/notebooks/playground_01_logarithmic_translation.py
```

The notebooks are optional; the existing commands above do not require marimo.
To compare every notebook's defaults with its original script, run
`uv run --locked --group notebooks python scripts/test_notebooks.py`. After intentional distribution edits,
`uv run --locked python scripts/update_manifest.py` refreshes payload hashes while retaining the
frozen Lean and original-Python source checks.

## Verification scope

The theorem map distinguishes compiled declarations from mathematical arguments
provided only in the paper. In particular, this snapshot does not formalize the
holomorphic family, global Gram stationarity, leakage/trace-class identities,
repaired interpolation, or the conditional moving-limit argument. It does
formalize the listed finite arithmetic, finite-window current/range, finite CCM,
and fixed critical half-line results under their exact hypotheses.

## Citation and licenses

Citation metadata is in [CITATION.cff](CITATION.cff).
Code, configuration and accompanying documentation are licensed under
[Apache-2.0](LICENSE), except where otherwise indicated. The paper PDF is
licensed under [CC BY 4.0](paper/LICENSE). Third-party dependencies retain their
own licenses. Attribution and source references are retained in the Lean files.
