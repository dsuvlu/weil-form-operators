# Weil form operators

Four draft articles on completed arithmetic operators, the Weil
quadratic form, causal response and finite spectral selection.

## Papers

Current drafts: **24 September 2026**.

| Paper | PDF 
|---|---|
| I | [An operator-theoretic representation of the Weil quadratic form](paper/weil-form-operators.pdf)
| II | [θ correlations and a causal range criterion for the Weil form](paper/theta-correlations-causal-range.pdf)
| III | [Arithmetic reconstruction and endpoint regularity of the completed ζ response](paper/arithmetic-reconstruction-endpoint-regularity.pdf)
| IV | [Constant-mode transfer and compactness criteria for finite Weil characteristics](paper/finite-weil-constant-mode-transfer.pdf)

**Animated reading of Paper I.** [Weil’s Boundary Response](animation/index.html)
walks through six scenes of the paper: logarithmic shifts, the non-closable
echo, the completed kernel, leakage at the window edge, the finite Fourier
matrix and finite characteristics. It is a single self-contained web page. GitHub
shows HTML files as source, so open it from a local clone in a browser, or
through GitHub Pages if Pages is enabled for this repository.

## The four-paper story

The common construction runs from arithmetic translations through Γ and polar
completion to the critical Weil response. It then branches:

```text
                   I · Completed arithmetic operators
                  /                                  \
       II · Sign, causality and Hankel range       IV · Finite spectral selection
                  |                                    and zero retention
       III · The causal arithmetic response
```

**Paper I: completion and localization.** Logarithmic coordinates turn
multiplication into translation. Completing the arithmetic family produces a
bounded convolution operator and a holomorphic parameter family. The functional
equation makes the full-line squared output norm stationary at the critical
parameter. On a fixed interval, retained and escaped energies have opposite first
variations: the localized Weil form on completed outputs is the negative
leakage-energy derivative, with the source fixed. The paper also derives the
complete finite Fourier matrix and expresses the same pairing through a
difference of projections associated with the unitary used in Paper II.

**Paper II: what the sign means.** An explicit θ probability law realizes the
positive-rate response kernel through one compact self-adjoint correlation
operator. Positivity of every finite rate matrix is equivalent to positivity of
that operator, then to one-sided causality and actual range membership
$b_*\in\operatorname{Ran}H_b$ for a distinguished source under a compact Hankel
operator. Membership in the closure of the range is insufficient. These rate
matrices are different from Paper IV's finite Fourier matrices.

**Paper III: constructing the response.** A weighted causal solution $q_c$ is
built from logarithmic prime delays and exact finite Möbius inversion. It is
Paper II's ordinary Hankel preimage precisely when $q_c\in L^2(0,\infty)$;
at that endpoint its squared norm is $1/2$. Here $\kappa(t)=e^{-t}$. The Euler-edge response
$g=e^{-t/2}(q_c+\kappa)$ has Gevrey-2 moment bounds and a stretched-exponential
weight. The distinguished source belongs to every positive fractional-power range below the
first power and none above it. For the original Hankel operator, regularized
inverse energy grows at most as the square root of $1+\log(1/\lambda)$, with a
further Gevrey improvement. These bounds still allow divergence. A genuine-pole-free half-plane extending left of the Euler edge gives a positive
exponential weight after a loss of width; the existence of that gap remains open.

**Paper IV: finite characteristics and their limits.** The finite real-zero
construction of Connes–Consani–Moscovici supplies the starting point under full
selection hypotheses. For integer carriers $x_j\to\infty$, consider a family
with a simple full least eigenvalue, an even ground state and the stated endpoint
and anchor normalizations at every member. If its **complete characteristic mean** is uniformly bounded,
then the normalized characteristics are locally bounded and have nonzero entire
clusters. The mean includes the untouched Fourier lattice, so it also forces the
Fourier resolution needed in the moving argument: no separate cutoff schedule
is required. Constant-mode transfer makes the complete filtered energy
Gaussian-small without a uniform excitation gap. The arithmetic current passage
then gives $E_j\to0$ and retention of every zero of
$\Xi(z)=\xi(1/2+iz)$ in every cluster. This is zero-value retention, not exact
identification with normalized $\Xi$. An appendix expresses the mean premise
equivalently through two hyperbolic-source energies; it does not prove that bound.

## What remains open

The two branches have distinct unresolved premises:

- **Half-line branch:** ordinary square-integrability of the constructed causal
  response, equivalently actual membership of $b_*$ in $\operatorname{Ran}H_b$.
- **Finite branch:** existence of an unbounded fully selected family with
  uniformly bounded complete characteristic mean on that same family.

The finite hypotheses would yield a nonzero entire cluster with only real zeros
that retains all zeros of $\Xi$, giving a conditional RH implication. Neither
hypothesis is established here, and Paper IV does not assume the unresolved sign
or range condition of Papers II–III.

“Critical noncollapse” describes a shared structural problem: preserve a
particular arithmetic source or normalized observable despite singular spectral
geometry. For the half-line branch this is an actual compact-operator range
question; for the finite branch it is compactness with arithmetic zero retention.
It is not a theorem equating the two conditions.

## Contents

- **paper/** — the four current draft PDFs; Typst sources are not copied here.
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
The [illustrated experiment guide](experiments/README.md) shows every figure with
its explanation; `run_all.py` regenerates the figures byte for byte. Diagnostic
tables are generated locally. Higher precision is not certified interval
arithmetic. Numerical agreement does not prove a theorem.

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

The Lean distribution and theorem map retain their frozen Paper I scope.
The new projection bridge, response estimates and two-source criterion are
written-proof results, not newly Lean-verified results. The existing
`RELEASE_MANIFEST.json`, validation receipts and `paper/README.md` describe
the earlier distribution; their PDF/README hashes and draft metadata have
not been regenerated for this PDF-and-README update.

The theorem map distinguishes compiled declarations from mathematical arguments
provided only in the paper. In particular, this snapshot does not formalize the
holomorphic family, global Gram stationarity, leakage/trace-class identities,
repaired interpolation, or the conditional moving-limit argument. It does
formalize the listed finite arithmetic, finite-window current/range, finite CCM,
and fixed critical half-line results under their exact hypotheses.

## Citation and licenses

The existing [CITATION.cff](CITATION.cff) describes the earlier Paper I release;
use the titles and draft versions above for the current manuscripts.
Code, configuration and accompanying documentation are licensed under
[Apache-2.0](LICENSE), except where otherwise indicated. The paper PDFs are
licensed under [CC BY 4.0](paper/LICENSE). Third-party dependencies retain their
own licenses. Attribution and source references are retained in the Lean files.
