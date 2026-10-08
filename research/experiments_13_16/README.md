# Experiments 13–16

Optional research diagnostics, separate from the frozen twelve-experiment
release. **Numerical diagnostic, uncertified:** finite precision agreement does
not prove RH, a uniform mean bound or complete identification of zeros.

## Run

From the repository root, using Python 3.13:

```sh
python3.13 -m venv research/experiments_13_16/.venv
research/experiments_13_16/.venv/bin/python -m pip install -r research/experiments_13_16/requirements.txt
research/experiments_13_16/.venv/bin/python research/experiments_13_16/check_integrity.py
MPLBACKEND=Agg research/experiments_13_16/.venv/bin/python research/experiments_13_16/tests/test_reviewed.py
MPLBACKEND=Agg research/experiments_13_16/.venv/bin/python research/experiments_13_16/smoke.py
```

The isolated requirements pin python-flint 0.9.0 alongside the compatible release
stack; the root lockfile is unchanged. The bounded smoke covers small zeta, DH,
Lefschetz, surgery and matrix-identity cases. The dedicated CI runs these checks,
not full sweeps. The default release runner is unchanged.

For an individual experiment, use the isolated Python above:

```sh
python research/experiments_13_16/reviewed/experiment_13_characteristic_mean.py --x 5 --N 6 --max-dps 120 --no-plot
python research/experiments_13_16/reviewed/experiment_14_lefschetz_decomposition.py --x 13
python research/experiments_13_16/reviewed/experiment_15_davenport_heilbronn_control.py characteristic --x 20
python research/experiments_13_16/reviewed/experiment_16_arithmetic_localization.py cramer --x 50 --seeds 1 --T 30 --save
```

## Provenance and outputs

- `imported/` preserves original code, numerical results and figures byte-for-byte;
  historical captions and schemas are not reviewed conclusions. Use `reviewed/`
  for execution
- `reviewed/` reuses frozen release helpers without modifying them. New JSON/CSV
  and figures go only to ignored `generated/`
- [IMPORT_PROVENANCE.json](IMPORT_PROVENANCE.json) records archive and retained-file
  hashes. [RESEARCH_MANIFEST.json](RESEARCH_MANIFEST.json) independently hashes
  this research payload; it is outside the root release manifest's scope
- [results/reviewed_smoke.json](results/reviewed_smoke.json) is a compact numerical
  snapshot, with environment and reviewed-source hashes; full attempt records
  are generated when running smoke. Original results were not regenerated

## Essential caveats

Reviewed selection allows negative simple-even ground energy. Root/mean records
retain precision attempts, failures and complex roots, with residual and
root-by-root agreement checks. Nonfinite or unresolved roots cannot supply an
accepted real mean. These are approximate tests, not rigorous enclosures.
Experiment 14 remains aggregate-only; residue/decomposition modes remain
single-precision diagnostics. The sampled DH sign-change scan is incomplete.

The fixed `N ≈ 2 log(x)^2` family retains a nonzero lattice Gaussian contribution;
finite zero matches do not establish an exact Xi limit. Imported enriched JSON
schemas differ from the original generators. Full reviewed sweeps, global zero
counts and the remaining analytic estimates are not established by these checks.
