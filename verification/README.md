# Lean verification

This is the full frozen source snapshot referenced by the paper, with **131
implementation modules plus the aggregate**. No source from the parent research
repository is needed to build it. The namespace remains `Riemann`.

## Build and audit

With elan installed, from this directory:

```sh
lake exe cache get
lake build
python3 audit/check.py
python3 audit/check.py --compiled
```

Use the committed `lean-toolchain`, `lakefile.toml` and `lake-manifest.json`.
Do not run `lake update` to reproduce the snapshot. The first command retrieves
pinned dependencies and the official mathlib build cache; the default build
compiles the project aggregate. No compiled project files are distributed.

The static audit checks every source and configuration hash, import reachability,
forbidden proof constructs, and the preserved archived evidence. The compiled
audit runs Lean's transitive axiom collector over every compiled project
namespace declaration, including private declarations, and checks the complete
elaborated namespace inventory against the archived snapshot. It rejects custom
axioms, unsafe declarations, and any transitive axiom outside `propext`,
`Classical.choice`, and `Quot.sound`. Fresh logs go to ignored `audit/latest/`.

## Read the mathematics

[THEOREM_MAP.md](THEOREM_MAP.md) maps the article to precise declarations and
records which article statements are outside the compiled coverage.
[DECLARATION_TYPES.json](DECLARATION_TYPES.json) records the mapped elaborated
types. `SNAPSHOT.json` and `audit/archived/source-hashes.json` identify the sources.

`audit/archived/` preserves earlier source-bound audit evidence verbatim. Names
and temporary paths in that historical evidence are provenance, not standalone
build dependencies. The distribution audit summary is in [audit/distribution/axiom-summary.json](audit/distribution/axiom-summary.json), with its build log alongside it.
