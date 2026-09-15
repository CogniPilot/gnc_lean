# GNC for Lean

A formally verified mathematical library for **guidance, navigation and control**, using released Lean
4.29.1 and mathlib v4.29.1. It includes Lie groups, mixed-invariant dynamics,
preintegration, Magnus algebra, nonlinear control, estimation, reachability
and orbital fuel certificates.

Every project `.lean` file lives under [GNC/](GNC/README.md).
`import GNC.All` exports the complete mathematical development, including
all paper applications. The exact-rational CLI is separate in `GNC/Tools/`. `import GNC.Core`
selects the general mathematics. Individual modules can also be imported.
Application proofs live in [GNC/Applications/](GNC/Applications/README.md).
The manuscripts, reviews, coverage ledgers, experiment programs and their
current figures and data live in a separate papers repository that consumes
this library as a submodule.

All theorem declarations are checked by Lean's kernel under their stated
hypotheses, with no admitted proofs or additional project axioms. The
[verification contract](docs/VERIFICATION.md) specifies this claim and its
limits. The [current verification record](docs/verification/README.md)
identifies the checked source snapshot. This does not claim that every
statement in every original paper, numerical simulation or physical vehicle
has been completely verified.

## Reproduce

```sh
nix develop
gnc-cache
lake build
python scripts/verify.py
```

The flake pins the official Lean compiler, released mathlib and every
transitive Lake dependency. No global elan installation or separate mathlib
checkout is needed.
`nix develop` materializes pinned sources in `.lake/packages` and writes the
path-based `lake-manifest.json`. Update dependencies through the flake;
do not run `lake update`.

`gnc-cache` fetches the released compiled dependency artifacts. After cache
setup, the proof build needs no dependency downloads. GNC reuses mathlib's
theorems directly. The first setup requires network access and several GB.
`nix build` alone builds the Lean compiler; `lake build` builds and audits
the proof library. The verification command uses Lake's incremental cache and runs the complete
axiom audit, source-coverage checks and planner interface checks. Checked project
proofs and build traces persist in `.lake/build`; released dependency artifacts
persist under `.lake/packages`. Lake rebuilds affected modules when sources,
imports, build options or the toolchain change. Keep these ignored directories
between sessions. An unchanged `lake build` reuses the checked proofs.

For an explicit clean verification, use
`nix develop --command python scripts/verify.py --fresh`. This rebuilds every
project module in an isolated directory and installs the successful build
into `.lake/build`, so subsequent commands reuse it.

```sh
nix develop --command python scripts/check_structure.py
nix develop --command python scripts/verify.py --check-report .lake/verification/report.json
```

The second command checks snapshot correspondence; it does not rerun proofs.

## Applications and papers

Notable results and limits are described in the [library overview](GNC/README.md),
and the [application index](GNC/Applications/README.md) links each proof
aggregate. The [library design](docs/LIBRARY_DESIGN.md) explains the separation
between general mathematics and applications and the proposed mathlib
contribution plan.

The manuscripts, adversarial reviews, coverage ledgers and experiment programs
live in a separate papers repository that includes this library as a submodule
and builds the documents and numerical experiments against these proofs.

## Repository layout

- `GNC/`: every project Lean source; general mathematics, applications and verification tooling.
- `docs/`: library design and the current verification record.
- `scripts/`: Python setup, verification and repository checks.
- `nix/`, `flake.nix`, `flake.lock`: reproducible environment and Lean toolchain.

`.lake/`, `.direnv/`, Python caches and Nix `result*` links are ignored.
Nix output links point to `/nix/store`; they are build artifacts, not source
files. Keep new output links under `.lake/`, or pass `--no-link`.

## License

GNC for Lean is licensed under the Apache License, Version 2.0. See
[LICENSE](LICENSE) and [NOTICE](NOTICE) for details. Copyright 2026 CogniPilot
Foundation.

The library reuses [mathlib](https://github.com/leanprover-community/mathlib4),
which is also distributed under the Apache License, Version 2.0, as a
dependency.
