# Verification contract

The supported claim is:

> GNC is a formally verified mathematical library for guidance, navigation
> and control. All its theorem declarations are checked by Lean's kernel
> against released mathlib, under their stated hypotheses, with no admitted
> proofs or additional project axioms.

For publication, use the statement above and attach a successful verification
record that matches the released source tree. An unqualified claim that
“the entire GNC software stack is fully verified” would exceed the evidence.

When a shorter description is needed, use **“GNC's mathematical theorems are
fully formally verified in Lean, under their stated assumptions.”** Link this
contract and the matching verification record. Avoid shortening this to
“everything in GNC is fully verified”: a defined algorithm can occur in a
checked module without a theorem establishing its complete intended behavior.

“Fully verified” should always refer to this mathematical scope. It must not
imply that every source paper is completely formalized, every executable
function has a correctness specification, or an aircraft is certified safe.
The theorem statement is the specification that has been proved. Choosing
the right specification and establishing its hypotheses for a physical
application require additional work.

## Enforced checks

Run the release check from the repository root:

```sh
nix develop --command python scripts/verify.py
```

The command checks the pinned dependency source copies, the import graph,
the complete Lake build, a fresh axiom audit, rejection tests for the audit,
and planner interface regressions. Lake reuses checked `.olean` files in
`.lake/build` when its source, import, option and toolchain traces match;
changed inputs cause the affected modules to rebuild. The report records
how many module outputs were reused and recompiled. It writes logs and a
dated, source-hashed report to `.lake/verification/`, fails if the source
changes during the check, and replaces a previous success report with a
running/failed status when appropriate. The report is an attestation produced
by build tooling; the proof terms themselves are checked by Lean.

Use `nix develop --command python scripts/verify.py --fresh` for an explicit
clean verification. This isolated build starts with no project proof
artifacts and reuses only the released dependency cache. After the complete
build, audit and regressions pass, it installs the checked artifacts into
`.lake/build`. The previous cache remains in place until then. Routine
verification uses Lake's incremental cache; neither `lake clean` nor repeated
clean rebuilds are required to retain the formal verification guarantee.

The default flake shell sets `LEAN_NUM_THREADS=2` to limit concurrent Lake
compiler processes. Some finite rational certificates require substantial
memory; this avoids launching them all at once on a build from source.
To serialize compiler work on a smaller machine, use
`nix develop --command env LEAN_NUM_THREADS=1 python scripts/verify.py`.
The same environment override applies to `lake build` and `--fresh`.
It changes scheduling, not the certificate, proof obligations or Lake's
source/dependency cache checks. With pinned Lake/Lean 4.29.1, an independent
six-module build probe observed one and two concurrent compiler processes
for settings one and two respectively.

Every project `.lean` file is under `GNC/`. `GNC.All` exports all mathematics,
including `GNC.Applications`. The planner CLI in `GNC/Tools/` is audited
separately so the mathematics import does not define an application entry
point. `GNC.Core` selects general results. The build covers every application certificate as well as every
general theorem; an explicit fresh build rechecks them all from source.
Audit/report tooling is in `GNC/Verification/` under the `Verification` module
namespace; it is part of the build trust boundary.

The report includes a machine-readable audit of the complete build. Lean's
actual loaded-module inventory is compared with every mathematical source file, including modules without declarations. A file
cannot escape coverage because it was omitted from an aggregate import or
mentioned only in a comment. Audit-policy and planner regressions run
against that completed build. Cache regression tests also verify unchanged
build reuse, cache transfer between directories, rejection of a theorem
invalidated by a dependency edit, and rebuilding after its correction while
unrelated proofs remain cached.

The [audit policy](../GNC/Verification/Policy.lean) selects **all declarations
originating in GNC mathematical modules**, including private declarations and
declarations in other namespaces. It also selects declarations in the GNC
namespace originating elsewhere. It follows dependencies through
Lean's checked environment, including the types and bodies of definitions,
instances and theorems. It rejects:

- Any unproved project axiom, even if unused.
- Dependencies on `sorryAx`, `native_decide` axioms, or any foundation beyond
  `propext`, `Classical.choice` and `Quot.sound`.
- User unsafe/partial definitions and project `implemented_by`/foreign-code
  replacements without a proved correspondence.

Lean generates partial runtime companions for ordinary total recursive
definitions. The audit recognizes companions paired with a safe kernel
definition of the same type and source module, audits their axiom
dependencies, and reports their count separately. Theorems concern the total
kernel definitions. This is not a proof of the Lean compiler or its runtime.

The [structure check](../scripts/check_structure.py) ensures every library
module is exported by `GNC.All`, rejects project Lean files outside `GNC/`,
checks import cycles, and prevents core imports from application models. The
[negative tests](../scripts/check_audit.py) deliberately introduce admitted
proofs, extra/private axioms, namespace escapes, unsafe/partial code, runtime
replacements and native evaluation in temporary modules. A failed test must
contain the audit diagnostic; an unrelated syntax error cannot pass it.
These cases include admissions in definition bodies, definition types and
opaque declarations. Separate [release regression tests](../scripts/check_release.py)
check missing application exports, misplaced Lean files, core-to-application imports, and stale records after
changed, removed or newly added files.

For a complete library build and audit:

```sh
nix develop --command lake build Verification
```

`lake build GNC` alone builds the mathematics but does not run the audit.
`nix flake check --no-build` checks flake evaluation, not mathematical proofs.

## What remains outside the claim

The orbital Lie-STT experiment checks full physical trajectory bounds and the
transfer from its offline polynomial surrogate to the factored SE2(3)
exponential-map output. The accepted certificate covers the mathematical
predictor with stored rational representations of rounded coefficients.
It does not verify binary64 evaluation of the final query or its
transcendental functions. Expression-graph FLOPs and certificate-proposer
rational-operation counts are reproducible measurements, not kernel-proved
compiler-cost theorems. The stronger exact-direction Cartesian comparators
are included in the same library and experiment; formal acceptance does not
assert that a Lie-coordinate predictor is always more accurate or cheaper.

| Object | Meaning of verification |
| --- | --- |
| GNC theorems | Kernel-checked mathematical statements with explicit hypotheses. Local chart, regularity, positive-definiteness, bounded-input and existence hypotheses remain part of the contract. |
| Executable polynomial kernel and septic Hermite interpolator | Universal correctness proofs connect exact arithmetic to polynomial evaluation and actual real derivatives. The general endpoint solver also has an eight-coefficient uniqueness proof. |
| Complete Dubins/offset planner | Not complete: candidate selection, global optimality, piecewise gluing and other obligations are listed in the [planning ledger](../GNC/Planning/README.md). |
| Aircraft/orbit applications | Conditional theorems and selected concrete certificates are checked. A complete disturbed-aircraft safety tube, operational mission safety and the new constant-attitude nonlinear fuel certificate remain open; the original ideal solar mission comparison has concrete certificates. |
| Python/Modelica simulations and plots | Reproducible numerical evidence; not a universal trajectory proof. Model identification and correspondence with an actual vehicle are separate obligations. |
| Rumoca translation | No verified Modelica-to-Lean translation exists here. Generated Lean must be related both to source-language semantics and to the verified specification. |
| Compiled execution | Lean/compiler/runtime, external numeric libraries, floating-point rounding and transcendental evaluation are not proved correct by the arithmetic theorems. |

The companion papers repository indexes the individual coverage ledgers.
Their open obligations do not invalidate the proved library theorems, but
they prevent claims that the original papers or complete physical systems
have all been verified. An audit cannot establish that hypotheses are
physically appropriate, mutually satisfiable, or sufficient for an unstated
engineering objective. Those require theorem review and application proofs.

## Reproducibility and reporting

The flake pins official Lean 4.29.1, released mathlib v4.29.1 and every Lake
dependency. The release check verifies the selected Lean executable and the
dependency source paths against values supplied by the flake. It compares
copied Lean sources, toolchain files, package configurations and manifests
with their Nix-store originals before and after the build, detecting changes
even when a dependency's source stamp is unchanged. Existing mathlib results are
reused directly. See the [setup instructions](../README.md#reproduce).

The trusted computing base includes Lean's kernel and importer, the pinned
upstream compiled dependency artifacts, previously checked GNC artifacts,
and Lake and the build/audit tooling used to select and report the checked
source tree. An explicit fresh build rechecks GNC proofs without using
project artifacts; it does not independently recheck every imported mathlib
proof or verify Lean's implementation. Reproducibility is not a proof of
that tooling.

Report total mathematical-library counts and the application subset, by source module.
“Declarations” includes definitions, instances, constructors, recursors and
generated declarations. Even “theorem declarations” includes generated
equational lemmas; neither number is a count of theorems in the source papers.
Attach the source hash report when making a claim about a particular version.
Do not turn an old successful build into a claim about later untested changes.

Check that a successful report still describes the current sources with:

```sh
nix develop --command python scripts/verify.py --check-report .lake/verification/report.json
```

This compares the complete recorded set, detecting added and removed proof
files as well as edits. Hashes cover Lean sources, Python verification and
experiment scripts, Nix definitions (including paper experiment environments),
dependency manifests, the toolchain and this contract. The command checks
snapshot correspondence; it does not rerun proofs or authenticate a report's
provenance. PDFs, simulation result files and other prose documents are not
covered by the mathematical source attestation.
