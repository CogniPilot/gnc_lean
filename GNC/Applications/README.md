# Application proofs

All formalizations associated with the papers are part of GNC. Import
`GNC.All` for the complete mathematical development, `GNC.Applications`
for the application aggregate, or an individual module below.

| Application module | Paper |
| --- | --- |
| [LogLinOrbit](LogLinOrbit.lean) | Orbital prediction |
| [Pointing-cap certificates](OrbitalComparison/PointingCapCertificate.lean), [quartic threshold](OrbitalComparison/PointingCapQuartic.lean) | Full-gravity finite-burn bounds and the physical polynomial-degree barrier |
| [Reachable pointing-cap images](OrbitalComparison/PointingCapReachable.lean), [set bounds](OrbitalComparison/PointingCapSetBounds.lean) | Hausdorff error and conditional physical clearance |
| [Optimized cap records](OrbitalComparison/HornerGraph.lean) | Matched graph optimization and independently checked physical coefficients |
| [Terminal support and clearance](OrbitalComparison/PointingCapSupportBounds.lean) | Computed physical support intervals and matched polynomial certificates |
| [Orion propulsion and pointing](Orion/PointingDisturbance.lean) | Public-data propulsion and synthetic controller contracts |
| [MotorBurn](MotorBurn/Bounds.lean) | Full-gravity, variable-mass burn/coast input enclosures |
| [Rendezvous](Rendezvous.lean) | Two-impulse planning |
| [Preintegration](Preintegration.lean) | Closed-form preintegration |
| [PreintegrationErrorTheory](PreintegrationErrorTheory.lean) | Exact error theory for mixed-invariant preintegration: FOH and centered-hold exponents, truncation residuals, interpolation and flow-sensitivity bounds, reapplication remainder (ledger in [docs/derivations](../../docs/derivations/README.md)) |
| [Nilpotent](Nilpotent.lean) | Mixed nilpotent summation |
| [Magnus](Magnus.lean) | Magnus extension |
| [Backstepping](Backstepping.lean) | Aircraft control |
| [DynamicInversion](DynamicInversion.lean) | Log-linear dynamic inversion |
| [EquivariantFilter](EquivariantFilter.lean) | Equivariant filtering |
| [TwoFrameScalings](TwoFrameScalings.lean) | Two-frame groups with scalings |
| [OrbitalFuel](OrbitalFuel.lean) | Orbital fuel and uncertainty |

## Derivations

Derivation documents behind the application proofs live in
[docs/derivations](../../docs/derivations/README.md).

| Derivation | Related application modules |
| --- | --- |
| [Mixed-invariant preintegration error theory](../../docs/derivations/mixed_invariant_preintegration_error_theory.pdf): exact Magnus truncation residuals on the time-extended SE2(3), the coning sufficiency bound, and the delayed-fusion error-state filter | [Preintegration](Preintegration.lean), [Magnus](Magnus.lean), [Nilpotent](Nilpotent.lean), [EquivariantFilter](EquivariantFilter.lean) |

General mathematics may not import these applications. Application modules
may reuse one another when a proof requires it. Every mathematical source
must be exported by `GNC.All`, and every declaration is included in the
[verification audit](../../docs/VERIFICATION.md), including declarations
outside the GNC namespace. Source module and declaration namespace need not
have identical hierarchies.

The manuscripts and their coverage ledgers live in the companion papers
repository. Those ledgers preserve explicit assumptions, counterexamples and
unfinished paper obligations. Moving the proofs into one library does not discharge
those obligations or turn numerical examples into universal certificates.
