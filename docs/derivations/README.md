# Derivations

Derivation documents that accompany the application proofs. Each entry names
the document, what it derives, and the GNC modules whose statements it
motivates. The documents are the mathematical source for the formalized
results; the Lean modules remain the checked artifact, and a derivation is not
itself a verified claim.

| Document | Derives | Related modules |
| --- | --- | --- |
| [Mixed-invariant preintegration error theory](mixed_invariant_preintegration_error_theory.pdf) | Exact truncation residuals for mixed-invariant preintegration on the time-extended SE2(3): the Magnus exponent's T^4 grade vanishes for a linear generator, the exact T^5 residual has rational coefficients -1/240 and -1/720, the two-sample coning correction is shown adequate at flight rates with explicit crossovers, the corrections enter the exponent of the exact closed form, and a delayed-fusion error-state filter is built on the result. | [Preintegration](../../GNC/Applications/Preintegration.lean), [Magnus](../../GNC/Applications/Magnus.lean), [Nilpotent](../../GNC/Applications/Nilpotent.lean), [EquivariantFilter](../../GNC/Applications/EquivariantFilter.lean) |
