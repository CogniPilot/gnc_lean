# Derivations

Derivation documents that accompany the application proofs. Each entry names
the document, what it derives, and the GNC modules whose statements it
motivates. The documents are the mathematical source for the formalized
results; the Lean modules remain the checked artifact, and a derivation is not
itself a verified claim.

| Document | Derives | Related modules |
| --- | --- | --- |
| [Mixed-invariant preintegration error theory](mixed_invariant_preintegration_error_theory.pdf) | Exact truncation residuals for mixed-invariant preintegration on the time-extended SE2(3): the Magnus exponent's T^4 grade vanishes for a linear generator, the exact T^5 residual has rational coefficients -1/240 and -1/720, the two-sample coning correction is shown adequate at flight rates with explicit crossovers, the corrections enter the exponent of the exact closed form, and a delayed-fusion error-state filter is built on the result. | [Preintegration](../../GNC/Applications/Preintegration.lean), [Magnus](../../GNC/Applications/Magnus.lean), [Nilpotent](../../GNC/Applications/Nilpotent.lean), [EquivariantFilter](../../GNC/Applications/EquivariantFilter.lean) |

## Formalization ledger: mixed-invariant preintegration error theory

The application module [PreintegrationErrorTheory](../../GNC/Applications/PreintegrationErrorTheory.lean)
names every proved item of the paper by its paper label and points at the
checked declaration. The general mathematics lives in the modules listed in
the last column. Where the Lean statement differs from the paper's wording
the difference is recorded here and in the alias docstring.

| Paper item | Lean declaration | Module | Deviation |
| --- | --- | --- | --- |
| Prop. 1, ZOH closed form (5)-(7) | `Preintegration.closed_form_spatial` | Preintegration/ClosedForm | none |
| Lemma 1, right and left stems, parity map | `exponent5_flow_coeff`, `exponent5Left_flow_coeff`, `parity`, `lemma1_right_coefficient` | Magnus/MagnusJet, Magnus/LeftConventionJet, Magnus/SimplexMoments | formal jet through degree five; analytic convergence is separate |
| Lemma 2, T^4 grade vanishes | `linear_degree_four`, `left_linear_degree_four`, `lemma2_cancellation` | same | none |
| Lemma 3, exact T^5 residual, Table II | `linear_degree_five`, `left_linear_degree_five`, `remark2_confirmation` | same | none |
| Cor. 1, residual bound (12) | `norm_residual5_le` | Magnus/ResidualBound | bounds the exact degree-five term, no O(T^6) tail |
| Lemma 4, splitting commutes with the hold | `peel_left`, `exists_mixed_flows` | Magnus/MagnusAlgebra, Magnus/MagnusFlow | none |
| Prop. 2, extended commutator (14), two-step ideal | `extended_commutator`, `ideal_commutator`, `ideal_triple_commutator` | Magnus/MagnusAlgebra | none |
| Eq. (15), coning, sculling, scrolling | `foh_commutator` | Magnus/MagnusAlgebra | none |
| Cor. 2, exact termination without rotation | `exp_fohExponent`, `exp_foh_increment_no_rotation`, `foh_flow_no_rotation_unique` | Magnus/FOHIncrement | abstract hypothesis: all triple products vanish; instantiated for the SE2(3) ideal |
| Thm. 1, increment (16) | `foh_increment` | Magnus/FOHIncrement | none |
| Thm. 1, error bound (17) | `foh_truncation_error`, `norm_exp_sub_exp_le` | Magnus/ExponentialPerturbation | needs a norm-one unit (true for matrices) |
| Prop. 3, relative residual (18) | `relative_residual` | Magnus/ResidualBound | exact bookkeeping; (19) is an estimate and is not formalized |
| Prop. 4, bias Jacobians (20)-(23) | `foh_bracket_bias_derivative`, `rotation_bias_derivative`, `velocity_bias_derivative` | Magnus/FOHIncrement, Magnus/MagnusInputs | recursion (24) not formalized |
| Thm. 2, interpolation error | `linear_error_le_bound`, `lipschitz_linear_error_le_bound` | Analysis/HoldInterpolation | derivatives given pointwise on the closed interval |
| Thm. 3, flow sensitivity (26)-(28) | `attitude_sensitivity`, `translation_sensitivity` | Analysis/FlowSensitivity | operator-norm distance in place of the bi-invariant distance; orthogonality as norm-one hypotheses |
| Lemma 5, composition | `norm_ofFn_prod_sub_le` | Analysis/FlowSensitivity | norm-one factors |
| Thm. 4, per-second bound (29) | `rotational_residual_le`, `per_second_bound` | Magnus/ResidualBound, Analysis/FlowSensitivity | the degree-six Magnus tail is an explicit hypothesis, not an order symbol |
| Prop. 5, online certificate (30) | `certificate` | Analysis/HoldInterpolation | none |
| Prop. 6, centered hold (31)-(32) | `centeredHold_pos`, `exponent5_flow_coeff`, `prop6_pairwise_coefficients`, `prop6_triple_coefficient` | Magnus/CenteredHold, Magnus/MagnusJet, Magnus/SimplexMoments | none |
| Prop. 7, bias invariance and (33) | `centered_bias_invariant`, `centeredRotationIncrement_bias_derivative` | Magnus/MagnusInputs, Magnus/CenteredHold | (33) is the Jacobian of the increment truncated after the displayed brackets |
| Thm. 5, quadratic error (34), gain (35), noise weights | `quadratic_error_le_bound`, `interpolation_gain`, `integral_centeredHold`, `centered_weight_variance` | Analysis/HoldInterpolation, Magnus/CenteredHold | variances are stated as weight sums of squares |
| Thm. 6, exact reapplication (36)-(37) | `reapplication`, `flow_factors_state_independent`, `corrected_flow` | Magnus/MagnusAlgebra, Magnus/ReapplicationRemainder | none |
| Prop. 8, second-order remainder (38) | `second_order_remainder`, `horizon_constant_le` | Magnus/ReapplicationRemainder | the curvature bound 2 T_D^2 on the body velocity is a hypothesis; velocity-channel remainder not formalized |
| Sec. IV-D(ii), trapezoid noise correlation | `trapezoid_cross_covariance`, `trapezoid_telescope_variance_sum` | Magnus/CenteredHold | weight identities |
| Sec. XIII, Simpson exactness on cubics | `simpson_exact_cubic` | Magnus/CenteredHold | none |
| Prop. 9, shipped coning term | `uniform_coning_stencil` | Magnus/MagnusInputs | uniform slope, as in the paper |
| Cor. 3, sampling crossovers | `crossover_half_mrad_freq`, `crossover_two_mrad_freq` | Magnus/ResidualBound | from the measured ratios 1.77e-5 and 6.60e-5 and h^2 scaling |
| Cor. 3, body-rate crossover | `crossover_body_rate` | Magnus/ResidualBound | the (1/60)(‖ω‖h)^2 term gives 1235 to 1245 rad/s; the paper's 1252 rad/s is not reproduced |
| Appendix A, block product | `extended_commutator` | Magnus/MagnusAlgebra | none |
| Appendix B, simplex moments | `simplex3_t1` and companions | Magnus/SimplexMoments | none |

Not formalized, by nature: Remark 8 (Galilean tangent-group lift, numerical
only in the paper), the recursion (24), the estimate (19), Lemma 6 and the
Part II measurement Jacobians (implementation audits), all measured tables
and figures, and the Corollary 3 ratios 1.77e-5 and 6.60e-5 themselves,
which are harness measurements.
