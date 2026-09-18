import GNC.Magnus.FOHIncrement
import GNC.Magnus.LeftConventionJet
import GNC.Magnus.ResidualBound
import GNC.Magnus.CenteredHold
import GNC.Magnus.SimplexMoments
import GNC.Magnus.ExponentialPerturbation
import GNC.Magnus.ReapplicationRemainder
import GNC.Analysis.HoldInterpolation
import GNC.Analysis.FlowSensitivity

/-! Ledger for "An Exact Error Theory for Mixed-Invariant Preintegration on
SE2(3)" (docs/derivations/mixed_invariant_preintegration_error_theory.pdf).
Each alias names a paper item and points at the checked statement. The
docstrings record every deviation from the paper's wording: operator norms
replace the bi-invariant distance, orthogonality enters as norm-one
hypotheses, and Magnus tails beyond the proved degree are explicit
hypotheses rather than order symbols. Items of the paper that are
measurements, implementation audits or numerical checks have no alias. -/
noncomputable section
namespace GNC.Applications.PreintegrationErrorTheory
open GNC.Magnus GNC.Analysis GNC.Hold

/-! ### Section II, Proposition 1 (ZOH closed form) -/

/-- Proposition 1: the closed-form mixed exponential, proved against
mathlib's matrix exponential for the actual SO(3) skew generators. -/
alias proposition1_zoh_closed_form := GNC.Preintegration.closed_form_spatial

/-! ### Section III-A, Lemmas 1 to 3 and Corollary 1 -/

/-- Lemma 1, right stem: the exponent of the right-composed flow through
degree five, kernel-matched against the flow coefficients; its degree-three
coefficient is +(1/12)[N0,N1]. -/
alias lemma1_right_stem := GNC.Magnus.exponent5_flow_coeff

/-- Lemma 1, left stem: the same matching for the left-composed flow, whose
degree-three coefficient is -(1/12)[N0,N1]. -/
alias lemma1_left_stem := GNC.Magnus.exponent5Left_flow_coeff

/-- Lemma 1, parity map: the left exponent is the negated right exponent of
the negated generators, as a polynomial identity. -/
alias lemma1_parity := GNC.Magnus.parity

/-- Lemma 1 by direct integration: the ordered double integral of (t2 - t1)
is -T^3/6, giving -T^3/12 on the left stem and +T^3/12 on the right stem. -/
alias lemma1_left_integral := GNC.Magnus.lemma1_left_coefficient
alias lemma1_right_integral := GNC.Magnus.lemma1_right_coefficient

/-- Lemma 2: the T^4 grade vanishes for a linear generator, right stem. -/
alias lemma2_right := GNC.Magnus.linear_degree_four

/-- Lemma 2: the T^4 grade vanishes for a linear generator, left stem. -/
alias lemma2_left := GNC.Magnus.left_linear_degree_four

/-- Lemma 2 by simplex moments: (1/6)(∫(t3 - t2) + ∫(t1 - t2)) = 0. -/
alias lemma2_simplex := GNC.Magnus.lemma2_cancellation

/-- Lemma 3: the exact T^5 residual on the right stem,
-(1/240)[N1,[N0,N1]] - (1/720)[N0,[N0,[N0,N1]]]. -/
alias lemma3_right := GNC.Magnus.linear_degree_five

/-- Lemma 3 and Table II, left column: -(1/240)[N1,[N0,N1]] + (1/720)[N0,[N0,[N0,N1]]]. -/
alias lemma3_left := GNC.Magnus.left_linear_degree_five

/-- Remark 2: the -1/240 coefficient recovered from Appendix B's simplex
moments by direct integration. -/
alias remark2_independent_confirmation := GNC.Magnus.remark2_confirmation

/-- Corollary 1, eq (12): the submultiplicative bound
T^5/60 ‖N0‖‖N1‖^2 + T^5/90 ‖N0‖^3 ‖N1‖ on the exact degree-five residual. -/
alias corollary1_residual_bound := GNC.Magnus.norm_residual5_le

/-! ### Section III-B, Lemma 4 -/

/-- Lemma 4: peeling the constant left flow leaves the right flow of N(t). -/
alias lemma4_peel_left := GNC.Magnus.peel_left

/-- Lemma 4 in factored form: state-independent left and right factors exist
for every continuous pair of inputs. -/
alias lemma4_factorization := GNC.Magnus.exists_mixed_flows

/-! ### Section III-C, Proposition 2 and Corollary 2 -/

/-- Proposition 2, eq (14): the extended-algebra commutator with the sign of
the time corner. -/
alias proposition2_commutator := GNC.Magnus.extended_commutator

/-- Proposition 2: brackets in the translation/time ideal occupy only the
position column. -/
alias proposition2_ideal_bracket := GNC.Magnus.ideal_commutator

/-- Proposition 2: the translation/time ideal is two-step nilpotent. -/
alias proposition2_two_step := GNC.Magnus.ideal_triple_commutator

/-- Eq (15): coning, sculling and scrolling as the three components of the
FOH bracket. -/
alias equation15_foh_bracket := GNC.Magnus.foh_commutator

/-- Corollary 2 in abstract form: when all triple products of the generators
vanish, the exponential of the degree-three exponent is exactly the flow. -/
alias corollary2_abstract := GNC.Magnus.exp_fohExponent

/-- Corollary 2 for the SE2(3) time-extended ideal: with no rotation the FOH
exponent T N0 + T^2/2 N1 + T^3/12 [N0,N1] is exact for every T. -/
alias corollary2_no_rotation := GNC.Magnus.exp_foh_increment_no_rotation

/-- Corollary 2, uniqueness: any solution of the rotation-free FOH flow is
that exponential. -/
alias corollary2_flow_unique := GNC.Magnus.foh_flow_no_rotation_unique

/-! ### Section III-D, Theorem 1 -/

/-- Theorem 1, eq (16): the corrected increment equals the truncated exponent
T N0 + T^2/2 N1 + T^3/12 [N0,N1] evaluated on the FOH generators. -/
alias theorem1_increment := GNC.Magnus.foh_increment

/-- Theorem 1, eq (17): the truncation error obeys
‖E(T)‖ ≤ ‖X(0)‖ e^{‖MT‖} e^{max(‖Ξ‖,‖Ξ≤3‖)} ‖Ξ - Ξ≤3‖. -/
alias theorem1_error_bound := GNC.Magnus.foh_truncation_error

/-- The exponential perturbation inequality behind eq (17). -/
alias theorem1_exponential_perturbation := GNC.Magnus.norm_exp_sub_exp_le

/-! ### Section III-E, Proposition 3 -/

/-- Proposition 3, eq (18): exact relative bookkeeping of the residual
against the T^3/12 correction. -/
alias proposition3_relative_residual := GNC.Magnus.relative_residual

/-! ### Section III-F, Proposition 4 -/

/-- Proposition 4, eq (20): bilinearity of the bracket in the bias. -/
alias proposition4_bracket_bilinear := GNC.Magnus.foh_bracket_bias_derivative

/-- Proposition 4, eq (21): gyro-bias sensitivity of the rotation increment. -/
alias proposition4_eq21 := GNC.Magnus.rotation_bias_derivative

/-- Proposition 4, eqs (22) and (23): accelerometer and gyro bias sensitivity
of the velocity increment, including the velocity-to-gyro-bias cross term. -/
alias proposition4_eq22_eq23 := GNC.Magnus.velocity_bias_derivative

/-! ### Section IV, Theorems 2 to 4 and Proposition 5 -/

/-- Theorem 2(a): FOH interpolation error at most M2 h^2/8. -/
alias theorem2a_interpolation := GNC.Hold.linear_error_le_bound

/-- Theorem 2(a), pointwise form (M2/2) t (h - t). -/
alias theorem2a_pointwise := GNC.Hold.linear_error_le

/-- Theorem 2(b): Lipschitz input, error at most M1 h/2. -/
alias theorem2b_lipschitz := GNC.Hold.lipschitz_linear_error_le_bound

/-- Theorem 3, eq (26), operator-norm form: the attitude discrepancy grows at
most linearly with the rate discrepancy; no Gronwall factor. -/
alias theorem3_eq26 := GNC.Analysis.attitude_sensitivity

/-- Theorem 3, eqs (27) and (28): velocity and position discrepancies. -/
alias theorem3_eq27_eq28 := GNC.Analysis.translation_sensitivity

/-- Lemma 5: error composition over a product of norm-one factors. -/
alias lemma5_composition := GNC.Analysis.norm_ofFn_prod_sub_le

/-- Theorem 4's truncation constants S^2 W/240 and S W^3/720 per interval. -/
alias theorem4_truncation_constants := GNC.Magnus.rotational_residual_le

/-- Theorem 4, eq (29): the per-second bound composed from per-subinterval
interpolation and truncation legs; the Magnus tail beyond degree five enters
as an explicit hypothesis. -/
alias theorem4_per_second := GNC.Analysis.per_second_bound

/-- Proposition 5, eq (30): the online certificate r + M2 h^2/8. -/
alias proposition5_certificate := GNC.Hold.certificate

/-! ### Section V, Propositions 6 and 7, Theorem 5 -/

/-- Proposition 6, eq (31): the centered parabola interpolates the three
samples. -/
alias proposition6_interpolates := GNC.Magnus.centeredHold_pos

/-- Proposition 6, eq (32): the exponent through degree five for a quadratic
generator, kernel-matched against the flow. -/
alias proposition6_exponent := GNC.Magnus.exponent5_flow_coeff

/-- Proposition 6: its pairwise-commutator moments h^3/12, h^4/12, h^5/60. -/
alias proposition6_pairwise := GNC.Magnus.prop6_pairwise_coefficients

/-- Proposition 6: the [A,[A,C]] coefficient 1/360 from simplex moments. -/
alias proposition6_triple := GNC.Magnus.prop6_triple_coefficient

/-- Proposition 6: C = 0 recovers the Theorem 1 exponent. -/
alias proposition6_recovers_theorem1 := GNC.Magnus.exponent5_zero_curvature_eq_foh

/-- Proposition 7: centered differences annihilate a constant bias. -/
alias proposition7_bias_invariance := GNC.Magnus.centered_bias_invariant

/-- Proposition 7, eq (33): gyro-bias Jacobian of the centered rotation
increment truncated after the displayed brackets. -/
alias proposition7_eq33 := GNC.Magnus.centeredRotationIncrement_bias_derivative

/-- Theorem 5, eq (34): quadratic interpolation error at most (√3/27) M3 h^3. -/
alias theorem5_quadratic := GNC.Hold.quadratic_error_le_bound

/-- Theorem 5, eq (35): the gain over FOH is (8√3/27)(2πfh). -/
alias theorem5_gain := GNC.Hold.interpolation_gain

/-- Theorem 5, noise term: centered quadrature weights (2/3, 5/12, -1/12). -/
alias theorem5_quadrature_weights := GNC.Magnus.integral_centeredHold

/-- Theorem 5, noise term: weight variance 5/8 against the trapezoid's 1/2. -/
alias theorem5_noise_variance := GNC.Magnus.centered_weight_variance

/-! ### Section VI, Theorem 6 and Proposition 8 -/

/-- Theorem 6: a right-injected correction transports through the buffered
factor by conjugation; no re-integration. -/
alias theorem6_reapplication := GNC.Magnus.reapplication

/-- Theorem 6, eq (36): the factors are independent of the initial state. -/
alias theorem6_state_independent := GNC.Magnus.flow_factors_state_independent

/-- Theorem 6, eq (37): the corrected flow from the corrected state. -/
alias theorem6_corrected_flow := GNC.Magnus.corrected_flow

/-- Proposition 8, eq (38), abstract form: a curvature bound 2 T_D^2 ‖db‖^2 on
the body velocity gives a remainder at most (T_D ‖db‖)^2. -/
alias proposition8_remainder := GNC.Magnus.second_order_remainder

/-- Proposition 8: the constant T_D ≤ T_tot (1 + h sup‖Δω‖/12). -/
alias proposition8_horizon_constant := GNC.Magnus.horizon_constant_le

/-! ### Section IV-D and Section XIII, covariance bookkeeping -/

/-- Section IV-D(ii): trapezoid endpoint sharing gives correlation exactly 1/2. -/
alias section4d_trapezoid_correlation := GNC.Magnus.trapezoid_cross_covariance

/-- Section IV-D(ii): the telescoped sum has variance (K - 1/2) h^2 σ^2. -/
alias section4d_telescoped_variance := GNC.Magnus.trapezoid_telescope_variance_sum

/-- Section XIII: Simpson's rule is exact on cubics. -/
alias section13_simpson_exact := GNC.Magnus.simpson_exact_cubic

/-! ### Section XVIII, Proposition 9 and Corollary 3 -/

/-- Proposition 9: the shipped two-sample coning term equals the bracket's
so(3) component with the identical 1/12 coefficient for uniform slope. -/
alias proposition9_coning_identity := GNC.Magnus.uniform_coning_stencil

/-- Corollary 3, sampling crossover at 0.5 mrad: 66.6 to 67.6 Hz. -/
alias corollary3_crossover_half_mrad := GNC.Magnus.crossover_half_mrad_freq

/-- Corollary 3, sampling crossover at 2 mrad: 128 to 132 Hz. -/
alias corollary3_crossover_two_mrad := GNC.Magnus.crossover_two_mrad_freq

/-- Corollary 3, body-rate crossover from the (1/60)(‖ω‖h)^2 term: between
1235 and 1245 rad/s at h = 1/1600 s. -/
alias corollary3_crossover_body_rate := GNC.Magnus.crossover_body_rate

/-! ### Appendices A and B -/

/-- Appendix A: the block product of two extended elements. -/
alias appendixA_block_product := GNC.Magnus.extended_commutator

/-- Appendix B: first simplex moments T^4/8, T^4/12, T^4/24. -/
alias appendixB_t1 := GNC.Magnus.simplex3_t1
alias appendixB_t2 := GNC.Magnus.simplex3_t2
alias appendixB_t3 := GNC.Magnus.simplex3_t3

/-- Appendix B: second simplex moments T^5/15, T^5/30, T^5/40. -/
alias appendixB_t1_t2 := GNC.Magnus.simplex3_t1_t2
alias appendixB_t1_t3 := GNC.Magnus.simplex3_t1_t3
alias appendixB_t2_t3 := GNC.Magnus.simplex3_t2_t3

end GNC.Applications.PreintegrationErrorTheory
