import GNC.Dynamics.GravityGradientBound
import GNC.Analysis.EuclideanBox
import Mathlib.Analysis.Calculus.MeanValue

/-! Lipschitz bounds for the actual inverse-square field on nonsingular
convex regions. The constants follow from the sharp gravity-gradient bound
and released mathlib's mean-value theorem, including the full field.
-/
noncomputable section
set_option autoImplicit false
open Set
namespace GNC.Gravity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem field_difference (μ : ℝ) (hμ : 0 ≤ μ) (p q : E) {r : ℝ}
    (hr : 0 < r) (hseg : ∀ s ∈ Icc (0:ℝ) 1, r ≤ ‖q+s • (p-q)‖) :
    ‖field μ p-field μ q‖ ≤ (2*μ/r^3)*‖p-q‖ := by
  have hd (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
      HasDerivAt (fun t : ℝ => field μ (q+t • (p-q)))
        (gradient μ (q+s • (p-q)) (p-q)) s := by
    apply field_derivative
    · simpa using ((hasDerivAt_id s).smul_const (p-q)).const_add q
    · exact norm_pos_iff.mp (hr.trans_le (hseg s hs))
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun s hs => (hd s hs).hasDerivWithinAt) (C := (2*μ/r^3)*‖p-q‖) (by
      intro s hs
      have hl := hseg s (Ico_subset_Icc_self hs)
      exact (gradient_bound μ hμ _ _).trans (mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_left (by positivity) (by positivity)
          (pow_le_pow_left₀ hr.le hl 3)) (norm_nonneg _)))
  simpa only [one_smul, zero_smul, add_zero, add_sub_cancel] using h

theorem field_difference_ball (μ : ℝ) (hμ : 0 ≤ μ) (c p q : E) {r R : ℝ}
    (hr : 0 < r) (hc : r+R ≤ ‖c‖) (hp : ‖p‖ ≤ R) (hq : ‖q‖ ≤ R) :
    ‖field μ (c+p)-field μ (c+q)‖ ≤ (2*μ/r^3)*‖p-q‖ := by
  have h := field_difference μ hμ (c+p) (c+q) hr (by
    intro s hs
    have he : c+q+s • ((c+p)-(c+q)) = c+((1-s) • q+s • p) := by module
    rw [he]
    have hb : ‖(1-s) • q+s • p‖ ≤ R := by
      have h := norm_add_le ((1-s) • q) (s • p)
      rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr hs.2),abs_of_nonneg hs.1] at h
      nlinarith [mul_le_mul_of_nonneg_left hp hs.1,
        mul_le_mul_of_nonneg_left hq (sub_nonneg.mpr hs.2)]
    have ht := norm_sub_norm_le c (-((1-s) • q+s • p))
    rw [norm_neg,sub_neg_eq_add] at ht
    linarith)
  simpa only [add_sub_add_left_eq_sub] using h

theorem field3_continuousAt (μ : ℝ) {p : Vec3} (hp : 0 < enorm p) :
    ContinuousAt (field3 μ) p := by
  change ContinuousAt (fun q : Vec3 => (-μ/enorm q^3) • q) p
  have he : Continuous (enorm : Vec3 → ℝ) :=
    (WithLp.linearEquiv 2 ℝ Vec3).symm.toLinearMap.toContinuousLinearMap.continuous.norm
  exact (continuousAt_const.div (he.continuousAt.pow 3)
    (pow_ne_zero 3 hp.ne')).smul continuousAt_id

/-- A convenient sup-norm constant on a five-percent position-error cube.
The general Euclidean theorem above supplies the actual nonlinear bound. -/
theorem field3_difference_box (c p q : Vec3)
    (hc : (79/100:ℝ) ≤ enorm c)
    (hp : ‖p‖ ≤ (1/20:ℝ)) (hq : ‖q‖ ≤ (1/20:ℝ)) :
    ‖field3 1 (c+p)-field3 1 (c+q)‖ ≤ 16*‖p-q‖ := by
  have h := field_difference_ball 1 (by norm_num)
    (WithLp.toLp 2 c : Jacobian.E3) (WithLp.toLp 2 p) (WithLp.toLp 2 q)
    (r := (2/3:ℝ)) (R := (1/10:ℝ)) (by norm_num) (by change _ ≤ enorm c; linarith)
    (by change enorm p ≤ _; linarith [enorm_le_two_pi_norm p])
    (by change enorm q ≤ _; linarith [enorm_le_two_pi_norm q])
  change enorm (field3 1 (c+p)-field3 1 (c+q)) ≤
    (2*1/(2/3)^3)*enorm (p-q) at h
  have he := pi_norm_le_enorm (field3 1 (c+p)-field3 1 (c+q))
  have hb := enorm_le_two_pi_norm (p-q)
  norm_num at h
  nlinarith [norm_nonneg (p-q)]

end GNC.Gravity
