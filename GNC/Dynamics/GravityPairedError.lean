import GNC.Dynamics.GravityLipschitz
import GNC.Dynamics.GravityHessianBilinear
import GNC.Dynamics.GravityRemainderBall

/-! Shared nominal error enters relative gravitational acceleration through
a mixed second difference. Its bound is proportional to both the nominal
prediction error and the relative displacement, rather than charging the
nominal position error twice. These are bounds on the actual inverse-square
field, on explicitly nonsingular regions, in any real inner-product space.
-/
noncomputable section
open Set
namespace GNC.Gravity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem gradient_difference (μ : ℝ) (hμ : 0 ≤ μ) (p q v : E) {r : ℝ}
    (hr : 0 < r) (hseg : ∀ s ∈ Icc (0:ℝ) 1, r ≤ ‖q+s • (p-q)‖) :
    ‖gradient μ p v-gradient μ q v‖ ≤ (6*μ/r^4)*‖p-q‖*‖v‖ := by
  have hd (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
      HasDerivAt (fun t : ℝ => gradient μ (q+t • (p-q)) v)
        (hessian μ (q+s • (p-q)) (p-q) v) s := by
    apply gradient_derivative
    · simpa using ((hasDerivAt_id s).smul_const (p-q)).const_add q
    · exact norm_pos_iff.mp (hr.trans_le (hseg s hs))
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun s hs => (hd s hs).hasDerivWithinAt) (C := (6*μ/r^4)*‖p-q‖*‖v‖) (by
      intro s hs
      have hss := Ico_subset_Icc_self hs
      have hz := norm_pos_iff.mp (hr.trans_le (hseg s hss))
      exact (hessian_mixed_bound μ hμ _ _ _ hz).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_left (by positivity) (by positivity)
            (pow_le_pow_left₀ hr.le (hseg s hss) 4)) (norm_nonneg _)) (norm_nonneg _)))
  simpa only [one_smul,zero_smul,add_zero,add_sub_cancel] using h

/-- The shared shift affects an increment only through the gravity Hessian.
In particular the right side vanishes when either displacement vanishes. -/
theorem field_increment_shift (μ : ℝ) (hμ : 0 ≤ μ) (q d e : E) {r : ℝ}
    (hr : 0 < r)
    (hrect : ∀ s ∈ Icc (0:ℝ) 1, ∀ t ∈ Icc (0:ℝ) 1,
      r ≤ ‖q+s • d+t • e‖) :
    ‖(field μ (q+d+e)-field μ (q+e))-(field μ (q+d)-field μ q)‖ ≤
      (6*μ/r^4)*‖d‖*‖e‖ := by
  have hd (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
      HasDerivAt (fun t : ℝ => field μ (q+t • d+e)-field μ (q+t • d))
        (gradient μ (q+s • d+e) d-gradient μ (q+s • d) d) s := by
    apply HasDerivAt.sub
    · apply field_derivative
      · simpa using (((hasDerivAt_id s).smul_const d).const_add q).add_const e
      · apply norm_pos_iff.mp
        have h := hrect s hs 1 (by norm_num)
        simpa only [one_smul] using hr.trans_le h
    · apply field_derivative
      · simpa using ((hasDerivAt_id s).smul_const d).const_add q
      · apply norm_pos_iff.mp
        have h := hrect s hs 0 (by norm_num)
        simpa only [zero_smul,add_zero] using hr.trans_le h
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun s hs => (hd s hs).hasDerivWithinAt) (C := (6*μ/r^4)*‖d‖*‖e‖) (by
      intro s hs
      have hb := gradient_difference μ hμ (q+s • d+e) (q+s • d) d hr (by
        intro t ht
        simpa only [add_sub_cancel_left] using hrect s (Ico_subset_Icc_self hs) t ht)
      simpa only [add_sub_cancel_left,mul_right_comm _ ‖e‖ ‖d‖] using hb)
  simp only [one_smul,zero_smul,add_zero] at h
  convert h using 1
  congr 1
  abel

theorem field_increment_shift_ball (μ : ℝ) (hμ : 0 ≤ μ) (q d e : E) {r D N : ℝ}
    (hr : 0 < r) (hq : r+D+N ≤ ‖q‖) (hd : ‖d‖ ≤ D) (he : ‖e‖ ≤ N) :
    ‖(field μ (q+d+e)-field μ (q+e))-(field μ (q+d)-field μ q)‖ ≤
      (6*μ/r^4)*‖d‖*‖e‖ := by
  apply field_increment_shift μ hμ q d e hr
  intro s hs t ht
  have hd' : ‖s • d‖ ≤ D := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hs.1]
    exact (mul_le_of_le_one_left (norm_nonneg d) hs.2).trans hd
  have he' : ‖t • e‖ ≤ N := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg e) ht.2).trans he
  have hb := (norm_add_le (s • d) (t • e)).trans (add_le_add hd' he')
  have hnorm := norm_sub_norm_le q (-(s • d+t • e))
  rw [norm_neg,sub_neg_eq_add] at hnorm
  rw [add_assoc]
  linarith

/-- Acceleration error for a pair of trajectories: the relative prediction
error is linear to first order, while the shared nominal error carries an
additional factor equal to the relative displacement. -/
theorem paired_field_error (μ : ℝ) (hμ : 0 ≤ μ) (q d nominalError relativeError : E)
    {r D N M : ℝ} (hr : 0 < r) (hq : r+D+N+M ≤ ‖q‖)
    (hd : ‖d‖ ≤ D) (hn : ‖nominalError‖ ≤ N) (he : ‖relativeError‖ ≤ M) :
    ‖(field μ (q+d+nominalError+relativeError)-field μ (q+nominalError))-
        (field μ (q+d)-field μ q)‖ ≤
      (2*μ/r^3)*‖relativeError‖+(6*μ/r^4)*‖d‖*‖nominalError‖ := by
  have hM : 0 ≤ M := (norm_nonneg _).trans he
  have hregion : r+M ≤ ‖q+d+nominalError‖ := by
    have hb := (norm_add_le d nominalError).trans (add_le_add hd hn)
    have hnorm := norm_sub_norm_le q (-(d+nominalError))
    rw [norm_neg,sub_neg_eq_add,← add_assoc] at hnorm
    linarith
  have hrel := field_difference_ball μ hμ (q+d+nominalError) relativeError 0 hr hregion he
    (by simpa using hM)
  simp only [add_zero,sub_zero] at hrel
  have hnom := field_increment_shift_ball μ hμ q d nominalError hr (by linarith) hd hn
  have hid : (field μ (q+d+nominalError+relativeError)-field μ (q+nominalError))-
        (field μ (q+d)-field μ q) =
      (field μ (q+d+nominalError+relativeError)-field μ (q+d+nominalError))+
      ((field μ (q+d+nominalError)-field μ (q+nominalError))-
        (field μ (q+d)-field μ q)) := by abel
  rw [hid]
  exact (norm_add_le _ _).trans (add_le_add hrel hnom)

/-- Relative to the usual gravity-gradient gain, the shared nominal-error
coefficient has the extra dimensionless factor `3 D / r`. -/
theorem nominal_error_coefficient (μ D r : ℝ) (hr : r ≠ 0) :
    (6*μ/r^4)*D = (3*D/r)*(2*μ/r^3) := by field_simp; ring

/-- Retain the known reference gradient rather than bounding it by its
norm. The remaining error consists of a small gradient-change term, a
quadratic prediction-error term, and the mixed shared-nominal term. -/
theorem paired_field_near_linear [CompleteSpace E]
    (μ : ℝ) (hμ : 0 ≤ μ) (q d nominalError relativeError : E)
    {r D N M : ℝ} (hr : 0 < r) (hq : r+D+N+M ≤ ‖q‖)
    (hd : ‖d‖ ≤ D) (hn : ‖nominalError‖ ≤ N) (he : ‖relativeError‖ ≤ M) :
    ‖(field μ (q+d+nominalError+relativeError)-field μ (q+nominalError))-
        (field μ (q+d)-field μ q)-gradient μ q relativeError‖ ≤
      (3*μ/r^4)*‖relativeError‖^2+(6*μ/r^4)*(D+N)*‖relativeError‖+
        (6*μ/r^4)*‖d‖*‖nominalError‖ := by
  have hM : 0 ≤ M := (norm_nonneg _).trans he
  have hdn := (norm_add_le d nominalError).trans (add_le_add hd hn)
  have hregion : r+M ≤ ‖q+d+nominalError‖ := by
    have hnorm := norm_sub_norm_le q (-(d+nominalError))
    rw [norm_neg,sub_neg_eq_add,← add_assoc] at hnorm
    linarith
  have hrem := remainder_quadratic μ hμ (q+d+nominalError) relativeError
    (r := r+M) (D := M) (by linarith) hregion he
  simp only [add_sub_cancel_right] at hrem
  have hgrad := gradient_difference μ hμ (q+d+nominalError) q relativeError hr (by
    intro s hs
    have hid : q+d+nominalError-q = d+nominalError := by abel
    rw [hid]
    have hb : ‖s • (d+nominalError)‖ ≤ D+N := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hs.1]
      exact (mul_le_of_le_one_left (norm_nonneg _) hs.2).trans hdn
    have hnorm := norm_sub_norm_le q (-(s • (d+nominalError)))
    rw [norm_neg,sub_neg_eq_add] at hnorm
    linarith)
  have hgrad' : ‖gradient μ (q+d+nominalError) relativeError-gradient μ q relativeError‖ ≤
      (6*μ/r^4)*(D+N)*‖relativeError‖ := by
    have hid : q+d+nominalError-q = d+nominalError := by abel
    rw [hid] at hgrad
    exact hgrad.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hdn (by positivity)) (norm_nonneg _))
  have hnom := field_increment_shift_ball μ hμ q d nominalError hr (by linarith) hd hn
  have hid : (field μ (q+d+nominalError+relativeError)-field μ (q+nominalError))-
      (field μ (q+d)-field μ q)-gradient μ q relativeError =
      (field μ (q+d+nominalError+relativeError)-field μ (q+d+nominalError)-
        gradient μ (q+d+nominalError) relativeError)+
      (gradient μ (q+d+nominalError) relativeError-gradient μ q relativeError)+
      ((field μ (q+d+nominalError)-field μ (q+nominalError))-
        (field μ (q+d)-field μ q)) := by abel
  rw [hid]
  exact (norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add hrem hgrad')) hnom)

end GNC.Gravity
