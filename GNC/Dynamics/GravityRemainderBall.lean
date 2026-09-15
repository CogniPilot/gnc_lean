import GNC.Dynamics.GravityLipschitz
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Uniform remainder over a certified physical displacement ball.
This convenient Hessian bound is weaker than the sharp radial remainder,
but separates the displacement squared from a fixed regional constant. -/
noncomputable section
open Set MeasureTheory
namespace GNC.Gravity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem remainder_ball (μ : ℝ) (hμ : 0 ≤ μ) (q d : E) {r R : ℝ}
    (hR : 0 ≤ R) (hr : R < r) (hq : r ≤ ‖q‖) (hd : ‖d‖ ≤ R) :
    ‖field μ (q+d)-field μ q-gradient μ q d‖ ≤ 3*μ*R^2/(r-R)^4 := by
  have hsep : ‖d‖ < ‖q‖ := hd.trans_lt (hr.trans_le hq)
  have hpos : 0 < r-R := sub_pos.mpr hr
  rw [taylor_integral μ q d hsep]
  have hb (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
      ‖(1-s) • hessian μ (q+s • d) d d‖ ≤ (1-s)*(6*μ*R^2/(r-R)^4) := by
    have hnorm := segment_norm_lower q d s hs.1
    have hrad : r-R ≤ ‖q+s • d‖ := by
      have hsd := mul_le_mul_of_nonneg_right hs.2 (norm_nonneg d)
      linarith
    have hh := hessian_bound μ hμ (q+s • d) d (segment_nonzero q d hsep s hs)
    have hden : 6*μ/‖q+s • d‖^4 ≤ 6*μ/(r-R)^4 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (pow_le_pow_left₀ (sub_pos.mpr hr).le hrad 4)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hs.2)]
    apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr hs.2)
    calc
      _ ≤ (6*μ/(r-R)^4)*R^2 := hh.trans
        (mul_le_mul hden (pow_le_pow_left₀ (norm_nonneg d) hd 2)
          (sq_nonneg _) (by positivity))
      _ = _ := by ring
  have hi := intervalIntegral.norm_integral_le_of_norm_le (by norm_num : (0:ℝ) ≤ 1)
    (Filter.Eventually.of_forall fun s hs => hb s ⟨hs.1.le,hs.2⟩)
    ((((continuous_const : Continuous (fun _ : ℝ => (1:ℝ))).sub continuous_id).mul_const
      (6*μ*R^2/(r-R)^4)).intervalIntegrable (μ := volume) 0 1)
  have he : (∫ s in (0:ℝ)..1, (1-s)*(6*μ*R^2/(r-R)^4)) =
      3*μ*R^2/(r-R)^4 := by
    have hd (s : ℝ) : HasDerivAt (fun t : ℝ => t-t^2/2) (1-s) s := by
      convert (hasDerivAt_id s).sub (((hasDerivAt_id s).pow 2).div_const 2) using 1
      simp
    have hs := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s (_ : s ∈ uIcc (0:ℝ) 1) => hd s)
      (((continuous_const : Continuous (fun _ : ℝ => (1:ℝ))).sub continuous_id).intervalIntegrable 0 1)
    rw [intervalIntegral.integral_mul_const, hs]
    norm_num; ring
  exact hi.trans_eq he

/-- Fix only the validity domain, not the displacement. The coefficient can
vary with the reference radius at every time in a response integral. -/
theorem remainder_quadratic (μ : ℝ) (hμ : 0 ≤ μ) (q d : E) {r D : ℝ}
    (hD : D < r) (hq : r ≤ ‖q‖) (hd : ‖d‖ ≤ D) :
    ‖field μ (q+d)-field μ q-gradient μ q d‖ ≤
      (3*μ/(r-D)^4)*‖d‖^2 := by
  have hb := remainder_ball μ hμ q d (norm_nonneg d) (hd.trans_lt hD) hq le_rfl
  have hden : (r-D)^4 ≤ (r-‖d‖)^4 :=
    pow_le_pow_left₀ (sub_pos.mpr hD).le (by linarith) 4
  have hpos : 0 < r-D := sub_pos.mpr hD
  calc
    _ ≤ 3*μ*‖d‖^2/(r-‖d‖)^4 := hb
    _ ≤ 3*μ*‖d‖^2/(r-D)^4 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ = _ := by ring

end GNC.Gravity
