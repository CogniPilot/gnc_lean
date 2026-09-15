import GNC.Dynamics.GravityField

/-! Monotonicity of the sharp gravity remainder in the displacement radius.
The proof compares the already established integral envelopes; no fitted
coefficient or enlargement of the residual is needed. -/
noncomputable section
namespace GNC.Gravity
open Set MeasureTheory

theorem remainderBound_mono {μ r d D : ℝ} (hμ : 0 ≤ μ) (hd : 0 ≤ d)
    (hdD : d ≤ D) (hDr : D < r) : remainderBound μ r d ≤ remainderBound μ r D := by
  have hD : 0 ≤ D := hd.trans hdD
  have hpos (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) : 0 < r-s*D := by
    nlinarith [mul_le_mul_of_nonneg_right hs.2 hD]
  have hposd (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) : 0 < r-s*d := by
    nlinarith [mul_le_mul_of_nonneg_left hdD hs.1,hpos s hs]
  have hc : ContinuousOn (fun s : ℝ => 6*μ*D^2*(1-s)/(r-s*D)^4) (Icc 0 1) := by
    intro s hs
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := exact pow_ne_zero 4 (hpos s hs).ne')
  have hcd : ContinuousOn (fun s : ℝ => 6*μ*d^2*(1-s)/(r-s*d)^4) (Icc 0 1) := by
    intro s hs
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := exact pow_ne_zero 4 (hposd s hs).ne')
  rw [← envelope_integral μ r d hd (hdD.trans_lt hDr),← envelope_integral μ r D hD hDr]
  apply intervalIntegral.integral_mono_on (by norm_num)
    (hcd.intervalIntegrable_of_Icc (by norm_num)) (hc.intervalIntegrable_of_Icc (by norm_num))
  intro s hs
  have hs1 : 0 ≤ 1-s := sub_nonneg.mpr hs.2
  have hn : 0 ≤ 6*μ*d^2*(1-s) := by positivity [sub_nonneg.mpr hs.2]
  apply (div_le_div_of_nonneg_left hn (by positivity [hpos s hs])
    (pow_le_pow_left₀ (hpos s hs).le
      (by nlinarith [mul_le_mul_of_nonneg_left hdD hs.1]) 4)).trans
  gcongr

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem remainder_bound_of_norm_le (μ : ℝ) (hμ : 0 ≤ μ) (q d : E) {D : ℝ}
    (hd : ‖d‖ ≤ D) (hD : D < ‖q‖) :
    ‖field μ (q+d)-field μ q-gradient μ q d‖ ≤ remainderBound μ ‖q‖ D :=
  (remainder_bound μ hμ q d (hd.trans_lt hD)).trans
    (remainderBound_mono hμ (norm_nonneg d) hd hD)

end GNC.Gravity
