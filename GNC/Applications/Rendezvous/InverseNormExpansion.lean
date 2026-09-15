import GNC.Analysis.SmallAngle
import GNC.Lie.Jacobian

/-! The inverse-Jacobian norm expansion in Lemma 2, using the already
checked sine remainder and mathlib's limit algebra. -/
noncomputable section
open Real Filter Asymptotics
open scoped Topology
namespace GNC.Coefficients

theorem inverse_contraction_remainder_limit :
    Tendsto (fun t : ℝ => ((sinc (t/2))⁻¹-1-t^2/24)/t^4)
      (𝓝[≠] 0) (𝓝 (7/5760)) := by
  have ht : Tendsto (fun t : ℝ => t) (𝓝[≠] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hconst : Tendsto (fun _ : ℝ => (1/576:ℝ)) (𝓝[≠] 0) (𝓝 (1/576)) := tendsto_const_nhds
  have hr := contraction_remainder_limit
  have h := ((hconst.sub hr).sub (((ht.pow 2).mul hr).div_const 24)).div
    (sinc_half_tendsto.mono_left nhdsWithin_le_nhds) (by norm_num)
  norm_num at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin, sin_half_eventually_ne] with t ht hs
  have ht0 : t ≠ 0 := ht
  have hhalf : t/2 ≠ 0 := div_ne_zero ht0 (by norm_num)
  have hsin : sinc (t/2) ≠ 0 := by rw [sinc_of_ne_zero hhalf]; exact div_ne_zero hs hhalf
  dsimp only [Pi.div_apply]
  field_simp
  ring

/-- The inverse norm is 1+θ²/24+O(θ⁴), with normalized remainder 7/5760. -/
theorem inverse_contraction_expansion :
    (fun t : ℝ => (sinc (t/2))⁻¹-1-t^2/24) =O[𝓝[≠] 0] (fun t : ℝ => t^4) := by
  apply isBigO_of_div_tendsto_nhds _ (7/5760) inverse_contraction_remainder_limit
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact fun h => False.elim (pow_ne_zero 4 ht h)

theorem inverse_operatorNorm_sinc (k : Vec3) (hk : dotProduct k k = 1)
    (t : ℝ) (ht : 0 < t) (htπ : t < 2*Real.pi) :
    ‖Jacobian.leftInvCLM k t‖ = (sinc (t/2))⁻¹ := by
  rw [Jacobian.leftInv_operatorNorm k hk t ht htπ, sinc_of_ne_zero (by linarith : t/2 ≠ 0)]
  simp

end GNC.Coefficients
