import GNC.Analysis.SmallAngle

/-! The remaining analytic statements in Appendix C: strict monotonicity
of c, the expansion of h, and the limiting sharp coefficient ratio. -/
noncomputable section
open Real Set Filter Asymptotics
open scoped Topology
namespace GNC.Coefficients

def inverseQuadraticCoefficient (t : ℝ) : ℝ := beta t/t^2

theorem inverseQuadraticCoefficient_derivative (t : ℝ) (ht : 0 < t) (htπ : t < π) :
    HasDerivAt inverseQuadraticCoefficient ((alpha t-2*beta t/t)/t^2) t := by
  convert (beta_derivative t ht htπ).div ((hasDerivAt_id t).pow 2) (pow_ne_zero 2 ht.ne') using 1
  dsimp only [id_eq, Pi.pow_apply]
  field_simp
  ring

theorem inverseQuadraticCoefficient_strictMono : StrictMonoOn inverseQuadraticCoefficient (Ioo 0 π) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo _ _)
  · intro t ht
    exact (inverseQuadraticCoefficient_derivative t ht.1 ht.2).continuousAt.continuousWithinAt
  · intro t ht
    rw [interior_Ioo] at ht
    rw [(inverseQuadraticCoefficient_derivative t ht.1 ht.2).deriv]
    exact div_pos (sub_pos.mpr (alpha_gt_two_beta_div t ht.1 ht.2)) (sq_pos_of_pos ht.1)

theorem sin_taylor_seven (t : ℝ) :
    taylorWithinEval sin 7 univ 0 t = t-t^3/6+t^5/120-t^7/5040 := by
  norm_num [taylorWithinEval_succ, iteratedDerivWithin_univ,
    iteratedDeriv_succ, Real.deriv_sin, deriv_cos', deriv.neg', deriv_neg]
  ring

theorem cos_taylor_eight (t : ℝ) :
    taylorWithinEval cos 8 univ 0 t = 1-t^2/2+t^4/24-t^6/720+t^8/40320 := by
  norm_num [taylorWithinEval_succ, iteratedDerivWithin_univ,
    iteratedDeriv_succ, Real.deriv_sin, deriv_cos', deriv.neg', deriv_neg]
  ring

theorem h_remainder_limit :
    Tendsto (fun t : ℝ => (h t-t^6/360)/t^8) (𝓝[≠] 0) (𝓝 (-1/10080)) := by
  rw [neg_div]
  have hs := (taylor_isLittleO_univ (x₀ := 0) (n := 7) contDiff_sin).tendsto_div_nhds_zero
  have hc := (taylor_isLittleO_univ (x₀ := 0) (n := 8) contDiff_cos).tendsto_div_nhds_zero
  simp only [sin_taylor_seven, cos_taylor_eight, sub_zero] at hs hc
  have hh := (hs.add (hc.const_mul 4)).sub_const (1/10080)
  norm_num at hh
  apply (hh.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : t ≠ 0 := ht
  unfold h
  field_simp
  ring

theorem h_expansion :
    (fun t : ℝ => h t-t^6/360) =O[𝓝[≠] 0] (fun t : ℝ => t^8) := by
  apply isBigO_of_div_tendsto_nhds _ (-1/10080) h_remainder_limit
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact fun h => False.elim (pow_ne_zero 8 ht h)

theorem beta_div_sq_limit : Tendsto (fun t : ℝ => beta t/t^2) (𝓝[≠] 0) (𝓝 (1/12)) := by
  have ht : Tendsto (fun t : ℝ => t) (𝓝[≠] 0) (𝓝 0) := nhdsWithin_le_nhds
  have h := ((ht.pow 2).mul beta_remainder_limit).add_const (1/12)
  norm_num at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : t ≠ 0 := ht
  field_simp
  ring

theorem alpha_div_limit : Tendsto (fun t : ℝ => alpha t/t) (𝓝[≠] 0) (𝓝 (1/6)) := by
  have ht : Tendsto (fun t : ℝ => t) (𝓝[≠] 0) (𝓝 0) := nhdsWithin_le_nhds
  have h := ((ht.pow 2).mul alpha_remainder_limit).add_const (1/6)
  norm_num at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : t ≠ 0 := ht
  field_simp
  ring

theorem coefficient_ratio_limit :
    Tendsto (fun t : ℝ => alpha t/(beta t/t)) (𝓝[≠] 0) (𝓝 2) := by
  have h := alpha_div_limit.div beta_div_sq_limit (by norm_num)
  norm_num at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : t ≠ 0 := ht
  dsimp only [Pi.div_apply]
  by_cases hb : beta t = 0
  · simp [hb]
  · field_simp

theorem coefficient_ratio_gt_two (t : ℝ) (ht : 0 < t) (htπ : t < π) :
    2 < alpha t/(beta t/t) := by
  rw [lt_div_iff₀ (div_pos (beta_pos t ht htπ) ht)]
  simpa only [mul_div_assoc] using alpha_gt_two_beta_div t ht htπ

end GNC.Coefficients
