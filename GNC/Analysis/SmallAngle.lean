import GNC.Analysis.Coefficients
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-! The small-angle coefficient expansions in equation (66), with explicit
continuous extensions instead of relying on division at zero. -/
noncomputable section
open Real Filter Asymptotics
open scoped Topology
namespace GNC.Coefficients

def sinRemainder (t : ℝ) : ℝ := (sin t-(t-t^3/6+t^5/120))/t^5
def cosRemainder (t : ℝ) : ℝ := (cos t-(1-t^2/2+t^4/24))/t^4

theorem sin_taylor_five (t : ℝ) :
    taylorWithinEval sin 5 Set.univ 0 t = t-t^3/6+t^5/120 := by
  norm_num [taylorWithinEval_succ, iteratedDerivWithin_univ,
    iteratedDeriv_succ, Real.deriv_sin, deriv_cos', deriv.neg', deriv_neg]
  ring

theorem cos_taylor_four (t : ℝ) :
    taylorWithinEval cos 4 Set.univ 0 t = 1-t^2/2+t^4/24 := by
  norm_num [taylorWithinEval_succ, iteratedDerivWithin_univ,
    iteratedDeriv_succ, Real.deriv_sin, deriv_cos', deriv.neg', deriv_neg]
  ring

theorem sinRemainder_tendsto : Tendsto sinRemainder (𝓝 0) (𝓝 0) := by
  have h := (taylor_isLittleO_univ (x₀ := 0) (n := 5) contDiff_sin).tendsto_div_nhds_zero
  simpa only [sinRemainder, sin_taylor_five, sub_zero] using h

theorem cosRemainder_tendsto : Tendsto cosRemainder (𝓝 0) (𝓝 0) := by
  have h := (taylor_isLittleO_univ (x₀ := 0) (n := 4) contDiff_cos).tendsto_div_nhds_zero
  simpa only [cosRemainder, cos_taylor_four, sub_zero] using h

def betaRemainderModel (t : ℝ) : ℝ :=
  (1/45+sinRemainder (t/2)-cosRemainder (t/2)-(t/2)^2/360-
    (t/2)^2*sinRemainder (t/2)/3)/(16*sinc (t/2))

def alphaRemainderModel (t : ℝ) : ℝ :=
  (1/60+cosRemainder t-3*sinRemainder t)/(3*sinc (t/2)^2)

theorem beta_remainder_identity (t : ℝ) (ht : t ≠ 0) (hs : sin (t/2) ≠ 0) :
    (beta t-t^2/12)/t^4 = betaRemainderModel t := by
  unfold betaRemainderModel sinRemainder cosRemainder beta
  rw [sinc_of_ne_zero (div_ne_zero ht (by norm_num))]
  field_simp
  ring

theorem alpha_remainder_identity (t : ℝ) (ht : t ≠ 0) (hs : sin (t/2) ≠ 0) :
    (alpha t-t/6)/t^3 = alphaRemainderModel t := by
  have hsin : sin t = 2*sin (t/2)*cos (t/2) := by
    convert sin_two_mul (t/2) using 1; congr 1; ring
  have hcos : cos t = 1-2*sin (t/2)^2 := by
    convert cos_two_mul_eq_one_sub (t/2) using 1; congr 1; ring
  unfold alphaRemainderModel sinRemainder cosRemainder alpha
  rw [sinc_of_ne_zero (div_ne_zero ht (by norm_num)), hsin, hcos]
  field_simp
  ring

theorem sinc_half_tendsto : Tendsto (fun t : ℝ => sinc (t/2)) (𝓝 0) (𝓝 1) := by
  simpa using (continuous_sinc.comp (continuous_id.div_const 2)).tendsto (0:ℝ)

theorem sin_half_eventually_ne : ∀ᶠ t : ℝ in 𝓝[≠] 0, sin (t/2) ≠ 0 := by
  have hs := sinc_half_tendsto.eventually (eventually_ne_nhds (by norm_num : (1:ℝ) ≠ 0))
  filter_upwards [self_mem_nhdsWithin, hs.filter_mono nhdsWithin_le_nhds] with t ht hs
  have ht0 : t ≠ 0 := ht
  have hhalf : t/2 ≠ 0 := div_ne_zero ht0 (by norm_num)
  intro hz
  exact hs (by rw [sinc_of_ne_zero hhalf, hz, zero_div])

theorem betaRemainderModel_tendsto : Tendsto betaRemainderModel (𝓝 0) (𝓝 (1/720)) := by
  have ht : Tendsto (fun t : ℝ => t/2) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_id.div_const 2).tendsto (0:ℝ)
  have hs := sinRemainder_tendsto.comp ht
  have hc := cosRemainder_tendsto.comp ht
  have hconst : Tendsto (fun _ : ℝ => (1/45:ℝ)) (𝓝 0) (𝓝 (1/45)) := tendsto_const_nhds
  have h := ((((hconst.add hs).sub hc).sub
    ((ht.pow 2).div_const 360)).sub (((ht.pow 2).mul hs).div_const 3)).div
      (sinc_half_tendsto.const_mul 16) (by norm_num)
  convert h using 1 <;> norm_num [betaRemainderModel]

theorem alphaRemainderModel_tendsto : Tendsto alphaRemainderModel (𝓝 0) (𝓝 (1/180)) := by
  have hconst : Tendsto (fun _ : ℝ => (1/60:ℝ)) (𝓝 0) (𝓝 (1/60)) := tendsto_const_nhds
  have h := ((hconst.add cosRemainder_tendsto).sub
    (sinRemainder_tendsto.const_mul 3)).div ((sinc_half_tendsto.pow 2).const_mul 3) (by norm_num)
  convert h using 1 <;> norm_num [alphaRemainderModel]

theorem beta_remainder_limit :
    Tendsto (fun t => (beta t-t^2/12)/t^4) (𝓝[≠] 0) (𝓝 (1/720)) := by
  apply (betaRemainderModel_tendsto.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin, sin_half_eventually_ne] with t ht hs
  exact (beta_remainder_identity t ht hs).symm

theorem alpha_remainder_limit :
    Tendsto (fun t => (alpha t-t/6)/t^3) (𝓝[≠] 0) (𝓝 (1/180)) := by
  apply (alphaRemainderModel_tendsto.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin, sin_half_eventually_ne] with t ht hs
  exact (alpha_remainder_identity t ht hs).symm

/-- First expansion in (66). The punctured filter avoids mistaking the raw
quotient's value at zero for its continuous extension. -/
theorem beta_expansion : (fun t => beta t-t^2/12) =O[𝓝[≠] 0] (fun t : ℝ => t^4) := by
  apply isBigO_of_div_tendsto_nhds _ (1/720) beta_remainder_limit
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact fun h => False.elim (pow_ne_zero 4 ht h)

/-- Second expansion in (66). -/
theorem alpha_expansion : (fun t => alpha t-t/6) =O[𝓝[≠] 0] (fun t : ℝ => t^3) := by
  apply isBigO_of_div_tendsto_nhds _ (1/180) alpha_remainder_limit
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact fun h => False.elim (pow_ne_zero 3 ht h)

theorem beta_tendsto_zero : Tendsto beta (𝓝[≠] 0) (𝓝 0) := by
  have ht : Tendsto (fun t : ℝ => t) (𝓝[≠] 0) (𝓝 0) := nhdsWithin_le_nhds
  have h := ((ht.pow 2).div_const 12).add ((ht.pow 4).mul beta_remainder_limit)
  norm_num at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : t ≠ 0 := ht
  field_simp
  ring

theorem alpha_tendsto_zero : Tendsto alpha (𝓝[≠] 0) (𝓝 0) := by
  have ht : Tendsto (fun t : ℝ => t) (𝓝[≠] 0) (𝓝 0) := nhdsWithin_le_nhds
  have h := (ht.div_const 6).add ((ht.pow 3).mul alpha_remainder_limit)
  norm_num at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : t ≠ 0 := ht
  field_simp
  ring

/-- The intended coefficient at zero; the raw quotient `beta 0` is 1. -/
def betaContinuous (t : ℝ) : ℝ := if t = 0 then 0 else beta t

@[simp] theorem betaContinuous_zero : betaContinuous 0 = 0 := by simp [betaContinuous]

theorem betaContinuous_of_ne (t : ℝ) (ht : t ≠ 0) : betaContinuous t = beta t := by
  simp [betaContinuous, ht]

theorem betaContinuous_continuousAt_zero : ContinuousAt betaContinuous 0 := by
  rw [continuousAt_iff_punctured_nhds, betaContinuous_zero]
  apply beta_tendsto_zero.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (betaContinuous_of_ne t ht).symm

@[simp] theorem alpha_zero : alpha 0 = 0 := by simp [alpha]

theorem alpha_continuousAt_zero : ContinuousAt alpha 0 := by
  rw [continuousAt_iff_punctured_nhds, alpha_zero]
  exact alpha_tendsto_zero

/-- Magnitude contraction in (83): sinc(θ/2)=1-θ²/24+O(θ⁴). -/
theorem contraction_remainder_limit :
    Tendsto (fun t : ℝ => (sinc (t/2)-1+t^2/24)/t^4) (𝓝[≠] 0) (𝓝 (1/1920)) := by
  have ht : Tendsto (fun t : ℝ => t/2) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_id.div_const 2).tendsto (0:ℝ)
  have hconst : Tendsto (fun _ : ℝ => (1/120:ℝ)) (𝓝 0) (𝓝 (1/120)) := tendsto_const_nhds
  have h := (hconst.add (sinRemainder_tendsto.comp ht)).div_const 16
  norm_num at h
  apply (h.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : t ≠ 0 := ht
  have hhalf : t/2 ≠ 0 := div_ne_zero ht0 (by norm_num)
  rw [sinc_of_ne_zero hhalf]
  unfold sinRemainder
  field_simp
  ring

theorem contraction_expansion :
    (fun t : ℝ => sinc (t/2)-1+t^2/24) =O[𝓝[≠] 0] (fun t : ℝ => t^4) := by
  apply isBigO_of_div_tendsto_nhds _ (1/1920) contraction_remainder_limit
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact fun h => False.elim (pow_ne_zero 4 ht h)

end GNC.Coefficients
