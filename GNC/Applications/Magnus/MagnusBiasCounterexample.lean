import GNC.Magnus.MagnusInputs
import GNC.Lie.ZeroAttitude
import GNC.Analysis.SmallAngle
import Mathlib.Analysis.Real.Pi.Bounds

/-! A counterexample to the unqualified velocity bias-remainder bound in
Proposition 8 of main.pdf, for the actual FOH closed-form update. This is a
large-rate test of the theorem's stated scope, not a deployed flight case. -/
noncomputable section
namespace GNC.Magnus
set_option maxHeartbeats 2000000
open Matrix Real NormedSpace
open Filter
open scoped Matrix Matrix.Norms.Operator Topology

def timeBlock : Matrix (Fin 2) (Fin 2) ℝ := !![0,1;0,0]

theorem timeBlock_sq : timeBlock^2 = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [timeBlock, pow_two, Matrix.mul_apply, Fin.sum_univ_succ]

theorem mul_timeBlock_first (A : Matrix (Fin 3) (Fin 2) ℝ) (i : Fin 3) :
    (A*timeBlock) i 0 = 0 := by
  simp [timeBlock, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The velocity column of the actual time-extended exponential. -/
def bodyVelocity (q a p : Vec3) : Vec3 := fun i =>
  exp (Preintegration.block (skew q) (columns a p) timeBlock) (Sum.inl i) (Sum.inr 0)

theorem bodyVelocity_eq (q a p : Vec3) : bodyVelocity q a p = Jacobian.leftAt q a := by
  have hz : enorm q = 0 → skew q = 0 := by
    intro h; rw [(enorm_eq_zero_iff q).mp h, skew_zero]
  have he := Preintegration.exp_block_all (skew q) (columns a p)
    timeBlock (enorm q) 1 (skew_cube q) hz timeBlock_sq
  simp only [one_smul] at he
  ext i
  simp only [bodyVelocity, he, Matrix.fromBlocks_apply₁₂]
  have hj := congrFun (congrFun (jacobian_columns q a p) i) 0
  rw [← translation_is_jacobian] at hj
  change _ = Jacobian.leftAt q a i at hj
  rw [← hj]
  by_cases hq : enorm q = 0
  · simp [Preintegration.translationAll, hq, mul_timeBlock_first]
  · simp [Preintegration.translationAll, hq, Preintegration.translation,
      mul_timeBlock_first]

def biasTestVelocity (b : ℝ) : Vec3 :=
  bodyVelocity
    (rotationIncrement 1 (![0,0,-12] - b • ![1,0,0]) ![0,0,24])
    (velocityIncrement 1 (![0,0,-12] - b • ![1,0,0]) ![0,0,1] ![0,0,24] 0)
    (positionIncrement 1 0)

theorem biasTestVelocity_formula (b : ℝ) :
    biasTestVelocity b = Jacobian.leftAt (b • ![-1,2,0]) ![0,0,1] := by
  rw [biasTestVelocity, bodyVelocity_eq]
  congr 1 <;> ext i <;> fin_cases i <;>
    norm_num [rotationIncrement, velocityIncrement, crossProduct, cons_val_two, vecHead, vecTail] <;> ring

theorem biasTestVelocity_derivative :
    HasDerivAt biasTestVelocity (![1,1/2,0] : Vec3) 0 := by
  have h := Jacobian.leftAt_derivative_zero (![-1,2,0] : Vec3) ![0,0,1]
  have hc : (1/2:ℝ) • crossProduct (![-1,2,0] : Vec3) ![0,0,1] =
      (![1,1/2,0] : Vec3) := by
    ext i; fin_cases i <;> norm_num [crossProduct, cons_val_two, vecHead, vecTail]
  rw [hc] at h
  simpa only [← biasTestVelocity_formula] using h

def testBias : ℝ := π / sqrt 5

theorem testBias_sq : testBias^2 = π^2/5 := by
  have hs : (sqrt (5:ℝ))^2 = 5 := Real.sq_sqrt (by norm_num)
  dsimp [testBias]
  rw [div_pow, hs]

theorem test_angle : enorm (testBias • (![-1,2,0] : Vec3)) = π := by
  have he : enorm (![-1,2,0] : Vec3)^2 = 5 := by
    norm_num [enorm_sq, lengthSq, cons_val_two, vecHead, vecTail]
  have hn : enorm (![-1,2,0] : Vec3) = sqrt 5 := by
    nlinarith [enorm_nonneg (![-1,2,0] : Vec3), Real.sqrt_nonneg (5:ℝ),
      Real.sq_sqrt (show (0:ℝ) ≤ 5 by norm_num)]
  rw [enorm_smul, hn, abs_of_pos (show 0 < testBias from
    div_pos pi_pos (Real.sqrt_pos.mpr (by norm_num)))]
  dsimp [testBias]
  field_simp

theorem biasTestVelocity_vertical : biasTestVelocity testBias 2 = 0 := by
  rw [biasTestVelocity_formula]
  rw [Jacobian.leftAt, test_angle]
  simp [crossProduct, cons_val_two, vecHead, vecTail]
  have hp : π ≠ 0 := pi_ne_zero
  have hs := testBias_sq
  field_simp
  nlinarith

/-- Proposition 8's claimed bound is 1/2 · sup|a| · T³ · |db|². Here
T=1, a(t)=e₃, db=testBias·e₁, and the exact first derivative is checked above.
The actual remainder has a vertical component -1, larger than π²/10. -/
theorem velocity_bias_bound_counterexample :
    (1/2:ℝ) * testBias^2 <
      enorm (biasTestVelocity testBias - biasTestVelocity 0 - testBias • ![1,1/2,0]) := by
  let e := biasTestVelocity testBias - biasTestVelocity 0 - testBias • ![1,1/2,0]
  have hz : biasTestVelocity 0 = (![0,0,1] : Vec3) := by
    rw [biasTestVelocity_formula]; simp [Jacobian.leftAt]
  have he : e 2 = -1 := by
    change biasTestVelocity testBias 2 - biasTestVelocity 0 2 -
      testBias * (![1,1/2,0] : Vec3) 2 = -1
    rw [biasTestVelocity_vertical, hz]
    norm_num [cons_val_two, vecHead, vecTail]
  have hn : 1 ≤ enorm e := by
    have hh := enorm_sq e
    rw [lengthSq, he] at hh
    nlinarith [enorm_nonneg e, sq_nonneg (e 0), sq_nonneg (e 1)]
  have hp : π^2 < 10 := by nlinarith [Real.pi_lt_d2, pi_pos]
  have hb : (1/2:ℝ)*testBias^2 < 1 := by rw [testBias_sq]; linarith
  exact lt_of_lt_of_le hb hn

/-- The failure is also local in bias: the vertical remainder's quadratic
coefficient is 5/6, exceeding Proposition 8's proposed 1/2. -/
theorem velocity_bias_quadratic_limit :
    Tendsto (fun b : ℝ => (1-biasTestVelocity b 2)/b^2) (𝓝[≠] 0) (𝓝 (5/6:ℝ)) := by
  let z : ℝ → ℝ := fun b => enorm (b • (![-1,2,0] : Vec3))
  have hzlim : Tendsto z (𝓝 0) (𝓝 0) := by
    have hc : Continuous z := enorm_continuous.comp (continuous_id.smul continuous_const)
    have hz : z 0 = 0 := by
      change enorm ((0:ℝ) • (![-1,2,0] : Vec3)) = 0
      rw [zero_smul]
      exact (enorm_eq_zero_iff 0).mpr rfl
    simpa only [hz] using hc.tendsto (0:ℝ)
  have hc : Tendsto (fun _ : ℝ => (5/6:ℝ)) (𝓝 0) (𝓝 (5/6:ℝ)) := tendsto_const_nhds
  have hl := hc.sub
    ((hzlim.pow 2).div_const 24) |>.sub
    (((hzlim.pow 2).const_mul 5).mul (Coefficients.sinRemainder_tendsto.comp hzlim))
  have hm : Tendsto (fun b => (5/6:ℝ)-(z b)^2/24-
      5*(z b)^2*Coefficients.sinRemainder (z b)) (𝓝[≠] 0) (𝓝 (5/6:ℝ)) := by
    simpa using hl.mono_left nhdsWithin_le_nhds
  apply hm.congr'
  filter_upwards [self_mem_nhdsWithin] with b hb
  have hb0 : b ≠ 0 := hb
  have hzsq : (z b)^2 = 5*b^2 := by
    dsimp [z]; rw [enorm_sq]
    norm_num [lengthSq, cons_val_two, vecHead, vecTail]; ring
  have hz0 : z b ≠ 0 := by
    intro h; rw [h] at hzsq
    nlinarith [sq_pos_of_ne_zero hb0]
  have hv : biasTestVelocity b 2 = 1-5*b^2*(z b-sin (z b))/(z b)^3 := by
    rw [biasTestVelocity_formula, Jacobian.leftAt]
    change ( (![0,0,1] + ((1-cos (z b))/(z b)^2) •
      crossProduct (b • ![-1,2,0]) ![0,0,1] +
      ((z b-sin (z b))/(z b)^3) • crossProduct (b • ![-1,2,0])
        (crossProduct (b • ![-1,2,0]) ![0,0,1]) : Vec3) ) 2 = _
    simp [crossProduct, cons_val_two, vecHead, vecTail]
    ring
  rw [hv]
  unfold Coefficients.sinRemainder
  field_simp
  ring

theorem velocity_bias_bound_fails_near_zero :
    ∀ᶠ b : ℝ in 𝓝[≠] 0, (1/2:ℝ)*b^2 <
      enorm (biasTestVelocity b - biasTestVelocity 0 - b • ![1,1/2,0]) := by
  have h := velocity_bias_quadratic_limit.eventually
    (lt_mem_nhds (show (1/2:ℝ) < 5/6 by norm_num))
  filter_upwards [h, self_mem_nhdsWithin] with b hb hb0
  have hb' : (1/2:ℝ)*b^2 < 1-biasTestVelocity b 2 :=
    (lt_div_iff₀ (sq_pos_of_ne_zero (show b ≠ 0 from hb0))).mp hb
  let e := biasTestVelocity b - biasTestVelocity 0 - b • ![1,1/2,0]
  have hz : biasTestVelocity 0 = (![0,0,1] : Vec3) := by
    rw [biasTestVelocity_formula]; simp [Jacobian.leftAt]
  have he : e 2 = biasTestVelocity b 2-1 := by
    change biasTestVelocity b 2 - biasTestVelocity 0 2 - b*(![1,1/2,0] : Vec3) 2 = _
    rw [hz]; norm_num [cons_val_two, vecHead, vecTail]
  have hn : -(e 2) ≤ enorm e := by
    have hs := enorm_sq e
    rw [lengthSq] at hs
    nlinarith [enorm_nonneg e, sq_nonneg (e 0), sq_nonneg (e 1)]
  rw [he] at hn
  dsimp [e] at hn
  linarith

end GNC.Magnus
