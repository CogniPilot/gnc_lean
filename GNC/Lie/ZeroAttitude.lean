import GNC.Lie.GroupDifferential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-! The removable zero-attitude case. Differentiability comes from the
actual matrix exponential. Its odd part determines DJ(0), so no unproved
Taylor expansion of a quotient is needed. -/
noncomputable section
open Matrix Real Filter
open scoped Matrix Matrix.Norms.Operator Topology
namespace GNC

theorem enorm_continuous : Continuous enorm :=
  (WithLp.linearEquiv 2 ℝ Vec3).symm.toLinearMap.toContinuousLinearMap.continuous.norm

namespace Jacobian

/-- J(q)v is differentiable at every q, including q=0, because it is a
translation column of the matrix exponential. -/
theorem leftAt_differentiable (v q : Vec3) : DifferentiableAt ℝ (fun r => leftAt r v) q := by
  have hl : DifferentiableAt ℝ (fun r : Vec3 => (![v,0,r] : LogState)) q := by
    apply differentiableAt_pi.mpr
    intro i; fin_cases i <;> dsimp <;> fun_prop
  have he := (matrixExp_differentiable (![v,0,q] : LogState)).comp q hl
  apply differentiableAt_pi.mpr
  intro i
  have hf : (fun r => leftAt r v i) =
      (fun r : Vec3 => NormedSpace.exp (hat ![v,0,r]) (i.castAdd 2) 4) := by
    funext r
    have h := congrFun (congrFun (groupExp_toMatrix (![v,0,r] : LogState)) (i.castAdd 2)) 4
    fin_cases i <;> exact h
  rw [hf]
  exact differentiableAt_pi.mp (differentiableAt_pi.mp he (i.castAdd 2)) 4

/-- The odd part is a continuous sinc coefficient times the cross product. -/
theorem leftAt_odd (q v : Vec3) :
    leftAt q v-leftAt (-q) v = (sinc (enorm q/2))^2 • (q ⨯₃ v) := by
  by_cases hq : enorm q = 0
  · rw [(enorm_eq_zero_iff q).mp hq]
    simp [leftAt]
  · rw [sinc_of_ne_zero (div_ne_zero hq (by norm_num))]
    simp only [leftAt, enorm_neg, map_neg, LinearMap.neg_apply, neg_neg]
    rw [half_cos (enorm q)]
    match_scalars <;> field_simp <;> ring

theorem continuous_smul_line_derivative {c : ℝ → ℝ} (hc : ContinuousAt c 0) (v : Vec3) :
    HasDerivAt (fun s : ℝ => c s • (s • v)) (c 0 • v) 0 := by
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  have h := hc.tendsto.smul_const v
  apply (h.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs0 : s ≠ 0 := hs
  simp only [zero_add, zero_smul, smul_zero, sub_zero, smul_smul]
  congr 1
  field_simp

/-- The directional derivative of J at zero is exactly half the cross product. -/
theorem leftAt_derivative_zero (u v : Vec3) :
    HasDerivAt (fun s : ℝ => leftAt (s • u) v) ((1/2:ℝ) • (u ⨯₃ v)) 0 := by
  have hp : HasDerivAt (fun s : ℝ => s • u) u 0 := by
    simpa using (hasDerivAt_id (0:ℝ)).smul_const u
  have hf : DifferentiableAt ℝ (fun s : ℝ => leftAt (s • u) v) 0 := by
    simpa only [Function.comp_def] using
      (leftAt_differentiable v ((0:ℝ) • u)).comp 0 hp.differentiableAt
  have hg := hf.hasDerivAt
  have hg' : HasDerivAt (fun s : ℝ => leftAt (s • u) v)
      (deriv (fun s : ℝ => leftAt (s • u) v) 0) (-(0:ℝ)) := by simpa using hg
  have hneg := hg'.scomp 0 (hasDerivAt_id (0:ℝ)).neg
  have hdiff := hg.sub hneg
  have he : (fun s : ℝ => leftAt (s • u) v-leftAt ((-s) • u) v) =
      (fun s => (sinc (enorm (s • u)/2))^2 • (s • (u ⨯₃ v))) := by
    funext s
    rw [neg_smul, leftAt_odd, map_smul, LinearMap.smul_apply]
  have hc : ContinuousAt (fun s : ℝ => (sinc (enorm (s • u)/2))^2) 0 := by
    exact ((continuous_sinc.comp ((enorm_continuous.comp
      (continuous_id.smul continuous_const)).div_const 2)).pow 2).continuousAt
  have hd := continuous_smul_line_derivative hc (u ⨯₃ v)
  change HasDerivAt (fun s : ℝ => leftAt (s • u) v-leftAt ((-s) • u) v) _ 0 at hdiff
  rw [he] at hdiff
  have hu := hdiff.unique hd
  simp only [enorm, zero_smul, WithLp.toLp_zero, norm_zero, zero_div, sinc_zero,
    one_pow, one_smul, neg_one_smul, sub_neg_eq_add] at hu
  convert hg using 1
  linear_combination (norm := module) -(1/2:ℝ) • hu

@[simp] theorem Q_at_zero (u v : Vec3) : Q 0 u v = (1/2:ℝ) • (u ⨯₃ v) := by
  simpa only [Q, zero_add] using (leftAt_derivative_zero u v).deriv

@[simp] theorem M_at_zero (u v : Vec3) : M 0 u v = 0 := by
  simp [M, inverseAt, Q_at_zero]

@[simp] theorem diagonalRemainder_at_zero (v : Vec3) : diagonalRemainder 0 v = 0 := by
  simp [diagonalRemainder]

/-- The exact control residual vanishes at zero attitude, including when
translation and angular-velocity mismatch are nonzero. -/
theorem controlResidual_at_zero (x : LogState) (da dw : Vec3) (hx : x 2 = 0) :
    controlResidual x da dw = 0 := by
  ext i j; fin_cases i <;> simp [controlResidual, hx]

theorem leftAt_smul (q v : Vec3) (a : ℝ) : leftAt q (a • v) = a • leftAt q v := by
  simp only [leftAt, map_smul, smul_add, smul_smul]
  module

theorem leftAt_moving_derivative_zero (u v w : Vec3) :
    HasDerivAt (fun s : ℝ => leftAt (s • u) (v+s • w))
      (w+(1/2:ℝ) • (u ⨯₃ v)) 0 := by
  have h := (leftAt_derivative_zero u v).add
    ((hasDerivAt_id (0:ℝ)).smul (leftAt_derivative_zero u w))
  have hz (z : Vec3) : leftAt 0 z = z := by simp [leftAt]
  simp only [id_eq, zero_smul, hz, add_zero, one_smul] at h
  simp_rw [leftAt_add, leftAt_smul]
  convert h using 1 <;> module

/-- The finite inverse block formula also inverts the actual Jacobian at zero. -/
theorem blockInverse_left_all (x y : LogState) (hqπ : enorm (x 2) < 2*π) :
    blockInverse x (blockLeft x y) = y := by
  funext i; fin_cases i <;>
    simp [blockLeft, blockInverse, inverseAt_add, inverseAt_leftAt_all (x 2) _ hqπ]

theorem blockLeft_inverse_all (x y : LogState) (hqπ : enorm (x 2) < 2*π) :
    blockLeft x (blockInverse x y) = y := by
  funext i; fin_cases i <;>
    simp [blockLeft, blockInverse, leftAt_sub, leftAt_inverseAt_all (x 2) _ hqπ]

end Jacobian

theorem rotationExp_derivative_zero (u : Vec3) :
    HasDerivAt (fun s : ℝ => (rotationExp (s • u)).val) (skew u) 0 := by
  simpa only [rotationExp, skew_smul, zero_smul, NormedSpace.exp_zero, one_mul] using
    hasDerivAt_exp_smul_const (skew u) (0:ℝ)

/-- Missing zero-attitude case of the full SE₂(3) differential. Translation
components may be arbitrary; this is not limited to the group identity. -/
theorem matrixExp_affine_derivative_zero (x y : LogState) (hx : x 2 = 0) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp (hat (x+s • y)))
      (hat (Jacobian.blockLeft x y)*NormedSpace.exp (hat x)) 0 := by
  let d : Mat5 := splitMatrix.symm (fromBlocks (skew (y 2))
    (columns (y 1+(1/2:ℝ) • (y 2 ⨯₃ x 1)) (y 0+(1/2:ℝ) • (y 2 ⨯₃ x 0))) 0 0)
  have hd : hat (Jacobian.blockLeft x y)*NormedSpace.exp (hat x) = d := by
    rw [← groupExp_toMatrix]
    apply splitMatrix.injective
    simp only [d, AlgEquiv.apply_symm_apply, map_mul, split_hat, split_group]
    simp only [Preintegration.block, fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero,
      zero_add, add_zero, Matrix.mul_one]
    have hz (z : Vec3) : Jacobian.leftAt 0 z = z := by simp [Jacobian.leftAt]
    simp only [Jacobian.blockLeft, Matrix.cons_val, groupExp, hx, hz, Jacobian.Q_at_zero]
    have hr : (rotationExp (0:Vec3)).val = 1 := by simp [rotationExp, skew_zero]
    rw [hr, Matrix.mul_one]
    congr 1
    have ht (v w : Vec3) : skew (y 2) *ᵥ v + (w+(1/2:ℝ) • (v ⨯₃ y 2)) =
        w+(1/2:ℝ) • (y 2 ⨯₃ v) := by
      rw [skew_mulVec, ← cross_anticomm (y 2) v]
      module
    ext i j
    fin_cases j
    · exact congrFun (ht (x 1) (y 1)) i
    · exact congrFun (ht (x 0) (y 0)) i
  have hr := rotationExp_derivative_zero (y 2)
  have hv := Jacobian.leftAt_moving_derivative_zero (y 2) (x 1) (y 1)
  have hp := Jacobian.leftAt_moving_derivative_zero (y 2) (x 0) (y 0)
  rw [hd]
  simp_rw [← groupExp_toMatrix]
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  fin_cases i <;> fin_cases j <;>
    simp only [SE23.toMatrix, groupExp, Pi.add_apply, Pi.smul_apply, hx, zero_add,
      Matrix.cons_val] <;> first
    | exact hasDerivAt_pi.mp (hasDerivAt_pi.mp hr _) _
    | exact hasDerivAt_pi.mp hv _
    | exact hasDerivAt_pi.mp hp _
    | exact hasDerivAt_const (0:ℝ) (0:ℝ)
    | exact hasDerivAt_const (0:ℝ) (1:ℝ)

theorem matrixExp_affine_derivative_all (x y : LogState) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp (hat (x+s • y)))
      (hat (Jacobian.blockLeft x y)*NormedSpace.exp (hat x)) 0 := by
  by_cases hx : x 2 = 0
  · exact matrixExp_affine_derivative_zero x y hx
  · exact matrixExp_affine_derivative x y
      (lt_of_le_of_ne (enorm_nonneg _) (Ne.symm (mt (enorm_eq_zero_iff _).mp hx)))

theorem matrixExp_fderiv_all (x y : LogState) :
    fderiv ℝ (fun z : LogState => NormedSpace.exp (hat z)) x y =
      hat (Jacobian.blockLeft x y)*NormedSpace.exp (hat x) := by
  have hp : HasDerivAt (fun s : ℝ => x+s • y) y 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const y).const_add x
  have hF : HasFDerivAt (fun z : LogState => NormedSpace.exp (hat z))
      (fderiv ℝ (fun z : LogState => NormedSpace.exp (hat z)) x) (x+(0:ℝ) • y) := by
    simpa using (matrixExp_differentiable x).hasFDerivAt
  have he := hF.comp_hasDerivAt 0 hp
  simpa using he.unique (matrixExp_affine_derivative_all x y)

theorem matrixExp_curve_derivative_all {x : ℝ → LogState} {y : LogState} {t : ℝ}
    (hx : HasDerivAt x y t) :
    HasDerivAt (fun s => NormedSpace.exp (hat (x s)))
      (hat (Jacobian.blockLeft (x t) y)*NormedSpace.exp (hat (x t))) t := by
  have he := (matrixExp_differentiable (x t)).hasFDerivAt.comp_hasDerivAt t hx
  simpa only [matrixExp_fderiv_all (x t) y] using he

end GNC
