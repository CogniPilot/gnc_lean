import GNC.Lie.JacobianDerivative

/-! The concrete block inverse and all three inequalities of Theorem 3.
Q is the derivative of J, with existence and inverse differentiation proved in
JacobianDerivative. Identification of this block map with dexp is separate. -/
noncomputable section
open Matrix Real
open scoped Matrix
namespace GNC.Jacobian

theorem inverseAt_add (q u v : Vec3) : inverseAt q (u+v) = inverseAt q u + inverseAt q v := by
  simp [inverseAt]; module

theorem inverseAt_sub' (q u v : Vec3) : inverseAt q (u-v) = inverseAt q u - inverseAt q v := by
  simp [inverseAt]; module

theorem leftAt_add (q u v : Vec3) : leftAt q (u+v) = leftAt q u + leftAt q v := by
  simp [leftAt]; module

theorem leftAt_sub (q u v : Vec3) : leftAt q (u-v) = leftAt q u - leftAt q v := by
  simp [leftAt]; module

@[simp] theorem inverseAt_zero (q : Vec3) : inverseAt q 0 = 0 := by simp [inverseAt]
@[simp] theorem leftAt_zero (q : Vec3) : leftAt q 0 = 0 := by simp [leftAt]
@[simp] theorem Q_zero (q u : Vec3) : Q q u 0 = 0 := by simp [Q]

def blockLeft (x y : LogState) : LogState :=
  ![leftAt (x 2) (y 0) + Q (x 2) (x 0) (y 2),
    leftAt (x 2) (y 1) + Q (x 2) (x 1) (y 2), leftAt (x 2) (y 2)]

def blockInverse (x y : LogState) : LogState :=
  ![inverseAt (x 2) (y 0) - inverseAt (x 2) (Q (x 2) (x 0) (inverseAt (x 2) (y 2))),
    inverseAt (x 2) (y 1) - inverseAt (x 2) (Q (x 2) (x 1) (inverseAt (x 2) (y 2))),
    inverseAt (x 2) (y 2)]

theorem blockInverse_left (x y : LogState) (hq : 0 < enorm (x 2)) (hqπ : enorm (x 2) < 2*π) :
    blockInverse x (blockLeft x y) = y := by
  funext i
  fin_cases i <;>
    simp [blockLeft, blockInverse, inverseAt_add, inverseAt_leftAt (x 2) _ hq hqπ]

theorem blockLeft_inverse (x y : LogState) (hq : 0 < enorm (x 2)) (hqπ : enorm (x 2) < 2*π) :
    blockLeft x (blockInverse x y) = y := by
  funext i
  fin_cases i <;>
    simp [blockLeft, blockInverse, leftAt_sub, leftAt_inverseAt (x 2) _ hq hqπ]

/-- Lemma 1's gravity block, now for the actual finite block inverse. -/
theorem blockInverse_velocityOnly (x : LogState) (v : Vec3) :
    blockInverse x (velocityOnly v) = velocityOnly (inverseAt (x 2) v) := by
  funext i; fin_cases i <;> simp [blockInverse, velocityOnly]

def diagonalRemainder (q v : Vec3) : Vec3 :=
  (Coefficients.beta (enorm q)/enorm q^2) • (q ⨯₃ (q ⨯₃ v))

theorem diagonalRemainder_axis (k v : Vec3) (hk : k ⬝ᵥ k = 1) (t : ℝ) (ht : 0 < t) :
    diagonalRemainder (t • k) v = -Coefficients.beta t • Axis.transverse k v := by
  have hn : enorm (t • k) = t := by
    rw [enorm_smul, Gravity.unit_enorm k hk, abs_of_pos ht, mul_one]
  simp only [diagonalRemainder, hn, map_smul, LinearMap.smul_apply, smul_smul, Axis.cross_sq k v hk]
  unfold Axis.transverse
  match_scalars <;> field_simp <;> ring

theorem diagonalRemainder_bound (k v : Vec3) (hk : k ⬝ᵥ k = 1)
    (t : ℝ) (ht : 0 < t) (htπ : t < π) :
    enorm (diagonalRemainder (t • k) v) ≤ Coefficients.beta t*enorm v := by
  rw [diagonalRemainder_axis k v hk t ht, enorm_smul, abs_neg,
    abs_of_pos (Coefficients.beta_pos t ht htπ)]
  apply mul_le_mul_of_nonneg_left _ (Coefficients.beta_pos t ht htπ).le
  have hs := Axis.transverse_sq k v hk
  have hn : lengthSq (Axis.transverse k v) ≤ 1^2*lengthSq v := by nlinarith [sq_nonneg (k ⬝ᵥ v)]
  simpa using norm_le_of_sq_le (by norm_num : (0:ℝ) ≤ 1) hn

def controlInput (da dw : Vec3) : LogState := ![0,da,dw]

def controlResidual (x : LogState) (da dw : Vec3) : LogState :=
  ![M (x 2) (x 0) dw,
    diagonalRemainder (x 2) da + M (x 2) (x 1) dw,
    diagonalRemainder (x 2) dw]

/-- Exact inverse decomposition (61), for the stated control-input structure. -/
theorem control_decomposition (x : LogState) (da dw : Vec3) :
    blockInverse x (controlInput da dw) = controlInput da dw +
      mismatchCorrection (controlInput da dw) x + controlResidual x da dw := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockInverse, controlInput, mismatchCorrection, ad, controlResidual,
      M, inverseAt, diagonalRemainder, cross_apply, Matrix.vecHead, Matrix.vecTail] <;> ring

/-- All three estimates (63)–(65), with every analytic bound discharged. -/
theorem control_residual_bounds (p v k da dw : Vec3) (hk : k ⬝ᵥ k = 1)
    (t : ℝ) (ht : 0 < t) (htπ : t < π) :
    let ε := controlResidual ![p,v,t • k] da dw
    enorm (ε 0) ≤ Coefficients.alpha t*enorm p*enorm dw ∧
    enorm (ε 1) ≤ Coefficients.beta t*enorm da + Coefficients.alpha t*enorm v*enorm dw ∧
    enorm (ε 2) ≤ Coefficients.beta t*enorm dw := by
  dsimp [controlResidual]
  exact ⟨M_bound k p dw hk t ht htπ,
    (enorm_add_le _ _).trans (add_le_add (diagonalRemainder_bound k da hk t ht htπ)
      (M_bound k v dw hk t ht htπ)), diagonalRemainder_bound k dw hk t ht htπ⟩

end GNC.Jacobian
