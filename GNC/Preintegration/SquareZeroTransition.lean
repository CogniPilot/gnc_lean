import GNC.Preintegration.EndpointTransition

/-! Dimension-independent square-zero translation coupling. The assumption
`B^2=0` is unchanged when the number of translation columns increases.
This is the class of the ZOH paper, not arbitrary dynamics on SE_n(3).
-/
noncomputable section
open Matrix
open scoped Matrix.Norms.Operator
namespace GNC.Preintegration.Uncertainty
variable {n : Type*} [Fintype n] [DecidableEq n]

def columnTransition (R : SO3) (V E : Matrix (Fin 3) n ℝ)
    (C : Matrix n n ℝ) (θ : Vec3) : Matrix (Fin 3) n ℝ :=
  R⁻¹.val * (skew θ*V+E*C)

/-- All translation columns share the same rotation; only one right
column-coupling matrix enters. This is an exact intertwining identity. -/
theorem columnTransition_intertwine (R : SO3) (V E : Matrix (Fin 3) n ℝ)
    (C : Matrix n n ℝ) (θ : Vec3) :
    fromBlocks R.val V 0 C *
      fromBlocks (skew (rotate R⁻¹ θ)) (columnTransition R V E C θ) 0 0 =
    fromBlocks (skew θ) E 0 0 * fromBlocks R.val V 0 C := by
  have hr := skew_rotate R (rotate R⁻¹ θ)
  simp only [← rotate_mul, mul_inv_cancel, rotate_one] at hr
  have hi : R.val*R⁻¹.val = 1 := by
    change (R*R⁻¹).val = 1
    simp
  simp only [fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero,
    columnTransition, ← Matrix.mul_assoc, hi, Matrix.one_mul, ← hr]

/-- Square-zero coupling is preserved at arbitrary translation dimension. -/
theorem square_zero_clock_inverse (B : Matrix n n ℝ) (hB : B^2=0) (t : ℝ) :
    (1-t • B)*(1+t • B) = 1 ∧ (1+t • B)*(1-t • B) = 1 := by
  constructor <;>
    simp only [sub_mul, add_mul, mul_add, mul_sub, Matrix.one_mul, Matrix.mul_one,
      smul_mul_smul_comm, ← pow_two B, hB, smul_zero] <;> abel

/-- `I+tB` solves the actual lower right-flow ODE exactly. -/
theorem square_zero_clock_derivative (B : Matrix n n ℝ) (hB : B^2=0) (t : ℝ) :
    HasDerivAt (fun s : ℝ => 1+s • B) ((1+t • B)*B) t := by
  have hh : (1+t • B)*B=B := by
    simp [add_mul, smul_mul_assoc, ← pow_two B, hB]
  rw [hh]
  simpa using ((hasDerivAt_id t).smul_const B).const_add 1

/-- The dependence on the square-zero clock needs only `E` and `E B`,
regardless of the number of columns. No powers B² or higher are evaluated. -/
theorem square_zero_column_formula (R : SO3) (V E : Matrix (Fin 3) n ℝ)
    (B : Matrix n n ℝ) (t : ℝ) (θ : Vec3) :
    columnTransition R V E (1+t • B) θ =
      R⁻¹.val*(skew θ*V+E+t • (E*B)) := by
  simp [columnTransition, Matrix.mul_add, Matrix.mul_smul, add_assoc]

/-- With zero rotational residual and one common square-zero clock, every
cross-time product of three triangular generators vanishes. The three input
columns may be different; pointwise nilpotence alone would not suffice. -/
theorem square_zero_clock_cross_time_cube
    (U V W : Matrix (Fin 3) n ℝ) (B : Matrix n n ℝ) (hB : B * B = 0) :
    fromBlocks 0 U 0 B * fromBlocks 0 V 0 B * fromBlocks 0 W 0 B =
      (0 : Matrix (Fin 3 ⊕ n) (Fin 3 ⊕ n) ℝ) := by
  simp [fromBlocks_multiply, Matrix.mul_assoc, hB, fromBlocks_zero]

end GNC.Preintegration.Uncertainty
