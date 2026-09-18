import GNC.Analysis.MixedFlow

/-! Perturbation bound for the exponential in a Banach algebra and the
error bound of Theorem 1 (equation 17): replacing the exact Magnus
exponent `Ξ` by its truncation `Ξ≤3` in `X(T) = e^{MT} X(0) e^{Ξ}` costs at
most `‖X(0)‖ e^{‖MT‖} e^{max(‖Ξ‖,‖Ξ≤3‖)} ‖Ξ - Ξ≤3‖`. -/
noncomputable section
namespace GNC.Magnus
open NormedSpace
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

omit [NormedAlgebra ℝ A] [CompleteSpace A] in
/-- Telescoping bound for consecutive powers: `P^(n+1) - Q^(n+1)` is
`P^n (P - Q) + (P^n - Q^n) Q`, so its norm is at most `(n+1) ‖P - Q‖ m^n`
with `m = max ‖P‖ ‖Q‖`. -/
theorem norm_pow_succ_sub_pow_succ_le (P Q : A) (n : ℕ) :
    ‖P ^ (n + 1) - Q ^ (n + 1)‖ ≤ (n + 1) * ‖P - Q‖ * (max ‖P‖ ‖Q‖) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    set m := max ‖P‖ ‖Q‖ with hm
    have hm0 : 0 ≤ m := le_trans (norm_nonneg P) (le_max_left _ _)
    have hsplit : P ^ (n + 2) - Q ^ (n + 2)
        = P ^ (n + 1) * (P - Q) + (P ^ (n + 1) - Q ^ (n + 1)) * Q := by
      simp only [pow_succ, mul_sub, sub_mul]
      abel
    have hP : ‖P ^ (n + 1)‖ ≤ m ^ (n + 1) :=
      le_trans (norm_pow_le' P (Nat.succ_pos n))
        (pow_le_pow_left₀ (norm_nonneg P) (le_max_left _ _) _)
    have hQ : ‖Q‖ ≤ m := le_max_right _ _
    have hd : 0 ≤ ‖P - Q‖ := norm_nonneg _
    calc ‖P ^ (n + 2) - Q ^ (n + 2)‖
        = ‖P ^ (n + 1) * (P - Q) + (P ^ (n + 1) - Q ^ (n + 1)) * Q‖ := by rw [hsplit]
      _ ≤ ‖P ^ (n + 1) * (P - Q)‖ + ‖(P ^ (n + 1) - Q ^ (n + 1)) * Q‖ := norm_add_le _ _
      _ ≤ ‖P ^ (n + 1)‖ * ‖P - Q‖ + ‖P ^ (n + 1) - Q ^ (n + 1)‖ * ‖Q‖ :=
          add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ m ^ (n + 1) * ‖P - Q‖ + ((n + 1) * ‖P - Q‖ * m ^ n) * m := by
          gcongr
      _ = ((n + 1 : ℕ) + 1) * ‖P - Q‖ * m ^ (n + 1) := by
          push_cast
          ring

omit [NormedAlgebra ℝ A] [CompleteSpace A] in
/-- Lipschitz-type bound for powers: `‖P^n - Q^n‖ ≤ n ‖P - Q‖ m^(n-1)` with
`m = max ‖P‖ ‖Q‖`. -/
theorem norm_pow_sub_pow_le (P Q : A) (n : ℕ) :
    ‖P ^ n - Q ^ n‖ ≤ n * ‖P - Q‖ * (max ‖P‖ ‖Q‖) ^ (n - 1) := by
  cases n with
  | zero => simp
  | succ k =>
    simpa using norm_pow_succ_sub_pow_succ_le P Q k

/-- The exponential series of `m` in `ℝ`, written with the coefficients
`(n!)⁻¹ * m^n`. -/
theorem hasSum_real_exp (m : ℝ) :
    HasSum (fun n : ℕ => (n.factorial : ℝ)⁻¹ * m ^ n) (Real.exp m) := by
  have h := exp_series_hasSum_exp' (𝕂 := ℝ) m
  rw [Real.exp_eq_exp_ℝ]
  simpa [smul_eq_mul] using h

/-- Term-wise derivative of the exponential series:
`∑ n (n!)⁻¹ m^(n-1) = e^m`. -/
theorem hasSum_real_exp_shift (m : ℝ) :
    HasSum (fun n : ℕ => (n.factorial : ℝ)⁻¹ * n * m ^ (n - 1)) (Real.exp m) := by
  rw [← hasSum_nat_add_iff' 1]
  have h := hasSum_real_exp m
  simp only [Finset.sum_range_one, Nat.factorial_zero, Nat.cast_one, inv_one,
    Nat.cast_zero, mul_zero, zero_mul, sub_zero, Nat.add_sub_cancel]
  refine h.congr_fun ?_
  intro n
  rw [Nat.factorial_succ]
  push_cast
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp

/-- Perturbation bound for the exponential in a Banach algebra:
`‖e^P - e^Q‖ ≤ ‖P - Q‖ e^{max(‖P‖,‖Q‖)}`. -/
theorem norm_exp_sub_exp_le (P Q : A) :
    ‖exp P - exp Q‖ ≤ ‖P - Q‖ * Real.exp (max ‖P‖ ‖Q‖) := by
  set m := max ‖P‖ ‖Q‖ with hm
  have hf : HasSum (fun n : ℕ => (n.factorial⁻¹ : ℝ) • P ^ n - (n.factorial⁻¹ : ℝ) • Q ^ n)
      (exp P - exp Q) :=
    (exp_series_hasSum_exp' (𝕂 := ℝ) P).sub (exp_series_hasSum_exp' (𝕂 := ℝ) Q)
  have hg : HasSum (fun n : ℕ => ‖P - Q‖ * ((n.factorial : ℝ)⁻¹ * n * m ^ (n - 1)))
      (‖P - Q‖ * Real.exp m) :=
    (hasSum_real_exp_shift m).mul_left _
  refine hf.norm_le_of_bounded hg ?_
  intro n
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h := norm_pow_sub_pow_le P Q n
  calc (n.factorial : ℝ)⁻¹ * ‖P ^ n - Q ^ n‖
      ≤ (n.factorial : ℝ)⁻¹ * (n * ‖P - Q‖ * m ^ (n - 1)) := by gcongr
    _ = ‖P - Q‖ * ((n.factorial : ℝ)⁻¹ * n * m ^ (n - 1)) := by ring

/-- Norm bound for the exponential: `‖e^X‖ ≤ e^{‖X‖}` (the constant term
requires `‖1‖ ≤ 1`, hence the norm-one hypothesis). -/
theorem norm_exp_le_exp_norm [NormOneClass A] (X : A) :
    ‖exp X‖ ≤ Real.exp ‖X‖ := by
  refine (exp_series_hasSum_exp' (𝕂 := ℝ) X).norm_le_of_bounded (hasSum_real_exp ‖X‖) ?_
  intro n
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  gcongr
  exact norm_pow_le X n

omit [NormedAlgebra ℝ A] [CompleteSpace A] in
/-- Theorem 1, equation (17), factor form: replacing the right factor `R`
by `Rt` in `L X0 R` costs at most `‖L‖ ‖X0‖ ‖R - Rt‖`. -/
theorem flow_truncation_error (X0 L R Rt : A) :
    ‖L * X0 * R - L * X0 * Rt‖ ≤ ‖L‖ * ‖X0‖ * ‖R - Rt‖ := by
  rw [← mul_sub]
  exact le_trans (norm_mul_le _ _) (by gcongr; exact norm_mul_le _ _)

/-- Theorem 1, equation (17), exponent form: truncating the Magnus exponent
`Ξ` to `Ξ₃` in `L X0 e^{Ξ}` costs at most
`‖L‖ ‖X0‖ ‖Ξ - Ξ₃‖ e^{max(‖Ξ‖,‖Ξ₃‖)}`. -/
theorem flow_exponent_truncation_error (X0 L Ξ Ξ₃ : A) :
    ‖L * X0 * exp Ξ - L * X0 * exp Ξ₃‖
      ≤ ‖L‖ * ‖X0‖ * ‖Ξ - Ξ₃‖ * Real.exp (max ‖Ξ‖ ‖Ξ₃‖) := by
  calc ‖L * X0 * exp Ξ - L * X0 * exp Ξ₃‖
      ≤ ‖L‖ * ‖X0‖ * ‖exp Ξ - exp Ξ₃‖ := flow_truncation_error X0 L _ _
    _ ≤ ‖L‖ * ‖X0‖ * (‖Ξ - Ξ₃‖ * Real.exp (max ‖Ξ‖ ‖Ξ₃‖)) := by
        gcongr
        exact norm_exp_sub_exp_le Ξ Ξ₃
    _ = ‖L‖ * ‖X0‖ * ‖Ξ - Ξ₃‖ * Real.exp (max ‖Ξ‖ ‖Ξ₃‖) := by ring

/-- Theorem 1, equation (17), full form: with the left factor `e^{T M}`,
`‖e^{TM} X0 e^{Ξ} - e^{TM} X0 e^{Ξ₃}‖ ≤ ‖X0‖ e^{‖TM‖} e^{max(‖Ξ‖,‖Ξ₃‖)} ‖Ξ - Ξ₃‖`. -/
theorem foh_truncation_error [NormOneClass A] (X0 M Ξ Ξ₃ : A) (T : ℝ) :
    ‖exp (T • M) * X0 * exp Ξ - exp (T • M) * X0 * exp Ξ₃‖
      ≤ ‖X0‖ * Real.exp ‖T • M‖ * Real.exp (max ‖Ξ‖ ‖Ξ₃‖) * ‖Ξ - Ξ₃‖ := by
  calc ‖exp (T • M) * X0 * exp Ξ - exp (T • M) * X0 * exp Ξ₃‖
      ≤ ‖exp (T • M)‖ * ‖X0‖ * ‖Ξ - Ξ₃‖ * Real.exp (max ‖Ξ‖ ‖Ξ₃‖) :=
        flow_exponent_truncation_error X0 _ Ξ Ξ₃
    _ ≤ Real.exp ‖T • M‖ * ‖X0‖ * ‖Ξ - Ξ₃‖ * Real.exp (max ‖Ξ‖ ‖Ξ₃‖) := by
        gcongr
        exact norm_exp_le_exp_norm _
    _ = ‖X0‖ * Real.exp ‖T • M‖ * Real.exp (max ‖Ξ‖ ‖Ξ₃‖) * ‖Ξ - Ξ₃‖ := by ring

end GNC.Magnus
