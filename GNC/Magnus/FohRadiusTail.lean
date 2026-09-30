import GNC.Magnus.FohSharpResidual

/-! Reusable analytic tail step for the FOH flow certificate.

If the coefficient norms are summable at a larger radius, their tail at
radius ratio x ∈ [0,1] is bounded by x^m times the complete majorant sum.
This proves the radius-tail argument. Identifying the FOH ODE coefficients
with its solution and deriving their exponential scalar majorants remain
separate analytic bridges; neither is silently assumed to be proved here. -/
noncomputable section
namespace GNC.Magnus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Radius reduction bounds the complete infinite tail, not just its leading
coefficient. `v n` represents a coefficient multiplied by the larger radius. -/
theorem foh_radius_tail (v : ℕ → E) (m : ℕ) (x Q : ℝ)
    (hx : 0 ≤ x) (hx1 : x ≤ 1)
    (hs : Summable (fun n => ‖v n‖)) (hQ : (∑' n, ‖v n‖) ≤ Q) :
    ‖∑' n, x^(n+m) • v (n+m)‖ ≤ x^m * Q := by
  have hst : Summable (fun n => ‖v (n+m)‖) :=
    (summable_nat_add_iff m).mpr hs
  have hb : ∀ n, ‖x^(n+m) • v (n+m)‖ ≤ x^m * ‖v (n+m)‖ := by
    intro n
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hx _)]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_of_le_one hx hx1 (Nat.le_add_left m n)) (norm_nonneg _)
  have hsmajor := hst.mul_left (x^m)
  have hsv : Summable (fun n => x^(n+m) • v (n+m)) := hsmajor.of_norm_bounded hb
  have hbound := hsv.hasSum.norm_le_of_bounded hsmajor.hasSum hb
  rw [tsum_mul_left] at hbound
  have hsplit := hs.sum_add_tsum_nat_add m
  have hp : 0 ≤ ∑ i ∈ Finset.range m, ‖v i‖ := Finset.sum_nonneg (fun i _ => norm_nonneg _)
  have ht : (∑' n, ‖v (n+m)‖) ≤ Q := by linarith
  exact hbound.trans (mul_le_mul_of_nonneg_left ht (pow_nonneg hx _))

end GNC.Magnus
