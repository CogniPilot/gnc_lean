import GNC.Magnus.GaussLegendre
import GNC.Analysis.ExponentialCertificate

/-! Error propagation through the actual two-node, left-composed Gauss
Magnus formula. Input perturbation, exponential evaluation and time-ordering
truncation are distinct: this module treats input perturbation only.
-/
noncomputable section
namespace GNC.Magnus

section Algebra
variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- Earlier node first, for the left equation Y' = A(t)Y. -/
def gaussStepExponent (earlier later : A) (h : ℝ) : A :=
  (h/2) • (earlier+later)-(Real.sqrt 3*h^2/12) • comm earlier later

/-- Connect the finite formal polynomial already audited in `GaussLegendre`
to the matrix formula whose norm error is bounded below. -/
theorem gaussStepExponent_eq_eval (a b c d : A) (h : ℝ) :
    (gaussLeftExponent a b c d (Real.sqrt 3/6)).eval (h • (1:A)) =
      gaussStepExponent
        ((nodeSample a b c d (1/2-Real.sqrt 3/6)).eval (h • (1:A)))
        ((nodeSample a b c d (1/2+Real.sqrt 3/6)).eval (h • (1:A))) h := by
  have hm (p q : Polynomial A) :
      (p*q).eval (h • (1:A)) = p.eval (h • (1:A))*q.eval (h • (1:A)) :=
    Polynomial.eval₂_mul_noncomm (RingHom.id A) (h • (1:A))
      (fun k => (Commute.one_right (q.coeff k)).smul_right h)
  simp only [gaussLeftExponent, gaussStepExponent, comm, Polynomial.eval_sub,
    Polynomial.eval_add, Polynomial.eval_smul, hm, Polynomial.eval_monomial,
    pow_one, one_mul, smul_pow, one_pow, smul_mul_assoc, one_mul, smul_smul]
  congr 1 <;> congr 1 <;> ring

end Algebra

section Norm
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

omit [NormedAlgebra ℝ A] in
theorem comm_norm (x y : A) : ‖comm x y‖ ≤ 2*‖x‖*‖y‖ := by
  have h := (norm_sub_le (x*y) (y*x)).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
  dsimp [comm]
  nlinarith

omit [NormedAlgebra ℝ A] in
/-- This asymmetric decomposition uses the computed later node and the
exact earlier node. No product of unknown errors is dropped. -/
theorem comm_perturbation (earlier later earlierHat laterHat : A) :
    ‖comm earlierHat laterHat-comm earlier later‖ ≤
      2*(‖earlierHat-earlier‖*‖laterHat‖+‖earlier‖*‖laterHat-later‖) := by
  have he : comm earlierHat laterHat-comm earlier later =
      comm (earlierHat-earlier) laterHat+comm earlier (laterHat-later) := by
    unfold comm; noncomm_ring
  rw [he]
  have h := (norm_add_le (comm (earlierHat-earlier) laterHat)
    (comm earlier (laterHat-later))).trans (add_le_add
      (comm_norm (earlierHat-earlier) laterHat) (comm_norm earlier (laterHat-later)))
  nlinarith

/-- Explicit propagation of node errors into the Magnus exponent. A bound
for the exact earlier node may be derived from its reported norm plus error.
The time-ordering truncation of the Magnus method is not included here. -/
theorem gauss_exponent_perturbation (earlier later earlierHat laterHat : A)
    {h ε₁ ε₂ M₁ M₂ : ℝ} (hh : 0 ≤ h)
    (he : ‖earlierHat-earlier‖ ≤ ε₁) (hl : ‖laterHat-later‖ ≤ ε₂)
    (hm₁ : ‖earlier‖ ≤ M₁) (hm₂ : ‖laterHat‖ ≤ M₂) :
    ‖gaussStepExponent earlierHat laterHat h-gaussStepExponent earlier later h‖ ≤
      (h/2)*(ε₁+ε₂)+(Real.sqrt 3*h^2/6)*(ε₁*M₂+M₁*ε₂) := by
  have hc : ‖comm earlierHat laterHat-comm earlier later‖ ≤
      2*(ε₁*M₂+M₁*ε₂) := (comm_perturbation _ _ _ _).trans
    (mul_le_mul_of_nonneg_left
      (add_le_add
        (mul_le_mul he hm₂ (norm_nonneg _) ((norm_nonneg _).trans he))
        (mul_le_mul hm₁ hl (norm_nonneg _) ((norm_nonneg _).trans hm₁))) (by norm_num))
  have hs : ‖(earlierHat+laterHat)-(earlier+later)‖ ≤ ε₁+ε₂ := by
    rw [show (earlierHat+laterHat)-(earlier+later) =
      (earlierHat-earlier)+(laterHat-later) by abel]
    exact (norm_add_le _ _).trans (add_le_add he hl)
  have heq : gaussStepExponent earlierHat laterHat h-gaussStepExponent earlier later h =
      (h/2) • ((earlierHat+laterHat)-(earlier+later))-
        (Real.sqrt 3*h^2/12) • (comm earlierHat laterHat-comm earlier later) := by
    unfold gaussStepExponent; module
  rw [heq]
  have hhalf : 0 ≤ h/2 := by positivity
  have hquad : 0 ≤ Real.sqrt 3*h^2/12 := by positivity
  calc
    _ ≤ ‖(h/2) • ((earlierHat+laterHat)-(earlier+later))‖+
        ‖(Real.sqrt 3*h^2/12) • (comm earlierHat laterHat-comm earlier later)‖ :=
      norm_sub_le _ _
    _ ≤ (h/2)*(ε₁+ε₂)+(Real.sqrt 3*h^2/12)*(2*(ε₁*M₂+M₁*ε₂)) := by
      simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hhalf, abs_of_nonneg hquad]
      exact add_le_add (mul_le_mul_of_nonneg_left hs hhalf) (mul_le_mul_of_nonneg_left hc hquad)
    _ = _ := by ring

/-- Input errors propagated all the way through the actual exponential.
This compares the two Gauss steps, not either step with the ODE solution. -/
theorem gauss_step_input_error [CompleteSpace A] [NormOneClass A]
    (earlier later earlierHat laterHat : A) {h ε₁ ε₂ M₁ M₂ r : ℝ} (hh : 0 ≤ h)
    (he : ‖earlierHat-earlier‖ ≤ ε₁) (hl : ‖laterHat-later‖ ≤ ε₂)
    (hm₁ : ‖earlier‖ ≤ M₁) (hm₂ : ‖laterHat‖ ≤ M₂)
    (hr : ‖gaussStepExponent earlier later h‖ ≤ r)
    (hrHat : ‖gaussStepExponent earlierHat laterHat h‖ ≤ r) :
    ‖NormedSpace.exp (gaussStepExponent earlierHat laterHat h)-
      NormedSpace.exp (gaussStepExponent earlier later h)‖ ≤
      Real.exp r*((h/2)*(ε₁+ε₂)+(Real.sqrt 3*h^2/6)*(ε₁*M₂+M₁*ε₂)) := by
  exact (ExponentialCertificate.perturbation_bound _ _ hrHat hr).trans
    (mul_le_mul_of_nonneg_left
      (gauss_exponent_perturbation _ _ _ _ hh he hl hm₁ hm₂) (Real.exp_pos r).le)

end Norm
end GNC.Magnus
