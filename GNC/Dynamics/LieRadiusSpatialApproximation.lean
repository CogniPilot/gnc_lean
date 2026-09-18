import GNC.Lie.JacobianPolynomial
import GNC.Dynamics.LieRadiusApproximation

/-! A scalar radius check for a full three-axis attitude ball. The known
reference radius is retained exactly. Only its projection onto the Lie
translation and the scalar Gram expression need polynomial evaluation;
three Cartesian trajectory polynomials need not be propagated. -/
noncomputable section
namespace GNC.LieRadiusSpatialApproximation
open Matrix Real LieRadiusApproximation

/-- Squared-norm perturbation with an explicit absolute error, including
zero vectors. This is used only on the known candidate, not on an assumed
physical reachable tube. -/
theorem squared_norm_error (x y : Vec3) {P ε : ℝ}
    (hx : enorm x≤P) (he : enorm (x-y)≤ε) :
    |enorm x^2-enorm y^2|≤ε*(2*P+ε) := by
  have hP := (enorm_nonneg x).trans hx
  have hε := (enorm_nonneg _).trans he
  have hy : enorm y≤P+ε := by
    have hid : y=x+ -(x-y) := by module
    rw [hid]
    exact (enorm_add_le _ _).trans (by simpa only [enorm_neg] using add_le_add hx he)
  have hsum : enorm (x+y)≤2*P+ε :=
    (enorm_add_le _ _).trans (by linarith)
  have hid : enorm x^2-enorm y^2=(x-y) ⬝ᵥ (x+y) := by
    simp only [enorm_sq,←dot_self_lengthSq,sub_dotProduct,dotProduct_add,
      dotProduct_comm y x]
    ring
  rw [hid]
  exact (abs_dot_bound _ _).trans (mul_le_mul he hsum (enorm_nonneg _) hε)

/-- Radius error from a displacement approximation and known-reference
interpolation. The exact squared reference radius is not approximated. -/
theorem radius_error (q qhat d dhat : Vec3) {P ε δ : ℝ}
    (hd : enorm d≤P) (he : enorm (d-dhat)≤ε) (hq : enorm (q-qhat)≤δ) :
    |enorm (q+d)^2-(enorm q^2+2*(qhat ⬝ᵥ dhat)+enorm dhat^2)|≤
      2*δ*(P+ε)+2*enorm q*ε+ε*(2*P+ε) := by
  have hP := (enorm_nonneg d).trans hd
  have hε := (enorm_nonneg _).trans he
  have hδ := (enorm_nonneg _).trans hq
  have hdh : enorm dhat≤P+ε := by
    have hid : dhat=d+ -(d-dhat) := by module
    rw [hid]
    exact (enorm_add_le _ _).trans (by simpa only [enorm_neg] using add_le_add hd he)
  have h1 : |(q-qhat) ⬝ᵥ dhat|≤δ*(P+ε) :=
    (abs_dot_bound _ _).trans (mul_le_mul hq hdh (enorm_nonneg _) hδ)
  have h2 : |q ⬝ᵥ (d-dhat)|≤enorm q*ε :=
    (abs_dot_bound _ _).trans (mul_le_mul_of_nonneg_left he (enorm_nonneg q))
  have h3 := squared_norm_error d dhat hd he
  have hid : enorm (q+d)^2-(enorm q^2+2*(qhat ⬝ᵥ dhat)+enorm dhat^2)=
      2*((q-qhat) ⬝ᵥ dhat)+2*(q ⬝ᵥ (d-dhat))+(enorm d^2-enorm dhat^2) := by
    simp only [enorm_sq,←dot_self_lengthSq,add_dotProduct,dotProduct_add,
      sub_dotProduct,dotProduct_sub,dotProduct_comm d q]
    ring
  rw [hid]
  apply (abs_add_le _ _).trans
  apply add_le_add _ h3
  apply (abs_add_le _ _).trans
  norm_num only [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
  convert add_le_add (mul_le_mul_of_nonneg_left h1 (by norm_num : (0:ℝ)≤2))
    (mul_le_mul_of_nonneg_left h2 (by norm_num : (0:ℝ)≤2)) using 1 <;> ring

/-- The polynomial scalar radius used by the all-axis certificate. Its
last term can be evaluated by `JacobianPolynomial.apply_gram`. -/
def radiusApprox (q qhat φ ρ : Vec3) : ℝ :=
  enorm q^2+2*(qhat ⬝ᵥ JacobianPolynomial.apply φ ρ)+
    enorm (JacobianPolynomial.apply φ ρ)^2

/-- Complete three-axis reconstruction budget. No component-wise angle box
or Taylor allowance for the physical trajectory is assumed. -/
theorem radiusApprox_error (q qhat φ ρ : Vec3) {σ P δ : ℝ}
    (hφ : enorm φ<2*π) (hσ : enorm φ≤σ) (hρ : enorm ρ≤P)
    (hq : enorm (q-qhat)≤δ) :
    |enorm (q+Jacobian.leftAt φ ρ)^2-radiusApprox q qhat φ ρ|≤
      2*δ*(1+JacobianPolynomial.tail σ)*P+
      2*enorm q*(JacobianPolynomial.tail σ*P)+
      (JacobianPolynomial.tail σ*P)*(2*P+JacobianPolynomial.tail σ*P) := by
  have hσ0 := (enorm_nonneg φ).trans hσ
  have hP0 := (enorm_nonneg ρ).trans hρ
  have hd := (leftAt_nonexpansive φ ρ hφ).trans hρ
  have he : enorm (Jacobian.leftAt φ ρ-JacobianPolynomial.apply φ ρ)≤
      JacobianPolynomial.tail σ*P :=
    (JacobianPolynomial.error_bound φ ρ).trans
      (mul_le_mul (JacobianPolynomial.tail_mono (enorm_nonneg φ) hσ) hρ
        (enorm_nonneg _) (JacobianPolynomial.tail_nonneg hσ0))
  convert radius_error q qhat (Jacobian.leftAt φ ρ)
    (JacobianPolynomial.apply φ ρ) hd he hq using 1 <;> dsimp [radiusApprox] <;> ring

end GNC.LieRadiusSpatialApproximation
