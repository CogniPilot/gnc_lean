import GNC.Applications.OrbitalComparison.LieRadiusQuadraticPolynomial
import GNC.Dynamics.SmallOffsetDefect

/-! Retained Lie-coordinate checking expressions. The delivered output uses
the exact Jacobian; every higher inverse-radius product and quadratic-radius
remainder is charged separately. These identities do not drop field terms. -/
namespace GNC.OrbitalComparison.LieReducedPolynomial
open ParameterPolynomial PointingCapPolynomial LieSTTOutput JointErrorPolynomial Matrix

def residual (D : Input) : PointingCapPolynomial.Vector := fun i =>
  add (D.baseResidual i) (scale (3*D.K) (multiply D.h (D.inverse i)))

def constraint (D : Input) : Coefficients :=
  subtract (add (LieRadiusQuadraticPolynomial.radius D) (scale 2 D.h)) (constant 1)

noncomputable section

theorem residual_value (D : Input) (x : Fin 3 → ℝ) (t : ℝ) :
    value3 (residual D) x t=SmallOffsetDefect.retained
      (value3 (PointingCapPolynomial.derivative (PointingCapPolynomial.derivative D.rho)) x t)
      (value3 D.rho x t) (jacobianInverseQuadratic x (value3 D.reference x t))
      (x ⨯₃ value3 D.force x t) (D.K:ℝ) (value D.h x t) := by
  have hf := cross_value phi D.force x t
  rw [phi_value] at hf
  have hi := D.inverse_value x t
  ext i
  simp only [residual,Input.baseResidual,SmallOffsetDefect.retained,
    value3,value_add,value_subtract,value_scale,value_multiply,
    PointingCapPolynomial.derivative,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,
    Rat.cast_mul,Rat.cast_ofNat]
  rw [show value (cross phi D.force i) x t=(x ⨯₃ value3 D.force x t) i from congrFun hf i,
    show value (D.inverse i) x t=(jacobianInverseQuadratic x (value3 D.reference x t)) i
      from congrFun hi i]
  ring

theorem constraint_value (D : Input) (x : Fin 3 → ℝ) (t : ℝ) :
    value (constraint D) x t=value (LieRadiusQuadraticPolynomial.radius D) x t+2*value D.h x t-1 := by
  simp only [constraint,value_subtract,value_add,value_scale,value_constant,
    Rat.cast_one,Rat.cast_ofNat]

theorem quadratic_norm (φ v : Vec3) :
    enorm (LieRadiusQuadratic.apply φ v)≤(1+enorm φ/2+enorm φ^2/6)*enorm v := by
  have h1 := cross_enorm_le φ v
  have h2 := (cross_enorm_le φ (φ ⨯₃ v)).trans
    (mul_le_mul_of_nonneg_left h1 (enorm_nonneg φ))
  have ha := (enorm_add_le (v+(1/2:ℝ) • (φ ⨯₃ v))
    ((1/6:ℝ) • (φ ⨯₃ (φ ⨯₃ v)))).trans (add_le_add
    (enorm_add_le v ((1/2:ℝ) • (φ ⨯₃ v))) le_rfl)
  simp only [enorm_smul] at ha
  norm_num at ha
  unfold LieRadiusQuadratic.apply
  nlinarith

theorem radius_difference_growth (q φ ρ : Vec3) (t : ℝ) {Q J P : ℝ}
    (hq : enorm q≤Q) (hρ : enorm ρ≤P*t^2)
    (hJ : enorm (LieRadiusQuadratic.apply φ ρ)≤J*(P*t^2)) :
    |(1+2*(q ⬝ᵥ LieRadiusQuadratic.apply φ ρ)+enorm ρ^2)-1|≤
      2*(Q*J)*P*t^2+P^2*t^4 := by
  have hQ := (enorm_nonneg _).trans hq
  have hP := (enorm_nonneg _).trans hρ
  have hd := (LieRadiusApproximation.abs_dot_bound q (LieRadiusQuadratic.apply φ ρ)).trans
    (mul_le_mul hq hJ (enorm_nonneg _) hQ)
  have hs := pow_le_pow_left₀ (enorm_nonneg _) hρ 2
  rw [show (1+2*(q ⬝ᵥ LieRadiusQuadratic.apply φ ρ)+enorm ρ^2)-1=
    2*(q ⬝ᵥ LieRadiusQuadratic.apply φ ρ)+enorm ρ^2 by ring]
  apply (abs_add_le _ _).trans
  rw [abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2),abs_of_nonneg (sq_nonneg (enorm ρ))]
  convert add_le_add (mul_le_mul_of_nonneg_left hd (by norm_num : (0:ℝ)≤2)) hs using 1 <;> ring

end
end GNC.OrbitalComparison.LieReducedPolynomial
