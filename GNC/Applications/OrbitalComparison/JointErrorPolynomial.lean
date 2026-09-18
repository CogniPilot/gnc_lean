import GNC.Applications.OrbitalComparison.LieRadiusPolynomial
import GNC.Dynamics.LieRadiusCubicEnclosure
import GNC.Dynamics.LieRadiusSpatialApproximation

/-! Executable three-axis Lie/scalar expressions and their exact semantics.
The reference and force are polynomial checking surrogates. Their errors,
the Jacobian tail, ranges and physical closure must be charged separately.
Time is normalized and the known reference radius is one. -/
namespace GNC.OrbitalComparison.JointErrorPolynomial
open ParameterPolynomial PointingCapPolynomial LieSTTOutput Matrix

structure Input where
  K : ℚ
  rho : PointingCapPolynomial.Vector
  h : Coefficients
  reference : PointingCapPolynomial.Vector
  force : PointingCapPolynomial.Vector

def phi : PointingCapPolynomial.Vector := ![u,v,c]
def square : Coefficients := LieRadiusPolynomial.dot phi phi
def firstCoefficient : Coefficients :=
  add (subtract (constant (1/2)) (scale (1/24) square))
    (subtract (scale (1/720) (multiply square square))
      (scale (1/40320) (multiply square (multiply square square))))
def secondCoefficient : Coefficients :=
  add (subtract (constant (1/6)) (scale (1/120) square))
    (subtract (scale (1/5040) (multiply square square))
      (scale (1/362880) (multiply square (multiply square square))))
def Input.displacement (D : Input) : PointingCapPolynomial.Vector := fun i =>
  add (add (D.rho i) (multiply firstCoefficient (cross phi D.rho i)))
    (multiply secondCoefficient (cross phi (cross phi D.rho) i))
def Input.inverse (D : Input) : PointingCapPolynomial.Vector := fun i =>
  add (subtract (D.reference i) (scale (1/2) (cross phi D.reference i)))
    (scale (1/12) (cross phi (cross phi D.reference) i))
def Input.coupled (D : Input) : PointingCapPolynomial.Vector := fun i =>
  add (D.rho i) (D.inverse i)
def Input.cube (D : Input) : Coefficients :=
  let a := add (constant 1) D.h
  multiply (multiply a a) a
def Input.baseResidual (D : Input) : PointingCapPolynomial.Vector := fun i =>
  subtract (add (ParameterPolynomial.derivative (ParameterPolynomial.derivative (D.rho i)))
    (scale D.K (D.rho i))) (cross phi D.force i)
/-- Sharing the coefficient preserves cancellations before range bounding. -/
def Input.residualWith (D : Input) (a : Coefficients) : PointingCapPolynomial.Vector := fun i =>
  add (D.baseResidual i) (scale D.K (multiply (subtract a (constant 1)) (D.coupled i)))
def Input.residual (D : Input) : PointingCapPolynomial.Vector := D.residualWith D.cube
def Input.radius (D : Input) : Coefficients :=
  let gamma := add (subtract (multiply firstCoefficient firstCoefficient)
    (scale 2 secondCoefficient)) (multiply square (multiply secondCoefficient secondCoefficient))
  add (add (constant 1) (scale 2 (LieRadiusPolynomial.dot D.reference D.displacement)))
    (add (LieRadiusPolynomial.dot D.rho D.rho)
      (multiply gamma (LieRadiusPolynomial.dot (cross phi D.rho) (cross phi D.rho))))
def Input.constraint (D : Input) : Coefficients :=
  let a := add (constant 1) D.h
  subtract (multiply D.radius (multiply a a)) (constant 1)

noncomputable section

theorem phi_value (x : Fin 3 → ℝ) (t : ℝ) : value3 phi x t=x := by
  ext i
  fin_cases i <;> simp [phi,value3]

theorem square_value (x : Fin 3 → ℝ) (t : ℝ) : value square x t=lengthSq x := by
  rw [square,LieRadiusPolynomial.dot_value,phi_value,dot_self_lengthSq]

theorem firstCoefficient_value (x : Fin 3 → ℝ) (t : ℝ) :
    value firstCoefficient x t=JacobianPolynomial.firstCoefficient (lengthSq x) := by
  simp [firstCoefficient,value_add,value_subtract,value_constant,value_scale,
    value_multiply,square_value,JacobianPolynomial.firstCoefficient]
  ring

theorem secondCoefficient_value (x : Fin 3 → ℝ) (t : ℝ) :
    value secondCoefficient x t=JacobianPolynomial.secondCoefficient (lengthSq x) := by
  simp [secondCoefficient,value_add,value_subtract,value_constant,value_scale,
    value_multiply,square_value,JacobianPolynomial.secondCoefficient]
  ring

theorem Input.displacement_value (D : Input) (x : Fin 3 → ℝ) (t : ℝ) :
    value3 D.displacement x t=JacobianPolynomial.apply x (value3 D.rho x t) := by
  have h1 := cross_value phi D.rho x t
  have h2 := cross_value phi (cross phi D.rho) x t
  rw [phi_value] at h1 h2
  rw [h1] at h2
  ext i
  simp only [Input.displacement,value3,value_add,value_multiply,
    firstCoefficient_value,secondCoefficient_value]
  rw [show value (cross phi D.rho i) x t=(x ⨯₃ value3 D.rho x t) i from congrFun h1 i,
    show value (cross phi (cross phi D.rho) i) x t=(x ⨯₃ (x ⨯₃ value3 D.rho x t)) i from congrFun h2 i]
  rfl

theorem Input.inverse_value (D : Input) (x : Fin 3 → ℝ) (t : ℝ) :
    value3 D.inverse x t=jacobianInverseQuadratic x (value3 D.reference x t) := by
  have h1 := cross_value phi D.reference x t
  have h2 := cross_value phi (cross phi D.reference) x t
  rw [phi_value] at h1 h2
  rw [h1] at h2
  ext i
  simp only [Input.inverse,value3,value_add,value_subtract,value_scale]
  rw [show value (cross phi D.reference i) x t=(x ⨯₃ value3 D.reference x t) i from congrFun h1 i,
    show value (cross phi (cross phi D.reference) i) x t=(x ⨯₃ (x ⨯₃ value3 D.reference x t)) i from congrFun h2 i]
  norm_num [jacobianInverseQuadratic,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,value3]

theorem Input.coupled_value (D : Input) (x : Fin 3 → ℝ) (t : ℝ) :
    value3 D.coupled x t=value3 D.rho x t+jacobianInverseQuadratic x (value3 D.reference x t) := by
  rw [←D.inverse_value]
  ext i
  exact value_add _ _ x t

theorem Input.cube_value (D : Input) (x : Fin 3 → ℝ) (t : ℝ) :
    value D.cube x t=(1+value D.h x t)^3 := by
  simp [Input.cube,value_multiply,value_add,value_constant]
  ring

theorem Input.residualWith_value (D : Input) (a : Coefficients) (x : Fin 3 → ℝ) (t : ℝ) :
    value3 (D.residualWith a) x t=
      value3 (PointingCapPolynomial.derivative (PointingCapPolynomial.derivative D.rho)) x t+
      ((D.K:ℝ)*value a x t) • value3 D.rho x t-x ⨯₃ value3 D.force x t+
      ((D.K:ℝ)*(value a x t-1)) • jacobianInverseQuadratic x (value3 D.reference x t) := by
  rw [LieRadiusFullDefect.coupled_residual_identity]
  have hf := cross_value phi D.force x t
  rw [phi_value] at hf
  have hw := D.coupled_value x t
  ext i
  simp only [Input.residualWith,Input.baseResidual,value3,value_add,value_subtract,
    value_scale,value_multiply,value_constant,Rat.cast_one,
    PointingCapPolynomial.derivative,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
  rw [show value (cross phi D.force i) x t=(x ⨯₃ value3 D.force x t) i from congrFun hf i,
    show value (D.coupled i) x t=(value3 D.rho x t+jacobianInverseQuadratic x (value3 D.reference x t)) i from congrFun hw i]
  simp only [Pi.add_apply,value3]
  ring

theorem Input.radius_value (D : Input) (x : Fin 3 → ℝ) (t : ℝ) :
    value D.radius x t=1+2*(value3 D.reference x t ⬝ᵥ JacobianPolynomial.apply x (value3 D.rho x t))+
      enorm (JacobianPolynomial.apply x (value3 D.rho x t))^2 := by
  simp only [Input.radius,value_add,value_scale,value_constant,value_multiply,value_subtract,
    LieRadiusPolynomial.dot_value,D.displacement_value,firstCoefficient_value,secondCoefficient_value,
    square_value,cross_value,phi_value,dot_self_lengthSq,←enorm_sq,JacobianPolynomial.apply_gram]
  simp only [Rat.cast_ofNat,Rat.cast_one]
  ring

/-- The stored scalar radius is linked to the exact reconstructed candidate.
Only polynomial reference and Jacobian errors occur in this bound. -/
theorem Input.radius_error (D : Input) (x : Fin 3 → ℝ) (t : ℝ) (q : Vec3)
    (hqnorm : enorm q=1) (hx : enorm x<2*Real.pi) {σ P δ : ℝ}
    (hσ : enorm x≤σ) (hρ : enorm (value3 D.rho x t)≤P)
    (hq : enorm (q-value3 D.reference x t)≤δ) :
    |enorm (q+Jacobian.leftAt x (value3 D.rho x t))^2-value D.radius x t|≤
      2*δ*(1+JacobianPolynomial.tail σ)*P+
      2*(JacobianPolynomial.tail σ*P)+
      (JacobianPolynomial.tail σ*P)*(2*P+JacobianPolynomial.tail σ*P) := by
  have h := LieRadiusSpatialApproximation.radiusApprox_error q (value3 D.reference x t)
    x (value3 D.rho x t) hx hσ hρ hq
  rw [D.radius_value]
  simpa only [LieRadiusSpatialApproximation.radiusApprox,hqnorm,one_pow,mul_one] using h

theorem Input.constraint_value (D : Input) (x : Fin 3 → ℝ) (t : ℝ) :
    value D.constraint x t=value D.radius x t*(1+value D.h x t)^2-1 := by
  simp only [Input.constraint,value_subtract,value_multiply,value_add,value_constant,Rat.cast_one]
  ring

/-- All range obligations refer to the actual executable expressions. This
is a pointwise physical defect, before time integration and first-exit closure. -/
theorem Input.physical_defect (D : Input) (x : Fin 3 → ℝ) (t : ℝ) (q b : Vec3)
    (a : Coefficients) (hK : 0≤(D.K:ℝ)) (hqnorm : enorm q=1)
    (hx : enorm x<2*Real.pi) {σ P H δq δb C R ε : ℝ}
    (hσ : enorm x≤σ) (hρ : enorm (value3 D.rho x t)≤P) (hP : P<1)
    (hh : |value D.h x t|≤H) (hH : H<1)
    (hq : enorm (q-value3 D.reference x t)≤δq)
    (hb : enorm (b-value3 D.force x t)≤δb)
    (hc : |value D.constraint x t|≤C)
    (hcube : |(1+value D.h x t)^3-value a x t|≤ε)
    (hR : enorm (value3 (D.residualWith a) x t)≤R) :
    enorm (Gravity.field3 (D.K:ℝ) q+b+
      Jacobian.leftAt x (value3 (PointingCapPolynomial.derivative
        (PointingCapPolynomial.derivative D.rho)) x t)-
      (Gravity.field3 (D.K:ℝ) (q+Jacobian.leftAt x (value3 D.rho x t))+
        rotate (rotationExp x) b))≤
      LieRadiusFullDefect.budget (D.K:ℝ) 1 σ P H δq δb
        (2*δq*(1+JacobianPolynomial.tail σ)*P+2*(JacobianPolynomial.tail σ*P)+
          (JacobianPolynomial.tail σ*P)*(2*P+JacobianPolynomial.tail σ*P)) C
        (R+(D.K:ℝ)*ε*enorm (value3 D.coupled x t)) := by
  have hr : 0<enorm q := by rw [hqnorm]; norm_num
  have hp : P<enorm q := by simpa only [hqnorm] using hP
  have he := D.radius_error x t q hqnorm hx hσ hρ hq
  have he' : |(enorm (q+Jacobian.leftAt x (value3 D.rho x t))^2/enorm q^2-1)-
      (value D.radius x t-1)|≤
      2*δq*(1+JacobianPolynomial.tail σ)*P+2*(JacobianPolynomial.tail σ*P)+
      (JacobianPolynomial.tail σ*P)*(2*P+JacobianPolynomial.tail σ*P) := by
    simpa only [hqnorm,one_pow,div_one,sub_sub_sub_cancel_right] using he
  have hc' : |(1+(value D.radius x t-1))*(1+value D.h x t)^2-1|≤C := by
    rw [show 1+(value D.radius x t-1)=value D.radius x t by ring,←D.constraint_value]
    exact hc
  have hr' : enorm (value3 (PointingCapPolynomial.derivative
        (PointingCapPolynomial.derivative D.rho)) x t+
      ((D.K:ℝ)/enorm q^3*value a x t) • value3 D.rho x t-x ⨯₃ value3 D.force x t+
      ((D.K:ℝ)/enorm q^3*(value a x t-1)) •
        jacobianInverseQuadratic x (value3 D.reference x t))≤R := by
    simpa only [hqnorm,one_pow,div_one,←D.residualWith_value] using hR
  have h := LieRadiusFullDefect.physical_defect_of_cubic_enclosure
    (D.K:ℝ) hK x q (value3 D.reference x t) (value3 D.rho x t)
    (value3 (PointingCapPolynomial.derivative (PointingCapPolynomial.derivative D.rho)) x t)
    b (value3 D.force x t) (value D.h x t) (value D.radius x t-1) (value a x t)
    hr hx hσ hρ hp hh hH hq hb he' hc' hcube hr'
  simpa only [hqnorm,one_pow,div_one,D.coupled_value] using h

end
end GNC.OrbitalComparison.JointErrorPolynomial
