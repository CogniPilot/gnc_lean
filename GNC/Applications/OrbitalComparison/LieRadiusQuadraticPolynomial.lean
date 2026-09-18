import GNC.Applications.OrbitalComparison.JointErrorPolynomial
import GNC.Dynamics.LieRadiusQuadratic

/-! A lower-degree scalar radius checker for the exact Lie translation.
The physical query still uses the exact Jacobian. The quadratic surrogate
is used only inside the radius proof and its entire remainder is charged.
No attitude products in the checked scalar constraint are discarded. -/
namespace GNC.OrbitalComparison.LieRadiusQuadraticPolynomial
open ParameterPolynomial PointingCapPolynomial LieSTTOutput Matrix
open JointErrorPolynomial

def displacement (D : Input) : PointingCapPolynomial.Vector := fun i =>
  add (add (D.rho i) (scale (1/2) (cross phi D.rho i)))
    (scale (1/6) (cross phi (cross phi D.rho) i))

def radius (D : Input) : Coefficients :=
  add (add (constant 1) (scale 2 (LieRadiusPolynomial.dot D.reference (displacement D))))
    (LieRadiusPolynomial.dot D.rho D.rho)

def constraint (D : Input) : Coefficients :=
  let a := add (constant 1) D.h
  subtract (multiply (radius D) (multiply a a)) (constant 1)

noncomputable section

theorem displacement_value (D : Input) (x : Fin 3 → ℝ) (t : ℝ) :
    value3 (displacement D) x t=LieRadiusQuadratic.apply x (value3 D.rho x t) := by
  have h1 := cross_value phi D.rho x t
  have h2 := cross_value phi (cross phi D.rho) x t
  rw [phi_value] at h1 h2
  rw [h1] at h2
  ext i
  simp only [displacement,value3,value_add,value_scale]
  rw [show value (cross phi D.rho i) x t=(x ⨯₃ value3 D.rho x t) i from congrFun h1 i,
    show value (cross phi (cross phi D.rho) i) x t=(x ⨯₃ (x ⨯₃ value3 D.rho x t)) i
      from congrFun h2 i]
  norm_num [LieRadiusQuadratic.apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul,value3]

theorem radius_value (D : Input) (x : Fin 3 → ℝ) (t : ℝ) :
    value (radius D) x t=1+2*(value3 D.reference x t ⬝ᵥ
      LieRadiusQuadratic.apply x (value3 D.rho x t))+enorm (value3 D.rho x t)^2 := by
  simp only [radius,value_add,value_constant,value_scale,LieRadiusPolynomial.dot_value,
    displacement_value,dot_self_lengthSq,←enorm_sq,Rat.cast_one,Rat.cast_ofNat]

theorem constraint_value (D : Input) (x : Fin 3 → ℝ) (t : ℝ) :
    value (constraint D) x t=value (radius D) x t*(1+value D.h x t)^2-1 := by
  simp only [constraint,value_subtract,value_multiply,value_add,value_constant,Rat.cast_one]
  ring

theorem radius_error (D : Input) (x : Fin 3 → ℝ) (t : ℝ) (q : Vec3)
    (hqnorm : enorm q=1) (hx : enorm x<2*Real.pi) {σ P δ : ℝ}
    (hσ : enorm x≤σ) (hρ : enorm (value3 D.rho x t)≤P)
    (hq : enorm (q-value3 D.reference x t)≤δ) :
    |enorm (q+Jacobian.leftAt x (value3 D.rho x t))^2-value (radius D) x t|≤
      2*δ*(1+LieRadiusQuadratic.tail σ)*P+2*LieRadiusQuadratic.tail σ*P+σ^2/12*P^2 := by
  have h := LieRadiusQuadratic.radius_error q (value3 D.reference x t)
    x (value3 D.rho x t) hx hσ hρ hq
  rw [radius_value]
  simpa only [LieRadiusQuadratic.radiusApprox,hqnorm,one_pow,mul_one,mul_assoc] using h

/-- This pointwise bound charges the quadratic radius remainder and checks
the full inverse-square field. Existence and integration remain separate. -/
theorem physical_defect (D : Input) (x : Fin 3 → ℝ) (t : ℝ) (q b : Vec3)
    (a : Coefficients) (hK : 0≤(D.K:ℝ)) (hqnorm : enorm q=1)
    (hx : enorm x<2*Real.pi) {σ P H δq δb C R : ℝ}
    (hσ : enorm x≤σ) (hρ : enorm (value3 D.rho x t)≤P) (hP : P<1)
    (hh : |value D.h x t|≤H) (hH : H<1)
    (hq : enorm (q-value3 D.reference x t)≤δq)
    (hb : enorm (b-value3 D.force x t)≤δb)
    (hc : |value (constraint D) x t|≤C)
    (hcube : value a x t=(1+value D.h x t)^3)
    (hR : enorm (value3 (D.residualWith a) x t)≤R) :
    enorm (Gravity.field3 (D.K:ℝ) q+b+
      Jacobian.leftAt x (value3 (PointingCapPolynomial.derivative
        (PointingCapPolynomial.derivative D.rho)) x t)-
      (Gravity.field3 (D.K:ℝ) (q+Jacobian.leftAt x (value3 D.rho x t))+
        rotate (rotationExp x) b))≤
      LieRadiusFullDefect.budget (D.K:ℝ) 1 σ P H δq δb
        (2*δq*(1+LieRadiusQuadratic.tail σ)*P+2*LieRadiusQuadratic.tail σ*P+σ^2/12*P^2) C R := by
  have hr : 0<enorm q := by rw [hqnorm]; norm_num
  have hp : P<enorm q := by simpa only [hqnorm] using hP
  have he := radius_error D x t q hqnorm hx hσ hρ hq
  have he' : |(enorm (q+Jacobian.leftAt x (value3 D.rho x t))^2/enorm q^2-1)-
      (value (radius D) x t-1)|≤
      2*δq*(1+LieRadiusQuadratic.tail σ)*P+2*LieRadiusQuadratic.tail σ*P+σ^2/12*P^2 := by
    simpa only [hqnorm,one_pow,div_one,sub_sub_sub_cancel_right] using he
  have hc' : |(1+(value (radius D) x t-1))*(1+value D.h x t)^2-1|≤C := by
    rw [show 1+(value (radius D) x t-1)=value (radius D) x t by ring,←constraint_value]
    exact hc
  have hr' : enorm (value3 (PointingCapPolynomial.derivative
        (PointingCapPolynomial.derivative D.rho)) x t+
      ((D.K:ℝ)/enorm q^3*value a x t) • value3 D.rho x t-x ⨯₃ value3 D.force x t+
      ((D.K:ℝ)/enorm q^3*(value a x t-1)) •
        jacobianInverseQuadratic x (value3 D.reference x t))≤R := by
    simpa only [hqnorm,one_pow,div_one,←D.residualWith_value] using hR
  have hz : |(1+value D.h x t)^3-value a x t|≤(0:ℝ) := by rw [hcube]; simp
  have h := LieRadiusFullDefect.physical_defect_of_cubic_enclosure
    (D.K:ℝ) hK x q (value3 D.reference x t) (value3 D.rho x t)
    (value3 (PointingCapPolynomial.derivative (PointingCapPolynomial.derivative D.rho)) x t)
    b (value3 D.force x t) (value D.h x t) (value (radius D) x t-1) (value a x t)
    hr hx hσ hρ hp hh hH hq hb he' hc' hz hr'
  simpa only [hqnorm,one_pow,div_one,mul_zero,zero_mul,add_zero] using h

end
end GNC.OrbitalComparison.LieRadiusQuadraticPolynomial
