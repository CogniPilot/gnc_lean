import GNC.Applications.OrbitalComparison.JointErrorPolynomial
import GNC.Dynamics.CartesianRadiusDefect

/-! Exact executable residual and scalar-radius expressions for a Cartesian
displacement query. The reference radius is normalized to one. The same
polynomial Jacobian used to check Lie reconstruction checks the Cartesian
force; its tail is charged, rather than truncating the physical thrust.
No property of the numerical coefficient generator is assumed. -/
namespace GNC.OrbitalComparison.CartesianErrorPolynomial
open ParameterPolynomial PointingCapPolynomial LieSTTOutput Matrix
open JointErrorPolynomial

def forcePolynomial (D : Input) : PointingCapPolynomial.Vector :=
  ({ D with rho := cross phi D.force } : Input).displacement

def coupled (D : Input) : PointingCapPolynomial.Vector := fun i =>
  add (D.rho i) (D.reference i)

def baseResidual (D : Input) : PointingCapPolynomial.Vector := fun i =>
  subtract (add (ParameterPolynomial.derivative (ParameterPolynomial.derivative (D.rho i)))
    (scale D.K (D.rho i))) (forcePolynomial D i)

def residualWith (D : Input) (a : Coefficients) : PointingCapPolynomial.Vector := fun i =>
  add (baseResidual D i) (scale D.K (multiply (subtract a (constant 1)) (coupled D i)))

def radius (D : Input) : Coefficients :=
  add (add (constant 1) (scale 2 (LieRadiusPolynomial.dot D.reference D.rho)))
    (LieRadiusPolynomial.dot D.rho D.rho)

def constraint (D : Input) : Coefficients :=
  let a := add (constant 1) D.h
  subtract (multiply (radius D) (multiply a a)) (constant 1)

noncomputable section

theorem forcePolynomial_value (D : Input) (x : Fin 3 → ℝ) (t : ℝ) :
    value3 (forcePolynomial D) x t=
      JacobianPolynomial.apply x (x ⨯₃ value3 D.force x t) := by
  rw [forcePolynomial,Input.displacement_value]
  simp only [cross_value,phi_value]

theorem coupled_value (D : Input) (x : Fin 3 → ℝ) (t : ℝ) :
    value3 (coupled D) x t=value3 D.rho x t+value3 D.reference x t := by
  ext i
  exact value_add _ _ x t

theorem residualWith_value (D : Input) (a : Coefficients) (x : Fin 3 → ℝ) (t : ℝ) :
    value3 (residualWith D a) x t=
      value3 (PointingCapPolynomial.derivative (PointingCapPolynomial.derivative D.rho)) x t+
      ((D.K:ℝ)*value a x t) • value3 D.rho x t+
      ((D.K:ℝ)*(value a x t-1)) • value3 D.reference x t-
      JacobianPolynomial.apply x (x ⨯₃ value3 D.force x t) := by
  have hf := forcePolynomial_value D x t
  have hw := coupled_value D x t
  ext i
  simp only [residualWith,baseResidual,value3,value_add,value_subtract,
    value_scale,value_multiply,value_constant,Rat.cast_one,
    PointingCapPolynomial.derivative,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
  rw [show value (forcePolynomial D i) x t=
      (JacobianPolynomial.apply x (x ⨯₃ value3 D.force x t)) i from congrFun hf i,
    show value (coupled D i) x t=(value3 D.rho x t+value3 D.reference x t) i from congrFun hw i]
  simp only [Pi.add_apply,value3]
  ring

theorem radius_value (D : Input) (x : Fin 3 → ℝ) (t : ℝ) :
    value (radius D) x t=1+2*(value3 D.reference x t ⬝ᵥ value3 D.rho x t)+
      enorm (value3 D.rho x t)^2 := by
  simp only [radius,value_add,value_scale,value_constant,LieRadiusPolynomial.dot_value,
    dot_self_lengthSq,←enorm_sq,Rat.cast_one,Rat.cast_ofNat]

theorem radius_error (D : Input) (x : Fin 3 → ℝ) (t : ℝ) (q : Vec3)
    (hqnorm : enorm q=1) {P δ : ℝ}
    (hd : enorm (value3 D.rho x t)≤P)
    (hq : enorm (q-value3 D.reference x t)≤δ) :
    |enorm (q+value3 D.rho x t)^2-value (radius D) x t|≤2*δ*P := by
  have he : enorm (value3 D.rho x t-value3 D.rho x t)≤0 := by
    rw [sub_self]
    exact le_of_eq ((enorm_eq_zero_iff _).mpr rfl)
  have h := LieRadiusSpatialApproximation.radius_error q (value3 D.reference x t)
    (value3 D.rho x t) (value3 D.rho x t) hd he hq
  rw [radius_value]
  simpa only [hqnorm,one_pow,mul_zero,zero_mul,add_zero,zero_add] using h

theorem constraint_value (D : Input) (x : Fin 3 → ℝ) (t : ℝ) :
    value (constraint D) x t=value (radius D) x t*(1+value D.h x t)^2-1 := by
  simp only [constraint,value_subtract,value_multiply,value_add,value_constant,Rat.cast_one]
  ring

/-- Complete Cartesian physical defect for the executable polynomial query.
All reference, thrust, scalar-constraint and residual obligations remain
explicit. In particular, integrator tolerances are not error hypotheses. -/
theorem physical_defect (D : Input) (x : Fin 3 → ℝ) (t : ℝ) (q b : Vec3)
    (a : Coefficients) (hK : 0≤(D.K:ℝ)) (hqnorm : enorm q=1)
    (hx : enorm x<2*Real.pi) {σ P H δq δb B C R : ℝ}
    (hσ : enorm x≤σ) (hd : enorm (value3 D.rho x t)≤P) (hP : P<1)
    (hh : |value D.h x t|≤H) (hH : H<1)
    (hq : enorm (q-value3 D.reference x t)≤δq)
    (hb : enorm (b-value3 D.force x t)≤δb) (hB : enorm (value3 D.force x t)≤B)
    (hc : |value (constraint D) x t|≤C)
    (ha : value a x t=(1+value D.h x t)^3)
    (hR : enorm (value3 (residualWith D a) x t)≤R) :
    enorm (Gravity.field3 (D.K:ℝ) q+b+
      value3 (PointingCapPolynomial.derivative (PointingCapPolynomial.derivative D.rho)) x t-
      (Gravity.field3 (D.K:ℝ) (q+value3 D.rho x t)+rotate (rotationExp x) b))≤
      CartesianRadiusDefect.budget (D.K:ℝ) 1 P H δq
        (σ*δb+JacobianPolynomial.tail σ*σ*B) (2*δq*P) C R := by
  have hr : 0<enorm q := by rw [hqnorm]; norm_num
  have hp : P<enorm q := by simpa only [hqnorm] using hP
  have he := radius_error D x t q hqnorm hd hq
  have he' : |(enorm (q+value3 D.rho x t)^2/enorm q^2-1)-
      (value (radius D) x t-1)|≤2*δq*P := by
    simpa only [hqnorm,one_pow,div_one,sub_sub_sub_cancel_right] using he
  have hc' : |(1+(value (radius D) x t-1))*(1+value D.h x t)^2-1|≤C := by
    rw [show 1+(value (radius D) x t-1)=value (radius D) x t by ring,←constraint_value]
    exact hc
  have hf := CartesianRadiusDefect.thrust_error x b (value3 D.force x t) hx hσ hb hB
  rw [residualWith_value,ha] at hR
  have h := CartesianRadiusDefect.physical_defect_bound (D.K:ℝ) hK q
    (value3 D.reference x t) (value3 D.rho x t)
    (value3 (PointingCapPolynomial.derivative (PointingCapPolynomial.derivative D.rho)) x t)
    (rotate (rotationExp x) b-b) (JacobianPolynomial.apply x (x ⨯₃ value3 D.force x t))
    (value D.h x t) (value (radius D) x t-1) hr hd hp hh hH hq hf he' hc'
    (by simpa only [hqnorm,one_pow,div_one] using hR)
  have hid : Gravity.field3 (D.K:ℝ) q+b+
      value3 (PointingCapPolynomial.derivative (PointingCapPolynomial.derivative D.rho)) x t-
      (Gravity.field3 (D.K:ℝ) (q+value3 D.rho x t)+rotate (rotationExp x) b)=
      value3 (PointingCapPolynomial.derivative (PointingCapPolynomial.derivative D.rho)) x t-
      (Gravity.field3 (D.K:ℝ) (q+value3 D.rho x t)-Gravity.field3 (D.K:ℝ) q+
        (rotate (rotationExp x) b-b)) := by module
  rw [hid]
  simpa only [hqnorm] using h

end
end GNC.OrbitalComparison.CartesianErrorPolynomial
