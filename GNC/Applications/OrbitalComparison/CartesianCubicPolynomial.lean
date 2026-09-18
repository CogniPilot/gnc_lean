import GNC.Applications.OrbitalComparison.CartesianReducedPolynomial
import GNC.Applications.OrbitalComparison.LieRadiusQuadraticPolynomial
import GNC.Dynamics.CubicThrust

/-! Cartesian checking with a cubic force polynomial. Only the checking
source is truncated; its entire rotational tail is charged explicitly. -/
namespace GNC.OrbitalComparison.CartesianCubicPolynomial
open ParameterPolynomial PointingCapPolynomial LieSTTOutput JointErrorPolynomial Matrix

def force (D : Input) : PointingCapPolynomial.Vector :=
  LieRadiusQuadraticPolynomial.displacement {D with rho := cross phi D.force}
def residual (D : Input) : PointingCapPolynomial.Vector := fun i =>
  add (subtract (add (ParameterPolynomial.derivative (ParameterPolynomial.derivative (D.rho i)))
    (scale D.K (D.rho i))) (force D i)) (scale (3*D.K) (multiply D.h (D.reference i)))

noncomputable section

theorem force_value (D : Input) (x : Vec3) (t : ℝ) :
    value3 (force D) x t=LieRadiusQuadratic.apply x (x ⨯₃ value3 D.force x t) := by
  rw [force,LieRadiusQuadraticPolynomial.displacement_value,cross_value,phi_value]

theorem residual_value (D : Input) (x : Vec3) (t : ℝ) :
    value3 (residual D) x t=SmallOffsetDefect.retained
      (value3 (PointingCapPolynomial.derivative (PointingCapPolynomial.derivative D.rho)) x t)
      (value3 D.rho x t) (value3 D.reference x t)
      (LieRadiusQuadratic.apply x (x ⨯₃ value3 D.force x t)) (D.K:ℝ) (value D.h x t) := by
  have hf := force_value D x t
  ext i
  simp only [residual,SmallOffsetDefect.retained,value3,value_add,value_subtract,
    value_scale,value_multiply,PointingCapPolynomial.derivative,Pi.add_apply,
    Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Rat.cast_mul,Rat.cast_ofNat]
  rw [show value (force D i) x t=(LieRadiusQuadratic.apply x (x ⨯₃ value3 D.force x t)) i
    from congrFun hf i]
  ring

/-- Complete physical gravity defect given bounds for the full scalar
constraint and full gravity residual. Higher-product growth supplies these
bounds without requiring their expanded polynomial coefficients. -/
theorem physical_defect (D : Input) (x : Vec3) (t : ℝ) (q b : Vec3)
    (hK : 0≤(D.K:ℝ)) (hqnorm : enorm q=1)
    (hx : enorm x<2*Real.pi) {σ P H δq δb B C R : ℝ}
    (hσ : enorm x≤σ) (hd : enorm (value3 D.rho x t)≤P) (hP : P<1)
    (hh : |value D.h x t|≤H) (hH : H<1)
    (hq : enorm (q-value3 D.reference x t)≤δq)
    (hb : enorm (b-value3 D.force x t)≤δb) (hB : enorm (value3 D.force x t)≤B)
    (hc : |value (CartesianErrorPolynomial.constraint D) x t|≤C)
    (hR : enorm (SmallOffsetDefect.full
      (value3 (PointingCapPolynomial.derivative (PointingCapPolynomial.derivative D.rho)) x t)
      (value3 D.rho x t) (value3 D.reference x t)
      (LieRadiusQuadratic.apply x (x ⨯₃ value3 D.force x t)) (D.K:ℝ) (value D.h x t))≤R) :
    enorm (Gravity.field3 (D.K:ℝ) q+b+
      value3 (PointingCapPolynomial.derivative (PointingCapPolynomial.derivative D.rho)) x t-
      (Gravity.field3 (D.K:ℝ) (q+value3 D.rho x t)+rotate (rotationExp x) b))≤
      CartesianRadiusDefect.budget (D.K:ℝ) 1 P H δq
        (σ*δb+LieRadiusQuadratic.tail σ*σ*B) (2*δq*P) C R := by
  have hr : 0<enorm q := by rw [hqnorm]; norm_num
  have hp : P<enorm q := by simpa only [hqnorm] using hP
  have he := CartesianErrorPolynomial.radius_error D x t q hqnorm hd hq
  have he' : |(enorm (q+value3 D.rho x t)^2/enorm q^2-1)-
      (value (CartesianErrorPolynomial.radius D) x t-1)|≤2*δq*P := by
    simpa only [hqnorm,one_pow,div_one,sub_sub_sub_cancel_right] using he
  have hc' : |(1+(value (CartesianErrorPolynomial.radius D) x t-1))*(1+value D.h x t)^2-1|≤C := by
    rw [show 1+(value (CartesianErrorPolynomial.radius D) x t-1)=
      value (CartesianErrorPolynomial.radius D) x t by ring,
      ←CartesianErrorPolynomial.constraint_value]
    exact hc
  have hf := CubicThrust.error x b (value3 D.force x t) hx hσ hb hB
  have h := CartesianRadiusDefect.physical_defect_bound (D.K:ℝ) hK q
    (value3 D.reference x t) (value3 D.rho x t)
    (value3 (PointingCapPolynomial.derivative (PointingCapPolynomial.derivative D.rho)) x t)
    (rotate (rotationExp x) b-b) (LieRadiusQuadratic.apply x (x ⨯₃ value3 D.force x t))
    (value D.h x t) (value (CartesianErrorPolynomial.radius D) x t-1) hr hd hp hh hH hq hf he' hc'
    (by simpa only [hqnorm,one_pow,div_one,SmallOffsetDefect.full] using hR)
  have hid : Gravity.field3 (D.K:ℝ) q+b+
      value3 (PointingCapPolynomial.derivative (PointingCapPolynomial.derivative D.rho)) x t-
      (Gravity.field3 (D.K:ℝ) (q+value3 D.rho x t)+rotate (rotationExp x) b)=
      value3 (PointingCapPolynomial.derivative (PointingCapPolynomial.derivative D.rho)) x t-
      (Gravity.field3 (D.K:ℝ) (q+value3 D.rho x t)-Gravity.field3 (D.K:ℝ) q+
        (rotate (rotationExp x) b-b)) := by module
  rw [hid]
  simpa only [hqnorm] using h

end
end GNC.OrbitalComparison.CartesianCubicPolynomial
