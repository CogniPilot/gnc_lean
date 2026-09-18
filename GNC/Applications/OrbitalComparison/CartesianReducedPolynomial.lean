import GNC.Applications.OrbitalComparison.CartesianErrorPolynomial
import GNC.Dynamics.SmallOffsetDefect

/-! Lower-degree checking expressions. The cubic gravity and nonlinear
radius-constraint products are charged by `SmallOffsetDefect`; they are
not assumed to vanish and the delivered predictor is unchanged. -/
namespace GNC.OrbitalComparison.CartesianReducedPolynomial
open ParameterPolynomial PointingCapPolynomial LieSTTOutput JointErrorPolynomial Matrix

def residual (D : Input) : PointingCapPolynomial.Vector := fun i =>
  add (CartesianErrorPolynomial.baseResidual D i)
    (scale (3*D.K) (multiply D.h (D.reference i)))

def constraint (D : Input) : Coefficients :=
  subtract (add (CartesianErrorPolynomial.radius D) (scale 2 D.h)) (constant 1)

noncomputable section

theorem residual_value (D : Input) (x : Fin 3 → ℝ) (t : ℝ) :
    value3 (residual D) x t=SmallOffsetDefect.retained
      (value3 (PointingCapPolynomial.derivative (PointingCapPolynomial.derivative D.rho)) x t)
      (value3 D.rho x t) (value3 D.reference x t)
      (JacobianPolynomial.apply x (x ⨯₃ value3 D.force x t)) (D.K:ℝ) (value D.h x t) := by
  have hf := CartesianErrorPolynomial.forcePolynomial_value D x t
  ext i
  simp only [residual,CartesianErrorPolynomial.baseResidual,SmallOffsetDefect.retained,
    value3,value_add,value_subtract,value_scale,value_multiply,
    PointingCapPolynomial.derivative,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,
    Rat.cast_mul,Rat.cast_ofNat]
  rw [show value (CartesianErrorPolynomial.forcePolynomial D i) x t=
    (JacobianPolynomial.apply x (x ⨯₃ value3 D.force x t)) i from congrFun hf i]
  ring

theorem constraint_value (D : Input) (x : Fin 3 → ℝ) (t : ℝ) :
    value (constraint D) x t=value (CartesianErrorPolynomial.radius D) x t+2*value D.h x t-1 := by
  simp only [constraint,value_subtract,value_add,value_scale,value_constant,
    Rat.cast_one,Rat.cast_ofNat]

end
end GNC.OrbitalComparison.CartesianReducedPolynomial
