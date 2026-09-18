import GNC.Analysis.CoefficientNormProfile
import GNC.Dynamics.LieRadiusApproximation
import GNC.Applications.OrbitalComparison.LieRadiusFrame

/-! Executable scalar and Lie-residual expressions for direct certification.
The input is a Lie translation and an auxiliary inverse-radius polynomial,
with the known reference phase supplied as polynomial sine/cosine curves.
No Cartesian trajectory polynomial is an input or an intermediate field.
Range checks here are a stage of certification; the physical defect and
first-exit composition must also be discharged.
-/
namespace GNC.OrbitalComparison.LieRadiusPolynomial
open ParameterPolynomial PointingCapPolynomial

structure Input where
  μ : ℚ
  r : ℚ
  w0 : ℚ
  slope : ℚ
  cosine : List ℚ
  sine : List ℚ
  z : PointingCapPolynomial.Vector
  h : Coefficients

def dot (a b : PointingCapPolynomial.Vector) : Coefficients :=
  add (add (multiply (a 0) (b 0)) (multiply (a 1) (b 1))) (multiply (a 2) (b 2))
def Input.K (D : Input) : ℚ := D.μ/D.r^3
def Input.axis (D : Input) : PointingCapPolynomial.Vector :=
  ![scale (-3/5) (VaryingRatePolynomial.time D.sine),
    scale (-3/5) (VaryingRatePolynomial.time D.cosine),constant (4/5)]
def Input.rho (D : Input) : PointingCapPolynomial.Vector := fun i => multiply u (D.z i)
def Input.rate (D : Input) : Coefficients := VaryingRatePolynomial.time [D.w0,D.slope]
def Input.covariant (D : Input) (p : PointingCapPolynomial.Vector) : PointingCapPolynomial.Vector :=
  ![subtract (ParameterPolynomial.derivative (p 0)) (multiply D.rate (p 1)),
    add (ParameterPolynomial.derivative (p 1)) (multiply D.rate (p 0)),
    ParameterPolynomial.derivative (p 2)]
def Input.force (D : Input) : PointingCapPolynomial.Vector :=
  ![scale D.r (subtract (constant D.K) (multiply D.rate D.rate)),constant (D.r*D.slope),[]]
def unitRadial : PointingCapPolynomial.Vector := ![constant 1,[],[]]
def Input.inverse (D : Input) : PointingCapPolynomial.Vector := fun i =>
  add (subtract (unitRadial i) (scale (1/2) (multiply u (LieSTTOutput.cross D.axis unitRadial i))))
    (scale (1/12) (multiply (multiply u u)
      (LieSTTOutput.cross D.axis (LieSTTOutput.cross D.axis unitRadial) i)))
def Input.residual (D : Input) : PointingCapPolynomial.Vector := fun i =>
  subtract (add (add (add (D.covariant (D.covariant D.rho) i) (scale D.K (D.rho i)))
    (scale (3*D.K) (multiply D.h (D.rho i))))
    (scale (3*D.K*D.r) (multiply D.h (D.inverse i))))
    (multiply u (LieSTTOutput.cross D.axis D.force i))
def Input.projection (D : Input) : Coefficients :=
  add (add (multiply u (D.z 0)) (multiply (VaryingRatePolynomial.cosineLoss .octic)
    (LieSTTOutput.cross D.axis D.z 0)))
    (multiply (subtract u (VaryingRatePolynomial.sine .octic))
      (LieSTTOutput.cross D.axis (LieSTTOutput.cross D.axis D.z) 0))
def Input.gram (D : Input) : Coefficients :=
  let axial := multiply (dot D.axis D.z) (dot D.axis D.z)
  add (multiply (multiply u u) axial) (scale 2
    (multiply (VaryingRatePolynomial.cosineLoss .octic) (subtract (dot D.z D.z) axial)))
def Input.radiusDeviation (D : Input) : Coefficients :=
  add (scale (2/D.r) D.projection) (scale (1/D.r^2) D.gram)
def Input.constraintLinear (D : Input) : Coefficients :=
  add D.radiusDeviation (scale 2 D.h)

noncomputable section
open Matrix LieSTTOutput

theorem dot_value (a b : PointingCapPolynomial.Vector) (x : Fin 3 → ℝ) (t : ℝ) :
    value (dot a b) x t=value3 a x t ⬝ᵥ value3 b x t := by
  simp [dot,value_add,value_multiply,value3,dotProduct,Fin.sum_univ_succ]
  ring

theorem rho_value (D : Input) (θ t : ℝ) :
    value3 D.rho ![θ,0,0] t=θ • value3 D.z ![θ,0,0] t := by
  ext i
  simp [Input.rho,value3,value_multiply,value_u]

theorem projection_value (D : Input) (θ t : ℝ) :
    value D.projection ![θ,0,0] t=
      (polynomialTranslation (value3 D.axis ![θ,0,0] t) (value3 D.z ![θ,0,0] t) θ) 0 := by
  have hx : ![θ,0,0]=VaryingRatePolynomial.parameter .octic θ := rfl
  rw [hx]
  simp only [Input.projection,value_add,value_multiply,value_subtract,value_u,
    VaryingRatePolynomial.cosine_octic,VaryingRatePolynomial.sine_octic,
    polynomialTranslation,Pi.add_apply,Pi.smul_apply,smul_eq_mul,←cross_value]
  rfl

theorem gram_value (D : Input) (θ t : ℝ) :
    value D.gram ![θ,0,0] t=LieRadiusApproximation.gram
      (value3 D.axis ![θ,0,0] t) (value3 D.z ![θ,0,0] t) θ (OcticPointing.cosineLoss θ) := by
  have hx : ![θ,0,0]=VaryingRatePolynomial.parameter .octic θ := rfl
  rw [hx]
  simp only [Input.gram,value_add,value_multiply,value_scale,value_subtract,dot_value,value_u,
    VaryingRatePolynomial.cosine_octic,LieRadiusApproximation.gram,←dot_self_lengthSq]
  simp only [VaryingRatePolynomial.parameter,Matrix.cons_val_zero]
  norm_num
  ring

end
end GNC.OrbitalComparison.LieRadiusPolynomial
