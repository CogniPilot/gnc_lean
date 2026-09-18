import GNC.Analysis.SumProductCertificate
import GNC.Applications.OrbitalComparison.JointErrorPolynomial

/-! Factored scalar-radius checks. The exact Gram expression needs three
scalar products, not squared Cartesian trajectory expansions. -/
namespace GNC.OrbitalComparison.JointErrorPolynomial
open ParameterPolynomial PointingCapPolynomial LieSTTOutput Matrix

def radiusGamma : Coefficients :=
  add (subtract (multiply firstCoefficient firstCoefficient) (scale 2 secondCoefficient))
    (multiply square (multiply secondCoefficient secondCoefficient))

def Input.radiusBase (D : Input) : Coefficients :=
  add (add (constant 1) (scale 2 (LieRadiusPolynomial.dot D.reference D.rho)))
    (LieRadiusPolynomial.dot D.rho D.rho)

def Input.radiusFactors (D : Input) : Fin 3 → Coefficients :=
  ![scale 2 (LieRadiusPolynomial.dot D.reference (cross phi D.rho)),
    scale 2 (LieRadiusPolynomial.dot D.reference (cross phi (cross phi D.rho))),
    LieRadiusPolynomial.dot (cross phi D.rho) (cross phi D.rho)]

def radiusCoefficients : Fin 3 → Coefficients :=
  ![firstCoefficient,secondCoefficient,radiusGamma]

noncomputable section

theorem Input.radius_factored (D : Input) (x : Fin 3 → ℝ) (t : ℝ) :
    value D.radius x t=value D.radiusBase x t+
      ∑ i : Fin 3, value (radiusCoefficients i) x t*value (D.radiusFactors i) x t := by
  simp only [Input.radius,Input.radiusBase,radiusCoefficients,Input.radiusFactors,
    value_add,value_scale,value_constant,value_multiply,value_subtract,
    Rat.cast_one,Rat.cast_ofNat,Fin.sum_univ_succ,Fin.sum_univ_zero,Matrix.cons_val_zero,
    Matrix.cons_val_succ,add_zero,radiusGamma]
  simp only [LieRadiusPolynomial.dot,value_add,value_multiply,Input.displacement]
  ring

end
end GNC.OrbitalComparison.JointErrorPolynomial
