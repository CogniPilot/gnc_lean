import GNC.Analysis.ParameterPolynomialCertificate
import GNC.Applications.OrbitalComparison.PointingCapPolynomial

/-! Finite rational support certificates on the physical pointing cap.
Weighted squares, the exact sphere identity, and a certified cap-depth
inequality suffice. No parameter sampling or inferred global optimizer is
used in the soundness theorem. The polynomial degree is unrestricted. -/
namespace GNC.OrbitalComparison.PointingCapSupport
open ParameterPolynomial PointingCapPolynomial PointingCapBurn

structure Certificate where
  time : ℚ
  upper : ℚ
  depth : ℚ
  depthMultiplier : ℚ
  sphereMultiplier : Coefficients
  squares : List (ℚ × Coefficients)
  diskSquares : List (ℚ × Coefficients) := []

def Certificate.Valid (C : Certificate) (p : Coefficients) (sigma : ℚ) : Prop :=
  C.depth < 1 ∧ sigma^2 ≤ 2*C.depth-C.depth^2 ∧
  0 ≤ C.depthMultiplier ∧ NonnegativeWeights C.squares ∧
  NonnegativeWeights C.diskSquares ∧
  zero (subtract (subtract (constant C.upper) (atTime p C.time))
    (add (weightedSquares C.squares)
      (add (scale C.depthMultiplier (subtract (constant C.depth) c))
        (add (multiply C.sphereMultiplier constraint)
          (multiply (weightedSquares C.diskSquares)
            (subtract (constant (sigma^2)) transverse))))))

instance (C : Certificate) (p : Coefficients) (sigma : ℚ) :
    Decidable (C.Valid p sigma) := by unfold Certificate.Valid; infer_instance

theorem depth_bound {sigma d : ℝ} {x : Fin 3 → ℝ}
    (hx : Admissible sigma x) (hd : d < 1) (hs : sigma^2 ≤ 2*d-d^2) :
    x 2 ≤ d := by
  by_contra hn
  have hpos : 0 < (x 2-d)*(2-x 2-d) :=
    mul_pos (sub_pos.mpr (lt_of_not_ge hn)) (by linarith [hx.2.1])
  nlinarith [hx.2.2.1,hx.2.2.2]

theorem Certificate.bounds (C : Certificate) (p : Coefficients) (sigma : ℚ)
    (h : C.Valid p sigma) {x : Fin 3 → ℝ} (hx : Admissible (sigma:ℝ) x) :
    value p x (C.time:ℝ) ≤ (C.upper:ℝ) := by
  obtain ⟨hd,hs,hm,hw,hdw,he⟩ := h
  have hd' : (C.depth:ℝ) < 1 := by exact_mod_cast hd
  have hs' : (sigma:ℝ)^2 ≤ 2*(C.depth:ℝ)-(C.depth:ℝ)^2 := by exact_mod_cast hs
  have hm' : (0:ℝ) ≤ C.depthMultiplier := by exact_mod_cast hm
  have hc := depth_bound hx hd' hs'
  have hi := identity _ _ he x 0
  simp only [value_subtract,value_constant,value_atTime,value_add,value_scale,
    value_multiply,value_c,value_constraint hx,value_transverse,mul_zero,
    zero_add,Rat.cast_pow] at hi
  have hn := weightedSquares_nonnegative C.squares hw x 0
  have hp := mul_nonneg hm' (sub_nonneg.mpr hc)
  have hdp := mul_nonneg (weightedSquares_nonnegative C.diskSquares hdw x 0)
    (sub_nonneg.mpr hx.2.2.2)
  linarith

end GNC.OrbitalComparison.PointingCapSupport
