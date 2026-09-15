import GNC.Analysis.DirectionalTensor
import GNC.Applications.OrbitalComparison.SpatialPolynomialObstruction

/-! The physical polynomial barrier also covers arbitrary directional
rank-one expansions on the benchmark's linear one-angle uncertainty input.
The number of terms, ranks represented by their sums, directions and real
coefficients are unrestricted. Only the maximum degree is bounded.

This is an approximation-class statement, not a reproduction of the
direction-selection algorithm, a FLOP bound, or an obstruction for nonlinear
input charts and piecewise predictors.
-/
noncomputable section
namespace GNC.OrbitalComparison.DirectionalObstruction
open GNC.DirectionalTensor SpatialPolynomialObstruction Set

theorem physical_comparison {I : Type*} [Fintype I] {n : ℕ}
    (degree : Fin n → ℕ) (a : Fin n → EuclideanSpace ℝ (Fin 3))
    (v : Fin n → I → ℝ) (direction : I → ℝ) (hd : ∀ k, degree k≤6) :
    (∀ θ : ℝ, |θ| ≤ 7/20 → ∀ t ∈ Icc (0:ℝ) 1,
      ‖physicalDeviation θ t-retainedDeviation θ t‖ ≤ (989067/1000000000000:ℝ)) ∧
    ∃ θ : ℝ, |θ| ≤ 7/20 ∧ (388/100000000:ℝ) <
      ‖physicalDeviation θ 1-ridgeSeries degree a v (fun i => θ*direction i)‖ := by
  have h := SpatialPolynomialObstruction.physical_comparison
    (linePolynomial degree a v direction)
    (linePolynomial_degree degree a v direction hd 1)
  simpa only [linePolynomial_eval] using h

end GNC.OrbitalComparison.DirectionalObstruction
