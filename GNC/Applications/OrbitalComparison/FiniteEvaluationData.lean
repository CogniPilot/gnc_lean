import GNC.Analysis.ArithmeticDyadic
import GNC.Applications.OrbitalComparison.FiniteQueryGraphData
import GNC.Applications.OrbitalComparison.FiniteCartesianData

/-! Exact dyadic grid, phase enclosure and graph evaluation budgets. -/
namespace GNC.OrbitalComparison.FiniteEvaluationData
open ArithmeticProgram ArithmeticProgram.Rounding
set_option maxRecDepth 4096
set_option maxHeartbeats 0
def grid : ℕ := 2^53
def roundingError : ℚ := 1/(2*grid)
def rateCenter : ℚ := (2912930905668793/4503599627370496)
theorem grid_pos : 0<grid := by decide +kernel
theorem rate_enclosure : 0≤rateCenter-roundingError ∧
    (rateCenter-roundingError)^2≤FiniteResponseData.speed2 ∧
    FiniteResponseData.speed2≤(rateCenter+roundingError)^2 := by decide +kernel
def reference : List (Instruction 1) := [
  .constant 0,
  .constant 1,
  .input 0,
  .multiply 2 2,
  .constant (1/20922789888000),
  .constant (-1/87178291200),
  .multiply 3 4,
  .add 5 6,
  .constant (1/479001600),
  .multiply 3 7,
  .add 8 9,
  .constant (-1/3628800),
  .multiply 3 10,
  .add 11 12,
  .constant (1/40320),
  .multiply 3 13,
  .add 14 15,
  .constant (-1/720),
  .multiply 3 16,
  .add 17 18,
  .constant (1/24),
  .multiply 3 19,
  .add 20 21,
  .constant (-1/2),
  .multiply 3 22,
  .add 23 24,
  .multiply 3 25,
  .add 1 26,
  .constant (-1/1307674368000),
  .constant (1/6227020800),
  .multiply 3 28,
  .add 29 30,
  .constant (-1/39916800),
  .multiply 3 31,
  .add 32 33,
  .constant (1/362880),
  .multiply 3 34,
  .add 35 36,
  .constant (-1/5040),
  .multiply 3 37,
  .add 38 39,
  .constant (1/120),
  .multiply 3 40,
  .add 41 42,
  .constant (-1/6),
  .multiply 3 43,
  .add 44 45,
  .multiply 3 46,
  .add 1 47,
  .multiply 2 48]
def referenceOutputs : Fin 3 → ℕ := ![27, 49, 0]
theorem reference_valid : validFrom 0 reference := by decide +kernel
theorem reference_cost : arithmetic reference=32 := by decide +kernel
def phaseBudget : Budget := ⟨FiniteResponseData.horizon, 2*roundingError⟩
def angleBudget : Budget := ⟨FiniteResponseData.theta, roundingError⟩
def inputBudget : Fin 4 → Budget := ![phaseBudget, angleBudget, angleBudget, angleBudget]
def errorSum {n : ℕ} (input : Fin n → Budget) (code : List (Instruction n))
    (outputs : Fin 3 → ℕ) : ℚ :=
  ∑ i, ((budgetsFrom roundingError input [] code).getD (outputs i) zero).error
def referenceError : ℚ := errorSum (fun _ => phaseBudget) reference referenceOutputs
def geometricError : ℚ := errorSum inputBudget FiniteQueryGraphData.geometric FiniteQueryGraphData.geometricOutputs
def cartesianError : ℚ := errorSum inputBudget FiniteQueryGraphData.cartesian FiniteQueryGraphData.cartesianOutputs
def geometricNumerical : ℚ := 7000000*(referenceError+geometricError+2*FiniteResponseData.delta)
def cartesianNumerical : ℚ := 7000000*(referenceError+cartesianError+2*FiniteResponseData.delta)
/-- Numerical evaluation, phase and reference approximation: below one micrometer. -/
theorem numerical_bounds : geometricNumerical<1/1000000 ∧ cartesianNumerical<1/1000000 := by decide +kernel
/-- Same display bounds, now including the declared dyadic evaluation. -/
theorem physical_budgets :
    7000000*(FiniteResponseData.predictionBudget+FiniteResponseData.reconstructionTail*FiniteResponseData.responseRadius)+geometricNumerical<913/1000000 ∧
    7000000*FiniteCartesianData.predictionBudget .quadratic+cartesianNumerical<313/1000000 := by decide +kernel
end GNC.OrbitalComparison.FiniteEvaluationData
