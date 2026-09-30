import GNC.Applications.OrbitalComparison.FiniteEvaluationData
import GNC.Applications.OrbitalComparison.FiniteBatchData

/-! Exact budgets for the new staged graphs. The sums account for the
prepared prefix once along each output dependency, including coefficient,
phase and input error. No allowance grows with the number of queries. -/
namespace GNC.OrbitalComparison.FiniteBatchEvaluationData
open ArithmeticProgram FiniteBatchData FiniteEvaluationData
set_option maxRecDepth 4096
set_option maxHeartbeats 0

def geometricNumerical : ℚ := 7000000*(referenceError+
  errorSum inputBudget (geometricPrepare++geometricQuery) geometricOutputs+2*FiniteResponseData.delta)
def cartesianNumerical : ℚ := 7000000*(referenceError+
  errorSum inputBudget (cartesianPrepare++cartesianQuery) cartesianOutputs+2*FiniteResponseData.delta)

theorem numerical_bounds : geometricNumerical<1/1000000 ∧ cartesianNumerical<1/1000000 := by
  decide +kernel

theorem physical_budgets :
    7000000*(FiniteResponseData.predictionBudget+FiniteResponseData.reconstructionTail*FiniteResponseData.responseRadius)+
      geometricNumerical<913/1000000 ∧
    7000000*FiniteCartesianData.predictionBudget .quadratic+cartesianNumerical<313/1000000 := by
  decide +kernel

end GNC.OrbitalComparison.FiniteBatchEvaluationData
