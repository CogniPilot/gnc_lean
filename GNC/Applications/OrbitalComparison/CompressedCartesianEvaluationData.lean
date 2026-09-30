import GNC.Applications.OrbitalComparison.CompressedCartesianData
import GNC.Applications.OrbitalComparison.FiniteEvaluationData

/-! Propagate each compressed graph's own dyadic error, including phase,
input, coefficient and reference errors. This does not reuse the numerical
budget of the higher-degree witness. -/
namespace GNC.OrbitalComparison.CompressedCartesianEvaluationData
open ArithmeticProgram CompressedCartesianData FiniteEvaluationData
set_option maxHeartbeats 0
set_option maxRecDepth 4096

def numerical (code : List (Instruction 4)) (outputs : Fin 3 → ℕ) : ℚ :=
  7000000*(referenceError+errorSum inputBudget code outputs+2*FiniteResponseData.delta)

theorem budgets :
    7000000*CompressedCartesian.budget+numerical (singlePrepare++singleQuery) singleOutputs<749/1000000 ∧
    7000000*CompressedCartesian.budget+numerical (batchPrepare++batchQuery) batchOutputs<749/1000000 := by
  decide +kernel

end GNC.OrbitalComparison.CompressedCartesianEvaluationData
