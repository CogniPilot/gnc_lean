import GNC.Analysis.ArithmeticExecutionCost
import GNC.Applications.OrbitalComparison.CompressedCartesianEvaluation

/-! Whole-output evaluation costs for the specified dyadic reference
implementation. Phase/reference preparation is shared per epoch; each query
quantizes three angle inputs and performs three SI additions/multiplications.
Offline certificate construction, memory and integer bit cost remain excluded.
The counts describe existing programs, not globally optimized implementations.
-/
namespace GNC.OrbitalComparison.FinitePredictionWork
open ArithmeticProgram ArithmeticProgram.Rounding
open FiniteEvaluationData

/-- One phase multiplication and quantization, followed by reference evaluation. -/
def common : Work := (⟨1,1,0⟩ : Work).plus (work reference)

/-- Three input quantizations, three reference additions and three SI scalings. -/
def output : Work := ⟨6,3,0⟩

def batch (prep body : List (Instruction 4)) (n : ℕ) : Work :=
  (common.plus (work prep)).plus ((output.plus (work body)).repeat n)

theorem common_work : common=⟨33,50,0⟩ := by decide +kernel

theorem geometric_work (n : ℕ) :
    batch FiniteBatchData.geometricPrepare FiniteBatchData.geometricQuery n=
      ⟨55+26*n,83+23*n,1+3*n⟩ := by
  have hp : work FiniteBatchData.geometricPrepare=⟨22,33,1⟩ := by decide +kernel
  have hq : work FiniteBatchData.geometricQuery=⟨20,20,3⟩ := by decide +kernel
  simp [batch, common_work, hp, hq, output, Work.plus, Work.repeat, Nat.mul_comm]

theorem cartesian_work (n : ℕ) :
    batch CompressedCartesianData.batchPrepare CompressedCartesianData.batchQuery n=
      ⟨91+34*n,143+31*n,0⟩ := by
  have hp : work CompressedCartesianData.batchPrepare=⟨58,93,0⟩ := by decide +kernel
  have hq : work CompressedCartesianData.batchQuery=⟨28,28,0⟩ := by decide +kernel
  simp [batch, common_work, hp, hq, output, Work.plus, Work.repeat, Nat.mul_comm]

theorem original_cartesian_work (n : ℕ) :
    (batch FiniteBatchData.cartesianPrepare FiniteBatchData.cartesianQuery n).binary=
      115+34*n := by
  have hp : (work FiniteBatchData.cartesianPrepare).binary=82 := by decide +kernel
  have hq : (work FiniteBatchData.cartesianQuery).binary=28 := by decide +kernel
  simp [batch, common_work, output, Work.plus, Work.repeat, hp, hq, Nat.mul_comm]

theorem single_binary :
    (common.plus (output.plus (work FiniteQueryGraphData.geometric))).binary=80 ∧
    (common.plus (output.plus (work
      (CompressedCartesianData.singlePrepare++CompressedCartesianData.singleQuery)))).binary=112 := by
  decide +kernel

/-- Unknown offline construction costs are not silently declared zero.
This exact break-even test states when the online saving pays for them. -/
theorem amortized_criterion (n geometricOffline cartesianOffline : ℕ) :
    geometricOffline+(batch FiniteBatchData.geometricPrepare FiniteBatchData.geometricQuery n).binary <
      cartesianOffline+(batch CompressedCartesianData.batchPrepare
        CompressedCartesianData.batchQuery n).binary ↔
    geometricOffline<cartesianOffline+36+8*n := by
  rw [geometric_work, cartesian_work]
  simp only
  omega

end GNC.OrbitalComparison.FinitePredictionWork
