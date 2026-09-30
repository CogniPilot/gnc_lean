import GNC.Applications.OrbitalComparison.CompressedCartesianData
import GNC.Applications.OrbitalComparison.FiniteBatchQueries

/-! Exact semantics of the stronger whole-interval Cartesian comparator.
The search is untrusted; the emitted graphs are checked against the actual
compressed polynomial and their operation counts are kernel evaluated.
-/
noncomputable section
namespace GNC.OrbitalComparison.CompressedCartesianGraphs
open ArithmeticProgram CompressedCartesianData Matrix
open PoweredCircularLogTube (rate)
set_option maxRecDepth 4096
set_option maxHeartbeats 0

theorem single_correct (t : ℝ) (φ : Vec3) :
    FiniteQueryGraphs.query (singlePrepare++singleQuery) singleOutputs (rate*t) φ=
      CompressedCartesian.position φ t := by
  rw [CompressedCartesian.position, ←coefficients_agree]
  ext i
  fin_cases i <;>
    norm_num (config := { maxSteps := 1000000 }) [FiniteQueryGraphs.query,
      FiniteQueryGraphs.input, singlePrepare, singleQuery, singleOutputs,
      values, runFrom, Instruction.eval, coefficients, LinearResponsePolynomial.response,
      FiniteCartesianResponse.features, FiniteCartesianResponse.matrix,
      PolynomialOrder.value, Planning.PolynomialKernel.evaluate, FiniteCircularResponse.basis,
      RotationFeatureBounds.quadraticMatrix, skew, mul_apply, Fin.sum_univ_succ,
      Matrix.vecHead, Matrix.vecTail, Pi.single_apply, Matrix.cons_val_zero',
      Matrix.cons_val_succ', Matrix.cons_val_three, Matrix.cons_val_two, Fin.ext_iff] <;> ring

theorem batch_as_single (s : ℝ) (φ : Vec3) :
    FiniteQueryGraphs.query (batchPrepare++batchQuery) batchOutputs s φ=
      FiniteQueryGraphs.query (singlePrepare++singleQuery) singleOutputs s φ := by
  ext i
  fin_cases i <;>
    norm_num (config := { maxSteps := 1000000 }) [FiniteQueryGraphs.query, FiniteQueryGraphs.input,
      batchPrepare, batchQuery, batchOutputs, singlePrepare, singleQuery, singleOutputs,
      values, runFrom, Instruction.eval] <;> ring

theorem batch_correct (t : ℝ) (φ : Vec3) :
    FiniteBatchQueries.query batchPrepare batchQuery batchOutputs (rate*t) φ=
      CompressedCartesian.position φ t := by
  rw [FiniteBatchQueries.as_single _ _ _ batch_phase_only, batch_as_single, single_correct]

/-- Preparation and feature/reconstruction arithmetic are included, shared
reference/phase and rounding are not. FMA is charged as two operations. -/
theorem costs (N : ℕ) :
    arithmetic (singlePrepare++singleQuery)=73 ∧
    batchArithmetic batchPrepare batchQuery N=58+28*N ∧
    batchArithmetic FiniteBatchData.geometricPrepare FiniteBatchData.geometricQuery N<
      batchArithmetic batchPrepare batchQuery N := by
  have hb : batchArithmetic batchPrepare batchQuery N=58+28*N := by
    simp [batchArithmetic, batch_cost.1, batch_cost.2.1, Nat.mul_comm]
  refine ⟨by decide +kernel,hb,?_⟩
  rw [(FiniteBatchQueries.batch_cost N).1, hb]
  omega

end GNC.OrbitalComparison.CompressedCartesianGraphs
