import GNC.Applications.OrbitalComparison.PrunedFiniteData
import GNC.Applications.OrbitalComparison.FiniteBatchQueries

/-! Independent exact-real identities for both mixed-degree query programs.
The optimizer and its polynomial expansion checks are not trusted. -/
noncomputable section
namespace GNC.OrbitalComparison.PrunedFiniteGraphs
open ArithmeticProgram PrunedFiniteData Matrix
set_option maxRecDepth 4096
set_option maxHeartbeats 0

theorem geometric_correct (cached : Bool) (t : ℝ) (φ : Vec3) :
    FiniteQueryGraphs.query (geometricPrepare cached++geometricQuery cached)
      (geometricOutputs cached) (PoweredCircularLogTube.rate*t) φ=
      PrunedFinitePrediction.geometricPosition φ t := by
  unfold PrunedFinitePrediction.geometricPosition
  rw [←geometric_coefficients_agree]
  cases cached <;> ext i <;> fin_cases i <;>
    norm_num (config := { maxSteps := 1000000 }) [FiniteQueryGraphs.query, FiniteQueryGraphs.input,
      geometricPrepare, geometricQuery, geometricOutputs, geometricSinglePrepare,
      geometricSingleQuery, geometricSingleOutputs, geometricBatchPrepare,
      geometricBatchQuery, geometricBatchOutputs, geometricCoefficients,
      values, runFrom, Instruction.eval, LinearResponsePolynomial.response,
      PolynomialOrder.value, Planning.PolynomialKernel.evaluate, FiniteCircularResponse.basis,
      JacobianAffine.apply, cross_apply, Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail,
      Pi.single_apply, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_three,
      Matrix.cons_val_two, Fin.ext_iff] <;> ring

theorem cartesian_correct (cached : Bool) (t : ℝ) (φ : Vec3) :
    FiniteQueryGraphs.query (cartesianPrepare cached++cartesianQuery cached)
      (cartesianOutputs cached) (PoweredCircularLogTube.rate*t) φ=
      PrunedFinitePrediction.cartesianPosition φ t := by
  unfold PrunedFinitePrediction.cartesianPosition
  rw [←cartesian_coefficients_agree]
  cases cached <;> ext i <;> fin_cases i <;>
    norm_num (config := { maxSteps := 1000000 }) [FiniteQueryGraphs.query, FiniteQueryGraphs.input,
      cartesianPrepare, cartesianQuery, cartesianOutputs, cartesianSinglePrepare,
      cartesianSingleQuery, cartesianSingleOutputs, cartesianBatchPrepare,
      cartesianBatchQuery, cartesianBatchOutputs, cartesianCoefficients,
      values, runFrom, Instruction.eval, LinearResponsePolynomial.response,
      PolynomialOrder.value, Planning.PolynomialKernel.evaluate, FiniteCircularResponse.basis,
      FiniteCartesianResponse.features, FiniteCartesianResponse.matrix,
      RotationFeatureBounds.quadraticMatrix, skew, mul_apply, Fin.sum_univ_succ,
      Matrix.vecHead, Matrix.vecTail, Pi.single_apply, Matrix.cons_val_zero',
      Matrix.cons_val_succ', Matrix.cons_val_three, Matrix.cons_val_two, Fin.ext_iff] <;> ring

end GNC.OrbitalComparison.PrunedFiniteGraphs
