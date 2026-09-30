import GNC.Applications.OrbitalComparison.FiniteQueryGraphData
import GNC.Applications.OrbitalComparison.FiniteCartesianCertificate

/-! Correctness of the counted graphs as real functions, and transfer of
both physical certificates to those graphs. The cost model charges each
emitted addition or multiplication once, with negations counted separately.
No floating rounding, optimizer optimality, or CPU-cycle claim is made. -/
noncomputable section
namespace GNC.OrbitalComparison.FiniteQueryGraphs
open ArithmeticProgram FiniteQueryGraphData
open GeometricSTMPrediction (E)
open Matrix
set_option maxHeartbeats 0
set_option maxRecDepth 4096

def input (s : ℝ) (φ : Vec3) : Fin 4 → ℝ := ![s, φ 0, φ 1, φ 2]
def query (code : List (Instruction 4)) (outputs : Fin 3 → ℕ) (s : ℝ) (φ : Vec3) : E :=
  WithLp.toLp 2 (fun i => (values code (input s φ)).getD (outputs i) 0)

/-- The entire emitted graph equals the certified finite geometric
position deviation, for every real swept angle and rotation vector. -/
theorem geometric_correct (t : ℝ) (φ : Vec3) :
    query geometric geometricOutputs (PoweredCircularLogTube.rate*t) φ=
      WithLp.toLp 2 (JacobianAffine.apply φ (FiniteCircularResponse.position φ t).ofLp) := by
  ext i
  fin_cases i <;>
    norm_num [query, geometric, geometricOutputs, values, runFrom, Instruction.eval, input,
      FiniteCircularResponse.position, LinearResponsePolynomial.response, FiniteResponseData.coefficients,
      PolynomialOrder.value, Planning.PolynomialKernel.evaluate, FiniteCircularResponse.basis,
      JacobianAffine.apply, cross_apply, Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail, Pi.single_apply, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_three, Matrix.cons_val_two, Fin.ext_iff] <;> ring

/-- The matched Cartesian graph includes quadratic feature formation. -/
theorem cartesian_correct (t : ℝ) (φ : Vec3) :
    query cartesian cartesianOutputs (PoweredCircularLogTube.rate*t) φ=
      FiniteCartesianResponse.position .quadratic φ t := by
  ext i
  fin_cases i <;>
    norm_num [query, cartesian, cartesianOutputs, values, runFrom, Instruction.eval, input,
      FiniteCartesianResponse.position, FiniteCartesianResponse.features, FiniteCartesianResponse.matrix,
      LinearResponsePolynomial.response, FiniteCartesianData.coefficients,
      PolynomialOrder.value, Planning.PolynomialKernel.evaluate, FiniteCircularResponse.basis,
      RotationFeatureBounds.quadraticMatrix, skew, mul_apply, Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail, Pi.single_apply, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_three, Matrix.cons_val_two, Fin.ext_iff] <;> ring

/-- This compares the two specific verified graphs, not an optimality lower
bound on all Cartesian algorithms. Input phase and reference are shared. -/
theorem arithmetic_comparison : arithmetic geometric=41 ∧ arithmetic cartesian=85 ∧
    arithmetic geometric<arithmetic cartesian := by
  decide +kernel


/-- Outward rounding for display in millimeters. These are upper bounds
on derived exact budgets, not allowances inserted into the dynamics. -/
theorem displayed_budgets :
    7000000*(FiniteResponseData.predictionBudget+
      FiniteResponseData.reconstructionTail*FiniteResponseData.responseRadius)<913/1000000 ∧
    7000000*FiniteCartesianData.predictionBudget .quadratic<313/1000000 ∧
    7000000*FiniteCartesianData.predictionBudget .components<284/1000000 := by
  decide +kernel

/-- Same actual trajectory and uncertainty input: both counted real-arithmetic
queries meet the fixed target, with exact scoped costs 41 and 85. -/
theorem fixed_accuracy_queries (φ : Vec3)
    (hφ : enorm φ≤PoweredCircularLogTube.angleRadius) (x xv : ℝ → E)
    (hx : Continuous x) (hxv : Continuous xv)
    (hdx : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt x (xv t) t)
    (hdxv : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt xv
      (Gravity.field PoweredCircularLogTube.μ (x t)+
        GeometricSTMPrediction.force φ (PoweredCircularLogTube.thrust t)) t)
    (hix : x 0=PoweredCircularLogTube.reference 0)
    (hixv : xv 0=PoweredCircularLogTube.referenceVelocity 0) :
    arithmetic geometric=41 ∧ arithmetic cartesian=85 ∧
    ∀ t ∈ Set.Icc (0:ℝ) 1,
      PoweredCircularLogTube.lengthScale*‖x t-(PoweredCircularLogTube.reference t+
        query geometric geometricOutputs (PoweredCircularLogTube.rate*t) φ)‖<1/1000 ∧
      PoweredCircularLogTube.lengthScale*‖x t-(PoweredCircularLogTube.reference t+
        query cartesian cartesianOutputs (PoweredCircularLogTube.rate*t) φ)‖<1/1000 := by
  refine ⟨geometric_cost.1, cartesian_cost.1, ?_⟩
  intro t ht
  constructor
  · simpa only [geometric_correct, FiniteCircularCertificate.prediction] using
      FiniteCircularCertificate.submillimeter φ hφ x xv hx hxv hdx hdxv hix hixv t ht
  · simpa only [cartesian_correct, FiniteCartesianCertificate.prediction] using
      FiniteCartesianCertificate.submillimeter .quadratic φ hφ x xv hx hxv hdx hdxv hix hixv t ht

end GNC.OrbitalComparison.FiniteQueryGraphs
