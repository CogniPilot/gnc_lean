import GNC.Applications.OrbitalComparison.FiniteBatchData
import GNC.Applications.OrbitalComparison.FiniteQueryGraphs

/-! Cached-phase query semantics and their transfer to physical certificates.
The finite optimizer is not trusted. These are exact-real graph costs;
the previous dyadic evaluator is not silently substituted for these graphs. -/
noncomputable section
namespace GNC.OrbitalComparison.FiniteBatchQueries
open ArithmeticProgram FiniteBatchData Matrix
open GeometricSTMPrediction (E)
set_option maxHeartbeats 0
set_option maxRecDepth 4096

def query (prepare body : List (Instruction 4)) (outputs : Fin 3 → ℕ)
    (s : ℝ) (φ : Vec3) : E := WithLp.toLp 2 (fun i =>
      (stagedValues prepare body (FiniteQueryGraphs.input s 0)
        (FiniteQueryGraphs.input s φ)).getD (outputs i) 0)

/-- The prepared prefix depends on phase alone, so it can be reused for
any number of different rotation vectors without changing the exact query. -/
theorem as_single (prepare body : List (Instruction 4)) (outputs : Fin 3 → ℕ)
    (h : usesOnly (fun i : Fin 4 => i == 0) prepare=true) (s : ℝ) (φ : Vec3) :
    query prepare body outputs s φ=FiniteQueryGraphs.query (prepare++body) outputs s φ := by
  have hv := stagedValues_eq (fun i : Fin 4 => i == 0) prepare body
    (FiniteQueryGraphs.input s 0) (FiniteQueryGraphs.input s φ) h (by
      intro i hi
      have he : i=0 := by simpa using hi
      subst i
      rfl)
  simp only [query, FiniteQueryGraphs.query, hv]

theorem geometric_correct (s : ℝ) (φ : Vec3) :
    query geometricPrepare geometricQuery geometricOutputs s φ=
      FiniteQueryGraphs.query FiniteQueryGraphData.geometric
        FiniteQueryGraphData.geometricOutputs s φ := by
  rw [as_single _ _ _ geometric_phase_only]
  ext i
  fin_cases i <;>
    norm_num (config := { maxSteps := 1000000 }) [FiniteQueryGraphs.query, FiniteQueryGraphs.input,
      geometricPrepare, geometricQuery, geometricOutputs,
      FiniteQueryGraphData.geometric, FiniteQueryGraphData.geometricOutputs,
      values, runFrom, Instruction.eval] <;> ring

theorem cartesian_correct (s : ℝ) (φ : Vec3) :
    query cartesianPrepare cartesianQuery cartesianOutputs s φ=
      FiniteQueryGraphs.query FiniteQueryGraphData.cartesian
        FiniteQueryGraphData.cartesianOutputs s φ := by
  rw [as_single _ _ _ cartesian_phase_only]
  ext i
  fin_cases i <;>
    norm_num (config := { maxSteps := 1000000 }) [FiniteQueryGraphs.query, FiniteQueryGraphs.input,
      cartesianPrepare, cartesianQuery, cartesianOutputs,
      FiniteQueryGraphData.cartesian, FiniteQueryGraphData.cartesianOutputs,
      values, runFrom, Instruction.eval] <;> ring

/-- Once-per-epoch preparation plus m uncertainty queries. -/
theorem batch_cost (m : ℕ) :
    batchArithmetic geometricPrepare geometricQuery m=22+20*m ∧
    batchArithmetic cartesianPrepare cartesianQuery m=82+28*m := by
  simp [batchArithmetic, geometric_cost.1, geometric_cost.2.1,
    cartesian_cost.1, cartesian_cost.2.1, Nat.mul_comm]

theorem batch_cost_lt (m : ℕ) :
    batchArithmetic geometricPrepare geometricQuery m<
      batchArithmetic cartesianPrepare cartesianQuery m := by
  rw [(batch_cost m).1, (batch_cost m).2]
  omega

/-- Identical physical model and accuracy target, with the actual cached
query functions. Approximation errors are inherited through proved identities. -/
theorem fixed_accuracy_queries (φ : Vec3)
    (hφ : enorm φ≤PoweredCircularLogTube.angleRadius) (x xv : ℝ → E)
    (hx : Continuous x) (hxv : Continuous xv)
    (hdx : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt x (xv t) t)
    (hdxv : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt xv
      (Gravity.field PoweredCircularLogTube.μ (x t)+
        GeometricSTMPrediction.force φ (PoweredCircularLogTube.thrust t)) t)
    (hix : x 0=PoweredCircularLogTube.reference 0)
    (hixv : xv 0=PoweredCircularLogTube.referenceVelocity 0) :
    ∀ t ∈ Set.Icc (0:ℝ) 1,
      PoweredCircularLogTube.lengthScale*‖x t-(PoweredCircularLogTube.reference t+
        query geometricPrepare geometricQuery geometricOutputs (PoweredCircularLogTube.rate*t) φ)‖<1/1000 ∧
      PoweredCircularLogTube.lengthScale*‖x t-(PoweredCircularLogTube.reference t+
        query cartesianPrepare cartesianQuery cartesianOutputs (PoweredCircularLogTube.rate*t) φ)‖<1/1000 := by
  simpa only [geometric_correct, cartesian_correct] using
    (FiniteQueryGraphs.fixed_accuracy_queries φ hφ x xv hx hxv hdx hdxv hix hixv).2.2

end GNC.OrbitalComparison.FiniteBatchQueries
