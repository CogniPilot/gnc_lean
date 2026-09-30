import GNC.Analysis.ArithmeticDyadicStages
import GNC.Applications.OrbitalComparison.FiniteBatchEvaluationData
import GNC.Applications.OrbitalComparison.FiniteBatchQueries
import GNC.Applications.OrbitalComparison.FiniteEvaluation

/-! Executable cached dyadic predictions with complete physical bounds.
The preparation is immutable and no query consumes a previous query output.
All admissible rational queries share the same error budget, independent of
batch size. This specifies unbounded-integer dyadics, not IEEE or CPU behavior. -/
namespace GNC.OrbitalComparison.FiniteBatchEvaluation
open ArithmeticProgram ArithmeticProgram.Rounding FiniteBatchData FiniteEvaluationData
open FiniteEvaluation (embed angle)
open GeometricSTMPrediction (E)
open PoweredCircularLogTube (rate angleRadius lengthScale)
open Matrix
set_option maxRecDepth 4096
set_option maxHeartbeats 0

structure Prepared where
  phase : ℚ
  reference : Fin 3 → ℚ
  values : List ℚ

def phaseInputs (s : ℚ) (φ : Fin 3 → ℚ) : Fin 4 → ℚ :=
  ![s, dyadicRat grid (φ 0), dyadicRat grid (φ 1), dyadicRat grid (φ 2)]

def prepare (code : List (Instruction 4)) (t : ℚ) : Prepared :=
  let s := FiniteEvaluation.phase t
  ⟨s, FiniteEvaluation.rationalQuery reference referenceOutputs (fun _ => s),
    roundedRatFrom grid (phaseInputs s 0) [] code⟩

def physicalPrediction (body : List (Instruction 4)) (outputs : Fin 3 → ℕ)
    (cache : Prepared) (φ : Fin 3 → ℚ) : Fin 3 → ℚ :=
  let v := roundedRatFrom grid (phaseInputs cache.phase φ) cache.values body
  fun i => 7000000*(cache.reference i+v.getD (outputs i) 0)

/-- Actual immutable preparation reuse agrees with the complete rounded
program for every query; no ideal-arithmetic equivalence is substituted. -/
theorem physicalPrediction_eq (prepCode body : List (Instruction 4)) (outputs : Fin 3 → ℕ)
    (h : usesOnly (fun i : Fin 4 => i == 0) prepCode=true) (t : ℚ) (φ : Fin 3 → ℚ) :
    physicalPrediction body outputs (prepare prepCode t) φ=
      FiniteEvaluation.physicalPrediction (prepCode++body) outputs t φ := by
  have hv := stagedRat_eq grid (fun i : Fin 4 => i == 0) prepCode body
    (FiniteEvaluation.inputs t 0) (FiniteEvaluation.inputs t φ) h (by
      intro i hi
      have he : i=0 := by simpa using hi
      subst i
      rfl)
  ext i
  simpa only [physicalPrediction, prepare, phaseInputs, FiniteEvaluation.physicalPrediction,
    FiniteEvaluation.prediction, FiniteEvaluation.rationalQuery, FiniteEvaluation.inputs,
    stagedRat] using congrArg (fun v : List ℚ =>
      7000000*(FiniteEvaluation.rationalQuery reference referenceOutputs
        (fun _ => FiniteEvaluation.phase t) i+v.getD (outputs i) 0)) hv

/-- Every admissible rational query after preparation has the same complete
SI bound, irrespective of how many other attitudes are queried. -/
theorem certificates (φ : Fin 3 → ℚ) (hφ : enorm (angle φ)≤angleRadius)
    (x xv : ℝ → E) (hx : Continuous x) (hxv : Continuous xv)
    (hdx : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt x (xv t) t)
    (hdxv : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt xv
      (Gravity.field PoweredCircularLogTube.μ (x t)+
        GeometricSTMPrediction.force (angle φ) (PoweredCircularLogTube.thrust t)) t)
    (hix : x 0=PoweredCircularLogTube.reference 0)
    (hixv : xv 0=PoweredCircularLogTube.referenceVelocity 0) :
    ∀ t : ℚ, (t:ℝ)∈Set.Icc (0:ℝ) 1 →
      ‖lengthScale • x (t:ℝ)-embed (physicalPrediction geometricQuery geometricOutputs
        (prepare geometricPrepare t) φ)‖<913/1000000 ∧
      ‖lengthScale • x (t:ℝ)-embed (physicalPrediction cartesianQuery cartesianOutputs
        (prepare cartesianPrepare t) φ)‖<313/1000000 := by
  intro t ht
  have hg := FiniteCircularCertificate.certificate (angle φ) hφ x xv hx hxv hdx hdxv hix hixv (t:ℝ) ht
  have hc := FiniteCartesianCertificate.certificate .quadratic (angle φ) hφ x xv hx hxv hdx hdxv hix hixv (t:ℝ) ht
  constructor
  · rw [physicalPrediction_eq _ _ _ geometric_phase_only]
    have heq := (FiniteBatchQueries.as_single _ _ _ geometric_phase_only
      (rate*(t:ℝ)) (angle φ)).symm.trans (FiniteBatchQueries.geometric_correct _ _)
    have htG := FiniteEvaluation.transfer (geometricPrepare++geometricQuery) geometricOutputs
      t φ ht hφ (x (t:ℝ))
      ((FiniteResponseData.predictionBudget:ℝ)+(FiniteResponseData.reconstructionTail:ℝ)*
        (FiniteResponseData.responseRadius:ℝ)) (by
        change ‖x (t:ℝ)-(PoweredCircularLogTube.reference (t:ℝ)+
          FiniteQueryGraphs.query (geometricPrepare++geometricQuery) geometricOutputs
            (rate*(t:ℝ)) (angle φ))‖≤_
        rw [heq]
        simpa only [FiniteCircularCertificate.prediction, ←FiniteQueryGraphs.geometric_correct] using hg)
    have hb : (7000000:ℝ)*((FiniteResponseData.predictionBudget:ℝ)+
        (FiniteResponseData.reconstructionTail:ℝ)*(FiniteResponseData.responseRadius:ℝ))+
        (FiniteBatchEvaluationData.geometricNumerical:ℝ)<913/1000000 := by
      have h := (Rat.cast_lt (K := ℝ)).mpr FiniteBatchEvaluationData.physical_budgets.1
      simpa only [Rat.cast_mul, Rat.cast_add, Rat.cast_div, Rat.cast_ofNat] using h
    exact htG.trans_lt hb
  · rw [physicalPrediction_eq _ _ _ cartesian_phase_only]
    have heq := (FiniteBatchQueries.as_single _ _ _ cartesian_phase_only
      (rate*(t:ℝ)) (angle φ)).symm.trans (FiniteBatchQueries.cartesian_correct _ _)
    have htC := FiniteEvaluation.transfer (cartesianPrepare++cartesianQuery) cartesianOutputs
      t φ ht hφ (x (t:ℝ)) (FiniteCartesianData.predictionBudget .quadratic:ℝ) (by
        change ‖x (t:ℝ)-(PoweredCircularLogTube.reference (t:ℝ)+
          FiniteQueryGraphs.query (cartesianPrepare++cartesianQuery) cartesianOutputs
            (rate*(t:ℝ)) (angle φ))‖≤_
        rw [heq]
        simpa only [FiniteCartesianCertificate.prediction, ←FiniteQueryGraphs.cartesian_correct] using hc)
    have hb : (7000000:ℝ)*(FiniteCartesianData.predictionBudget .quadratic:ℝ)+
        (FiniteBatchEvaluationData.cartesianNumerical:ℝ)<313/1000000 := by
      have h := (Rat.cast_lt (K := ℝ)).mpr FiniteBatchEvaluationData.physical_budgets.2
      simpa only [Rat.cast_mul, Rat.cast_add, Rat.cast_div, Rat.cast_ofNat] using h
    exact htC.trans_lt hb

end GNC.OrbitalComparison.FiniteBatchEvaluation
