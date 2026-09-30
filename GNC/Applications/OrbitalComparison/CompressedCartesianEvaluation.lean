import GNC.Applications.OrbitalComparison.CompressedCartesianGraphs
import GNC.Applications.OrbitalComparison.CompressedCartesianEvaluationData
import GNC.Applications.OrbitalComparison.FiniteBatchEvaluation
import GNC.Applications.OrbitalComparison.PoweredCircularExistence

/-! Full dyadic and physical certificates for the compressed comparator.
Both generated operation graphs have their own propagated rounding budget.
The original degree-eight graph's numerical budget is not reused.
-/
namespace GNC.OrbitalComparison.CompressedCartesianEvaluation
open ArithmeticProgram CompressedCartesianData FiniteEvaluationData
open CompressedCartesianEvaluationData
open PoweredCircularLogTube (lengthScale angleRadius rate)
open FiniteEvaluation (angle embed)
set_option maxHeartbeats 0
set_option maxRecDepth 4096

noncomputable section

/-- Same constructed orbit as the other predictors; no supplied existence
oracle or uncharged approximation error. SI units, full pointing ball. -/
theorem certificates (φ : Fin 3 → ℚ) (hφ : enorm (angle φ)≤angleRadius)
    (X : PoweredCircularExistence.Motion (angle φ)) {t : ℚ}
    (ht : (t:ℝ)∈Set.Icc (0:ℝ) 1) :
    ‖lengthScale • X.p (t:ℝ)-embed
      (FiniteEvaluation.physicalPrediction (singlePrepare++singleQuery) singleOutputs t φ)‖<749/1000000 ∧
    ‖lengthScale • X.p (t:ℝ)-embed
      (FiniteBatchEvaluation.physicalPrediction batchQuery batchOutputs
        (FiniteBatchEvaluation.prepare batchPrepare t) φ)‖<749/1000000 := by
  have hc := CompressedCartesian.certificate (angle φ) hφ X.p X.v X.continuous_p
    X.continuous_v X.derivative_p X.derivative_v X.initial_p X.initial_v (t:ℝ) ht
  have transfer (code : List (Instruction 4)) (outputs : Fin 3 → ℕ)
      (heq : FiniteQueryGraphs.query code outputs (rate*(t:ℝ)) (angle φ)=
        CompressedCartesian.position (angle φ) (t:ℝ))
      (hb : 7000000*CompressedCartesian.budget+numerical code outputs<749/1000000) :
      ‖lengthScale • X.p (t:ℝ)-embed (FiniteEvaluation.physicalPrediction code outputs t φ)‖<749/1000000 := by
    have h := FiniteEvaluation.transfer code outputs t φ ht hφ (X.p (t:ℝ))
      (CompressedCartesian.budget:ℝ) (by
        change ‖X.p (t:ℝ)-(PoweredCircularLogTube.reference (t:ℝ)+
          FiniteQueryGraphs.query code outputs (rate*(t:ℝ)) (angle φ))‖≤_
        rw [heq]
        exact hc)
    apply h.trans_lt
    have hh := (Rat.cast_lt (K := ℝ)).mpr hb
    simpa only [numerical, Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat] using hh
  refine ⟨transfer _ _ (CompressedCartesianGraphs.single_correct _ _) budgets.1,?_⟩
  rw [FiniteBatchEvaluation.physicalPrediction_eq _ _ _ batch_phase_only]
  exact transfer _ _ ((CompressedCartesianGraphs.batch_as_single _ _).trans
    (CompressedCartesianGraphs.single_correct _ _)) budgets.2

end
end GNC.OrbitalComparison.CompressedCartesianEvaluation
