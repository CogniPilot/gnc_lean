import GNC.Applications.OrbitalComparison.PrunedFiniteGraphs
import GNC.Applications.OrbitalComparison.FinitePredictionWork

/-! The stronger mixed-degree comparison includes each selected program's
own rounding budget and complete output primitive count. Physical existence
is supplied by the existing powered-circle IVP theorem, not a numerical oracle.
-/
namespace GNC.OrbitalComparison.PrunedFiniteEvaluation
open ArithmeticProgram PrunedFiniteData FiniteEvaluationData
open PrunedFinitePrediction
open PoweredCircularLogTube (lengthScale angleRadius rate)
open FiniteEvaluation (angle embed)
open CompressedCartesianEvaluationData (numerical)
set_option maxHeartbeats 0
set_option maxRecDepth 4096

theorem budgets (cached : Bool) :
    7000000*geometricBudget+numerical (geometricPrepare cached++geometricQuery cached)
      (geometricOutputs cached)<963/1000000 ∧
    7000000*cartesianBudget+numerical (cartesianPrepare cached++cartesianQuery cached)
      (cartesianOutputs cached)<974/1000000 := by
  cases cached <;> decide +kernel

noncomputable section

/-- All times and the full three-dimensional pointing ball, for the same
actual nonlinear orbit. Both single and phase-cached implementations pass. -/
theorem certificates (cached : Bool) (φ : Fin 3 → ℚ) (hφ : enorm (angle φ)≤angleRadius)
    (X : PoweredCircularExistence.Motion (angle φ)) {t : ℚ}
    (ht : (t:ℝ)∈Set.Icc (0:ℝ) 1) :
    ‖lengthScale • X.p (t:ℝ)-embed
      (FiniteBatchEvaluation.physicalPrediction (geometricQuery cached) (geometricOutputs cached)
        (FiniteBatchEvaluation.prepare (geometricPrepare cached) t) φ)‖<963/1000000 ∧
    ‖lengthScale • X.p (t:ℝ)-embed
      (FiniteBatchEvaluation.physicalPrediction (cartesianQuery cached) (cartesianOutputs cached)
        (FiniteBatchEvaluation.prepare (cartesianPrepare cached) t) φ)‖<974/1000000 := by
  have hc := PrunedFinitePrediction.certificates (angle φ) hφ X ht
  have transfer (code : List (Instruction 4)) (outputs : Fin 3 → ℕ) (B C : ℚ)
      (hphysical : ‖X.p (t:ℝ)-(PoweredCircularLogTube.reference (t:ℝ)+
        FiniteQueryGraphs.query code outputs (rate*(t:ℝ)) (angle φ))‖≤(B:ℝ))
      (hb : 7000000*B+numerical code outputs<C) :
      ‖lengthScale • X.p (t:ℝ)-embed (FiniteEvaluation.physicalPrediction code outputs t φ)‖<(C:ℝ) := by
    have h := FiniteEvaluation.transfer code outputs t φ ht hφ (X.p (t:ℝ)) B hphysical
    apply h.trans_lt
    have hh := (Rat.cast_lt (K := ℝ)).mpr hb
    simpa only [numerical, Rat.cast_add, Rat.cast_mul, Rat.cast_ofNat] using hh
  constructor
  · rw [FiniteBatchEvaluation.physicalPrediction_eq _ _ _ (geometric_phase_only cached)]
    have hp : ‖X.p (t:ℝ)-(PoweredCircularLogTube.reference (t:ℝ)+
        FiniteQueryGraphs.query (geometricPrepare cached++geometricQuery cached)
          (geometricOutputs cached) (rate*(t:ℝ)) (angle φ))‖≤(geometricBudget:ℝ) := by
      rw [PrunedFiniteGraphs.geometric_correct]
      exact hc.1
    simpa using transfer _ _ geometricBudget (963/1000000) hp (budgets cached).1
  · rw [FiniteBatchEvaluation.physicalPrediction_eq _ _ _ (cartesian_phase_only cached)]
    have hp : ‖X.p (t:ℝ)-(PoweredCircularLogTube.reference (t:ℝ)+
        FiniteQueryGraphs.query (cartesianPrepare cached++cartesianQuery cached)
          (cartesianOutputs cached) (rate*(t:ℝ)) (angle φ))‖≤(cartesianBudget:ℝ) := by
      rw [PrunedFiniteGraphs.cartesian_correct]
      exact hc.2
    simpa using transfer _ _ cartesianBudget (974/1000000) hp (budgets cached).2

/-- A physical solution exists and is unique; neither the true orbit nor
an exact response is an external oracle for these executable certificates. -/
theorem exists_certified_predictions (φ : Fin 3 → ℚ)
    (hφ : enorm (angle φ)≤angleRadius) :
    ∃ X : PoweredCircularExistence.Motion (angle φ),
      (∀ Y : PoweredCircularExistence.Motion (angle φ), ∀ t ∈ Set.Icc (0:ℝ) 1,
        Y.p t=X.p t ∧ Y.v t=X.v t) ∧
      ∀ cached : Bool, ∀ t : ℚ, (t:ℝ)∈Set.Icc (0:ℝ) 1 →
        ‖lengthScale • X.p (t:ℝ)-embed
          (FiniteBatchEvaluation.physicalPrediction (geometricQuery cached) (geometricOutputs cached)
            (FiniteBatchEvaluation.prepare (geometricPrepare cached) t) φ)‖<963/1000000 ∧
        ‖lengthScale • X.p (t:ℝ)-embed
          (FiniteBatchEvaluation.physicalPrediction (cartesianQuery cached) (cartesianOutputs cached)
            (FiniteBatchEvaluation.prepare (cartesianPrepare cached) t) φ)‖<974/1000000 := by
  let X := PoweredCircularExistence.trajectory (angle φ) hφ
  exact ⟨X,PoweredCircularExistence.unique (angle φ) hφ,
    fun cached t ht => certificates cached φ hφ X ht⟩

end

open ArithmeticProgram.Rounding FinitePredictionWork

theorem single_work :
    (batch (geometricPrepare false) (geometricQuery false) 1).binary=78 ∧
    (batch (cartesianPrepare false) (cartesianQuery false) 1).binary=94 := by decide +kernel

theorem batch_work (n : ℕ) :
    (batch (geometricPrepare true) (geometricQuery true) n).binary=53+26*n ∧
    (batch (cartesianPrepare true) (cartesianQuery true) n).binary=71+30*n := by
  have hp : (work (geometricPrepare true)).binary=20 := by decide +kernel
  have hq : (work (geometricQuery true)).binary=20 := by decide +kernel
  have hcp : (work (cartesianPrepare true)).binary=38 := by decide +kernel
  have hcq : (work (cartesianQuery true)).binary=24 := by decide +kernel
  simp [batch, common_work, output, Work.plus, Work.repeat, hp, hq, hcp, hcq, Nat.mul_comm]

theorem amortization (n g c : ℕ) :
    g+(batch (geometricPrepare true) (geometricQuery true) n).binary<
      c+(batch (cartesianPrepare true) (cartesianQuery true) n).binary ↔
    g<c+18+4*n := by
  rw [(batch_work n).1,(batch_work n).2]
  omega

theorem other_primitive_work (n : ℕ) :
    (batch (geometricPrepare true) (geometricQuery true) n).quantize=80+23*n ∧
    (batch (cartesianPrepare true) (cartesianQuery true) n).quantize=111+27*n ∧
    (batch (geometricPrepare true) (geometricQuery true) n).negate=1+3*n ∧
    (batch (cartesianPrepare true) (cartesianQuery true) n).negate=0 := by
  have hp : work (geometricPrepare true)=⟨20,30,1⟩ := by decide +kernel
  have hq : work (geometricQuery true)=⟨20,20,3⟩ := by decide +kernel
  have hcp : work (cartesianPrepare true)=⟨38,61,0⟩ := by decide +kernel
  have hcq : work (cartesianQuery true)=⟨24,24,0⟩ := by decide +kernel
  simp [batch, common_work, output, Work.plus, Work.repeat, hp, hq, hcp, hcq, Nat.mul_comm]

end GNC.OrbitalComparison.PrunedFiniteEvaluation
