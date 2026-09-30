import GNC.Applications.OrbitalComparison.WholeOutputGraphs
import GNC.Applications.OrbitalComparison.PrunedFiniteEvaluation

/-! Joint reference/deviation evaluation with its own rounding certificate.
The two graphs can share reference powers. There is no separately evaluated
reference hidden in the cost or rounding model. SI conversion is exact
rational scaling; phase and angle quantization are charged explicitly. -/
namespace GNC.OrbitalComparison.WholeOutputEvaluation
open ArithmeticProgram ArithmeticProgram.Rounding WholeOutputData FiniteEvaluationData
open FiniteEvaluation (embed angle exactQuery rationalQuery inputs)
open PoweredCircularLogTube (lengthScale angleRadius rate)
open GeometricSTMPrediction (E)
set_option maxRecDepth 4096
set_option maxHeartbeats 0

def numerical (code : List (Instruction 4)) (outputs : Fin 3 → ℕ) : ℚ :=
  7000000*(errorSum inputBudget code outputs+2*FiniteResponseData.delta)

theorem budgets (cached : Bool) :
    7000000*PrunedFinitePrediction.geometricBudget+
      numerical (geometricPrepare cached++geometricQuery cached) (geometricOutputs cached)<963/1000000 ∧
    7000000*PrunedFinitePrediction.cartesianBudget+
      numerical (cartesianPrepare cached++cartesianQuery cached) (cartesianOutputs cached)<974/1000000 := by
  cases cached <;> decide +kernel

def physicalPrediction (code : List (Instruction 4)) (outputs : Fin 3 → ℕ)
    (t : ℚ) (φ : Fin 3 → ℚ) : Fin 3 → ℚ :=
  fun i => 7000000*rationalQuery code outputs (inputs t φ) i

structure Prepared where
  phase : ℚ
  values : List ℚ

def prepare (code : List (Instruction 4)) (t : ℚ) : Prepared :=
  ⟨FiniteEvaluation.phase t, roundedRatFrom grid (inputs t 0) [] code⟩

def cachedPrediction (code : List (Instruction 4)) (outputs : Fin 3 → ℕ)
    (cache : Prepared) (φ : Fin 3 → ℚ) : Fin 3 → ℚ :=
  let v := roundedRatFrom grid (FiniteBatchEvaluation.phaseInputs cache.phase φ) cache.values code
  fun i => 7000000*v.getD (outputs i) 0

theorem cached_eq (pre body : List (Instruction 4)) (outputs : Fin 3 → ℕ)
    (h : usesOnly (fun i : Fin 4 => i == 0) pre=true) (t : ℚ) (φ : Fin 3 → ℚ) :
    cachedPrediction body outputs (prepare pre t) φ=physicalPrediction (pre++body) outputs t φ := by
  have hv := stagedRat_eq grid (fun i : Fin 4 => i == 0) pre body
    (inputs t 0) (inputs t φ) h (by
      intro i hi
      have he : i=0 := by simpa using hi
      subst i
      rfl)
  ext i
  simpa only [cachedPrediction,prepare,physicalPrediction,rationalQuery,
    FiniteBatchEvaluation.phaseInputs,inputs,stagedRat] using
    congrArg (fun v : List ℚ => 7000000*v.getD (outputs i) 0) hv

noncomputable section

/-- Transfer any already certified deviation to a joint graph. The exact
graph identity, reference truncation, input rounding and all arithmetic
rounding are required separately. -/
theorem transfer (code : List (Instruction 4)) (outputs : Fin 3 → ℕ)
    (t : ℚ) (φ : Fin 3 → ℚ) (ht : (t:ℝ)∈Set.Icc (0:ℝ) 1)
    (hφ : enorm (angle φ)≤angleRadius) (x y : E) (B : ℝ)
    (hcert : ‖x-(PoweredCircularLogTube.reference (t:ℝ)+y)‖≤B)
    (hid : exactQuery code outputs (FiniteQueryGraphs.input (rate*(t:ℝ)) (angle φ))=
      FiniteCircularResponse.polynomialReference (rate*(t:ℝ))+y) :
    ‖lengthScale • x-embed (physicalPrediction code outputs t φ)‖≤
      lengthScale*B+(numerical code outputs:ℝ) := by
  have hr := FiniteEvaluation.query_error inputBudget
    (FiniteQueryGraphs.input (rate*(t:ℝ)) (angle φ)) (inputs t φ)
    (FiniteEvaluation.input_holds t φ ht hφ) code outputs
  rw [hid,norm_sub_rev] at hr
  have hp := FiniteCircularResponse.reference_error ht
  have hδ : (0:ℝ)≤(FiniteResponseData.delta:ℝ) := by
    exact_mod_cast FiniteResponseData.inputs.2.2.2.2.2.2.2
  have href : ‖PoweredCircularLogTube.reference (t:ℝ)-
      FiniteCircularResponse.polynomialReference (rate*(t:ℝ))‖≤2*(FiniteResponseData.delta:ℝ) :=
    hp.trans (mul_le_of_le_one_right (by positivity) (pow_le_one₀ ht.1 ht.2))
  have hm : ‖(PoweredCircularLogTube.reference (t:ℝ)+y)-
      embed (rationalQuery code outputs (inputs t φ))‖≤
      2*(FiniteResponseData.delta:ℝ)+(errorSum inputBudget code outputs:ℝ) := by
    have h := norm_sub_le_norm_sub_add_norm_sub (PoweredCircularLogTube.reference (t:ℝ)+y)
      (FiniteCircularResponse.polynomialReference (rate*(t:ℝ))+y)
      (embed (rationalQuery code outputs (inputs t φ)))
    simp only [add_sub_add_right_eq_sub] at h
    exact h.trans (add_le_add href hr)
  have hn := (norm_sub_le_norm_sub_add_norm_sub x
    (PoweredCircularLogTube.reference (t:ℝ)+y)
    (embed (rationalQuery code outputs (inputs t φ)))).trans (add_le_add hcert hm)
  have hout : embed (physicalPrediction code outputs t φ)=
      lengthScale • embed (rationalQuery code outputs (inputs t φ)) := by
    ext i
    simp [embed,physicalPrediction,PoweredCircularLogTube.lengthScale]
  rw [hout,←smul_sub,norm_smul]
  have hL : (0:ℝ)≤lengthScale := by norm_num [PoweredCircularLogTube.lengthScale]
  rw [Real.norm_eq_abs,abs_of_nonneg hL]
  have h := mul_le_mul_of_nonneg_left hn hL
  simpa only [numerical,Rat.cast_mul,Rat.cast_add,Rat.cast_ofNat,
    PoweredCircularLogTube.lengthScale,mul_add,add_assoc,add_comm,add_left_comm] using h

theorem certificates (cached : Bool) (φ : Fin 3 → ℚ) (hφ : enorm (angle φ)≤angleRadius)
    (X : PoweredCircularExistence.Motion (angle φ)) {t : ℚ}
    (ht : (t:ℝ)∈Set.Icc (0:ℝ) 1) :
    ‖lengthScale • X.p (t:ℝ)-embed
      (cachedPrediction (geometricQuery cached) (geometricOutputs cached)
        (prepare (geometricPrepare cached) t) φ)‖<963/1000000 ∧
    ‖lengthScale • X.p (t:ℝ)-embed
      (cachedPrediction (cartesianQuery cached) (cartesianOutputs cached)
        (prepare (cartesianPrepare cached) t) φ)‖<974/1000000 := by
  have hc := PrunedFinitePrediction.certificates (angle φ) hφ X ht
  constructor
  · rw [cached_eq _ _ _ (geometric_phase_only cached)]
    have h := transfer (geometricPrepare cached++geometricQuery cached) (geometricOutputs cached)
      t φ ht hφ (X.p (t:ℝ)) _ _ hc.1 (WholeOutputGraphs.geometric_correct cached (t:ℝ) (angle φ))
    apply h.trans_lt
    have hb := (Rat.cast_lt (K := ℝ)).mpr (budgets cached).1
    simpa only [Rat.cast_add,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_div,
      PoweredCircularLogTube.lengthScale] using hb
  · rw [cached_eq _ _ _ (cartesian_phase_only cached)]
    have h := transfer (cartesianPrepare cached++cartesianQuery cached) (cartesianOutputs cached)
      t φ ht hφ (X.p (t:ℝ)) _ _ hc.2 (WholeOutputGraphs.cartesian_correct cached (t:ℝ) (angle φ))
    apply h.trans_lt
    have hb := (Rat.cast_lt (K := ℝ)).mpr (budgets cached).2
    simpa only [Rat.cast_add,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_div,
      PoweredCircularLogTube.lengthScale] using hb

theorem exists_certified_predictions (φ : Fin 3 → ℚ) (hφ : enorm (angle φ)≤angleRadius) :
    ∃ X : PoweredCircularExistence.Motion (angle φ),
      (∀ Y : PoweredCircularExistence.Motion (angle φ), ∀ t ∈ Set.Icc (0:ℝ) 1,
        Y.p t=X.p t ∧ Y.v t=X.v t) ∧
      ∀ cached : Bool, ∀ t : ℚ, (t:ℝ)∈Set.Icc (0:ℝ) 1 →
        ‖lengthScale • X.p (t:ℝ)-embed
          (cachedPrediction (geometricQuery cached) (geometricOutputs cached)
            (prepare (geometricPrepare cached) t) φ)‖<963/1000000 ∧
        ‖lengthScale • X.p (t:ℝ)-embed
          (cachedPrediction (cartesianQuery cached) (cartesianOutputs cached)
            (prepare (cartesianPrepare cached) t) φ)‖<974/1000000 := by
  exact ⟨PoweredCircularExistence.trajectory (angle φ) hφ,
    PoweredCircularExistence.unique (angle φ) hφ,fun cached t ht => certificates cached φ hφ _ ht⟩

end

/-- One phase multiplication/quantization per epoch; three exact rational
SI multiplications and three angle quantizations per attitude. -/
def batchWork (pre body : List (Instruction 4)) (n : ℕ) : Work :=
  ((⟨1,1,0⟩ : Work).plus (work pre)).plus (((⟨3,3,0⟩ : Work).plus (work body)).repeat n)

theorem single_work :
    (batchWork (geometricPrepare false) (geometricQuery false) 1).binary=76 ∧
    (batchWork (cartesianPrepare false) (cartesianQuery false) 1).binary=92 := by decide +kernel

theorem batch_work (n : ℕ) :
    (batchWork (geometricPrepare true) (geometricQuery true) n).binary=52+25*n ∧
    (batchWork (cartesianPrepare true) (cartesianQuery true) n).binary=70+29*n := by
  have hp : (work (geometricPrepare true)).binary=51 := by decide +kernel
  have hq : (work (geometricQuery true)).binary=22 := by decide +kernel
  have hcp : (work (cartesianPrepare true)).binary=69 := by decide +kernel
  have hcq : (work (cartesianQuery true)).binary=26 := by decide +kernel
  simp [batchWork,Work.plus,Work.repeat,hp,hq,hcp,hcq,Nat.mul_comm]

theorem amortization (n g c : ℕ) :
    g+(batchWork (geometricPrepare true) (geometricQuery true) n).binary<
      c+(batchWork (cartesianPrepare true) (cartesianQuery true) n).binary ↔
    g<c+18+4*n := by
  rw [(batch_work n).1,(batch_work n).2]
  omega

theorem other_primitive_work (n : ℕ) :
    (batchWork (geometricPrepare true) (geometricQuery true) n).quantize=78+25*n ∧
    (batchWork (cartesianPrepare true) (cartesianQuery true) n).quantize=109+29*n ∧
    (batchWork (geometricPrepare true) (geometricQuery true) n).negate=1+3*n ∧
    (batchWork (cartesianPrepare true) (cartesianQuery true) n).negate=0 := by
  have hp : work (geometricPrepare true)=⟨51,77,1⟩ := by decide +kernel
  have hq : work (geometricQuery true)=⟨22,22,3⟩ := by decide +kernel
  have hcp : work (cartesianPrepare true)=⟨69,108,0⟩ := by decide +kernel
  have hcq : work (cartesianQuery true)=⟨26,26,0⟩ := by decide +kernel
  simp [batchWork,Work.plus,Work.repeat,hp,hq,hcp,hcq,Nat.mul_comm]

end GNC.OrbitalComparison.WholeOutputEvaluation
