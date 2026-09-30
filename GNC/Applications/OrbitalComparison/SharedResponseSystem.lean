import GNC.Applications.OrbitalComparison.SharedResponseData.Checked
import GNC.Applications.OrbitalComparison.TangentialReferenceMotion

/-! Polynomial response certificates against the actual, computed reference.
These theorems charge reference/gradient/input uncertainty and all handoffs.
They certify solutions of the displayed sparse affine equations. Identifying
those solutions with the physical response reconstruction is a separate step.
-/
noncomputable section
namespace GNC.OrbitalComparison.SharedResponseSystem
open Set PolynomialODE PolynomialOrder PolynomialOrbit PolynomialOrbitTransition
open TangentialReferenceMotion
set_option maxHeartbeats 0

private theorem negative_frame_piece (r : Reference) (j : ℕ) (hj : j<32)
    (u : ℝ) (hu : u ∈ Icc (0:ℝ) (13/640)) (k : Fin 3) :
    |-(TangentialReferenceData.alpha:ℝ)*polynomialFrame (lift (r.w ((j:ℝ)*(13/640)+u))) k 1-
      TangentialReference.observable
        (PolynomialGravityObservable.frameInput TangentialReferenceData.alpha k 1).negate j u|≤
      (TangentialReference.thrustBudget:ℝ) := by
  have h := TangentialReference.observable_pieces r.w r.continuous r.positive r.derivative r.initial
    (PolynomialGravityObservable.frameInput TangentialReferenceData.alpha k 1).negate j hj u hu
  simp only [Expr.value,PolynomialGravityObservable.frameInput_value] at h
  rw [neg_mul]
  apply h.trans
  exact_mod_cast mul_le_mul_of_nonneg_right
    (PolynomialGravityObservable.frameInput_slope TangentialReferenceData.alpha
      (by norm_num [TangentialReferenceData.errorBound] : (0:ℚ)≤4/3+TangentialReferenceData.errorBound) k 1)
    (by norm_num [TangentialReferenceData.errorBound] : (0:ℚ)≤TangentialReferenceData.errorBound)


def geometricOperator (r : Reference) (t : ℝ) : Fin 8 → Fin 8 → ℝ :=
  let g := gravityMatrix (lift (r.w t))
  !![0,0,0,0,1,0,0,0;
    0,0,0,0,0,1,0,0;
    0,0,0,0,0,0,1,0;
    0,0,0,0,0,0,0,1;
    g 0 0,g 0 1,0,0,0,0,0,0;
    g 1 0,g 1 1,0,0,0,0,0,0;
    0,0,g 2 2,0,0,0,0,0;
    0,0,0,g 2 2,0,0,0,0]

def geometricInput (r : Reference) (t : ℝ) : Fin 8 → ℝ :=
  let f := fun k => (TangentialReferenceData.alpha:ℝ)*polynomialFrame (lift (r.w t)) k 1
  ![0,0,0,0,-f 1,f 0,f 1,-f 0]

def geometricSequence (j : ℕ) : AffinePolynomialStep.Step 8 :=
  if hj : j<32 then SharedResponseData.geometricSteps ⟨j,hj⟩ else SharedResponseData.geometric0

theorem geometric_coefficients (r : Reference) (j : ℕ) (hj : j<32)
    (u : ℝ) (hu : u ∈ Icc (0:ℝ) (13/640)) :
    (∀ k l, |geometricOperator r ((j:ℝ)*(13/640)+u) k l-
      value ((geometricSequence j).operator k l) u|≤((geometricSequence j).operatorError:ℝ)) ∧
    (∀ k, |geometricInput r ((j:ℝ)*(13/640)+u) k-
      value ((geometricSequence j).input k) u|≤((geometricSequence j).inputError:ℝ)) := by
  have hg := TangentialReference.gradient_pieces r.w r.continuous r.positive r.derivative r.initial j hj u hu
  have hf := TangentialReference.frameInput_pieces r.w r.continuous r.positive r.derivative r.initial j hj u hu
  have hn := negative_frame_piece r j hj u hu
  have hg0 : (0:ℝ)≤(TangentialReference.gradientBudget:ℝ) := by
    norm_num [TangentialReference.gradientBudget,TangentialReferenceData.errorBound]
  have hf0 : (0:ℝ)≤(TangentialReference.thrustBudget:ℝ) := by
    norm_num [TangentialReference.thrustBudget,TangentialReferenceData.errorBound,TangentialReferenceData.alpha]
  simp only [geometricSequence,dif_pos hj,SharedResponseData.geometric_operators,SharedResponseData.geometric_inputs,
    SharedResponseData.geometric_operatorErrors,SharedResponseData.geometric_inputErrors]
  simp only [TangentialReference.observable,TangentialReference.sequence,dif_pos hj] at hg hf hn
  constructor
  · intro k l
    fin_cases k <;> fin_cases l <;>
      simp only [geometricOperator,SharedResponseData.geometricOperator,Matrix.cons_val_succ,Matrix.cons_val_zero]
    all_goals first
      | simpa only [value] using hg 0 0
      | simpa only [value] using hg 0 1
      | simpa only [value] using hg 1 0
      | simpa only [value] using hg 1 1
      | simpa only [value] using hg 2 2
      | simpa [value,Planning.PolynomialKernel.evaluate] using hg0
  · intro k
    fin_cases k <;>
      simp only [geometricInput,SharedResponseData.geometricInput,Matrix.cons_val_succ,Matrix.cons_val_zero]
    all_goals first
      | simpa only [value] using hf 0 1
      | simpa only [value] using hf 1 1
      | simpa only [value,neg_mul] using hn 0
      | simpa only [value,neg_mul] using hn 1
      | simpa [value,Planning.PolynomialKernel.evaluate] using hf0

theorem geometric_pieces (r : Reference) (x : ℝ → Fin 8 → ℝ) (hx : Continuous x) (hx0 : x 0=0)
    (hd : ∀ t ∈ Icc (0:ℝ) (13/20), HasDerivAt x
      (fun k => (∑ l, geometricOperator r t k l*x t l)+geometricInput r t k) t)
    (j : ℕ) (hj : j<32) (u : ℝ) (hu : u ∈ Icc (0:ℝ) (13/640)) :
    ‖x ((j:ℝ)*(13/640)+u)-curve (geometricSequence j).coefficients u‖<
      (SharedResponseData.geometricError:ℝ) := by
  have hv (k : ℕ) (hk : k<32) : (geometricSequence k).Valid := by
    simpa [geometricSequence,hk] using SharedResponseData.geometric_valid ⟨k,hk⟩
  have hdur (k : ℕ) (hk : k<32) : (geometricSequence k).duration=13/640 := by
    simp [geometricSequence,hk,SharedResponseData.geometric_durations,TangentialReferenceData.stepLength]
  have hjn (k : ℕ) (hk : k+1<32) :
      AffinePolynomialStep.Compatible (geometricSequence k) (geometricSequence (k+1)) := by
    have hk' : k<32 := by omega
    simpa [geometricSequence,hk,hk'] using SharedResponseData.geometric_joins ⟨k,by omega⟩
  have hi : ‖x 0-curve (geometricSequence 0).coefficients 0‖≤((geometricSequence 0).initialError:ℝ) := by
    have he : curve (geometricSequence 0).coefficients 0=0 := by
      ext k
      change PolynomialOrder.value _ 0=0
      rw [show (0:ℝ)=((0:ℚ):ℝ) by norm_num,PolynomialOrder.value_at_rational]
      simp [geometricSequence,SharedResponseData.geometric_initial]
    rw [hx0,he,sub_self,norm_zero]
    exact_mod_cast (hv 0 (by norm_num)).2.1
  have h := AffinePolynomialStep.chain_sound geometricSequence 32 (h := 13/640)
    (by norm_num) hv hdur hjn (geometricOperator r) (geometricInput r) x hx
    (by intro t ht; apply hd t; norm_num at ht; exact ht)
    (fun k hk t ht => by simpa using (geometric_coefficients r k hk t (by simpa using ht)).1)
    (fun k hk t ht => by simpa using (geometric_coefficients r k hk t (by simpa using ht)).2)
    hi j hj u (by simpa using hu)
  have he : (geometricSequence j).error≤SharedResponseData.geometricError := by
    simp only [geometricSequence,dif_pos hj]
    exact SharedResponseData.geometric_errors ⟨j,hj⟩
  exact lt_of_lt_of_le (by simpa using h) (by exact_mod_cast he)

def cartesianOperator (r : Reference) (t : ℝ) : Fin 20 → Fin 20 → ℝ :=
  let g := gravityMatrix (lift (r.w t))
  !![0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0;
    0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0;
    0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0;
    0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0;
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0;
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0;
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0;
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0;
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0;
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1;
    g 0 0,g 0 1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;
    g 1 0,g 1 1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;
    0,0,g 0 0,g 0 1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;
    0,0,g 1 0,g 1 1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;
    0,0,0,0,g 0 0,g 0 1,0,0,0,0,0,0,0,0,0,0,0,0,0,0;
    0,0,0,0,g 1 0,g 1 1,0,0,0,0,0,0,0,0,0,0,0,0,0,0;
    0,0,0,0,0,0,g 0 0,g 0 1,0,0,0,0,0,0,0,0,0,0,0,0;
    0,0,0,0,0,0,g 1 0,g 1 1,0,0,0,0,0,0,0,0,0,0,0,0;
    0,0,0,0,0,0,0,0,g 2 2,0,0,0,0,0,0,0,0,0,0,0;
    0,0,0,0,0,0,0,0,0,g 2 2,0,0,0,0,0,0,0,0,0,0]

def cartesianInput (r : Reference) (t : ℝ) : Fin 20 → ℝ :=
  let f := fun k => (TangentialReferenceData.alpha:ℝ)*polynomialFrame (lift (r.w t)) k 1
  ![0,0,0,0,0,0,0,0,0,0,f 0,0,f 1,0,0,f 0,0,f 1,f 0,f 1]

def cartesianSequence (j : ℕ) : AffinePolynomialStep.Step 20 :=
  if hj : j<32 then SharedResponseData.cartesianSteps ⟨j,hj⟩ else SharedResponseData.cartesian0

theorem cartesian_coefficients (r : Reference) (j : ℕ) (hj : j<32)
    (u : ℝ) (hu : u ∈ Icc (0:ℝ) (13/640)) :
    (∀ k l, |cartesianOperator r ((j:ℝ)*(13/640)+u) k l-
      value ((cartesianSequence j).operator k l) u|≤((cartesianSequence j).operatorError:ℝ)) ∧
    (∀ k, |cartesianInput r ((j:ℝ)*(13/640)+u) k-
      value ((cartesianSequence j).input k) u|≤((cartesianSequence j).inputError:ℝ)) := by
  have hg := TangentialReference.gradient_pieces r.w r.continuous r.positive r.derivative r.initial j hj u hu
  have hf := TangentialReference.frameInput_pieces r.w r.continuous r.positive r.derivative r.initial j hj u hu
  have hn := negative_frame_piece r j hj u hu
  have hg0 : (0:ℝ)≤(TangentialReference.gradientBudget:ℝ) := by
    norm_num [TangentialReference.gradientBudget,TangentialReferenceData.errorBound]
  have hf0 : (0:ℝ)≤(TangentialReference.thrustBudget:ℝ) := by
    norm_num [TangentialReference.thrustBudget,TangentialReferenceData.errorBound,TangentialReferenceData.alpha]
  simp only [cartesianSequence,dif_pos hj,SharedResponseData.cartesian_operators,SharedResponseData.cartesian_inputs,
    SharedResponseData.cartesian_operatorErrors,SharedResponseData.cartesian_inputErrors]
  simp only [TangentialReference.observable,TangentialReference.sequence,dif_pos hj] at hg hf hn
  constructor
  · intro k l
    fin_cases k <;> fin_cases l <;>
      simp only [cartesianOperator,SharedResponseData.cartesianOperator,Matrix.cons_val_succ,Matrix.cons_val_zero]
    all_goals first
      | simpa only [value] using hg 0 0
      | simpa only [value] using hg 0 1
      | simpa only [value] using hg 1 0
      | simpa only [value] using hg 1 1
      | simpa only [value] using hg 2 2
      | simpa [value,Planning.PolynomialKernel.evaluate] using hg0
  · intro k
    fin_cases k <;>
      simp only [cartesianInput,SharedResponseData.cartesianInput,Matrix.cons_val_succ,Matrix.cons_val_zero]
    all_goals first
      | simpa only [value] using hf 0 1
      | simpa only [value] using hf 1 1
      | simpa only [value,neg_mul] using hn 0
      | simpa only [value,neg_mul] using hn 1
      | simpa [value,Planning.PolynomialKernel.evaluate] using hf0

theorem cartesian_pieces (r : Reference) (x : ℝ → Fin 20 → ℝ) (hx : Continuous x) (hx0 : x 0=0)
    (hd : ∀ t ∈ Icc (0:ℝ) (13/20), HasDerivAt x
      (fun k => (∑ l, cartesianOperator r t k l*x t l)+cartesianInput r t k) t)
    (j : ℕ) (hj : j<32) (u : ℝ) (hu : u ∈ Icc (0:ℝ) (13/640)) :
    ‖x ((j:ℝ)*(13/640)+u)-curve (cartesianSequence j).coefficients u‖<
      (SharedResponseData.cartesianError:ℝ) := by
  have hv (k : ℕ) (hk : k<32) : (cartesianSequence k).Valid := by
    simpa [cartesianSequence,hk] using SharedResponseData.cartesian_valid ⟨k,hk⟩
  have hdur (k : ℕ) (hk : k<32) : (cartesianSequence k).duration=13/640 := by
    simp [cartesianSequence,hk,SharedResponseData.cartesian_durations,TangentialReferenceData.stepLength]
  have hjn (k : ℕ) (hk : k+1<32) :
      AffinePolynomialStep.Compatible (cartesianSequence k) (cartesianSequence (k+1)) := by
    have hk' : k<32 := by omega
    simpa [cartesianSequence,hk,hk'] using SharedResponseData.cartesian_joins ⟨k,by omega⟩
  have hi : ‖x 0-curve (cartesianSequence 0).coefficients 0‖≤((cartesianSequence 0).initialError:ℝ) := by
    have he : curve (cartesianSequence 0).coefficients 0=0 := by
      ext k
      change PolynomialOrder.value _ 0=0
      rw [show (0:ℝ)=((0:ℚ):ℝ) by norm_num,PolynomialOrder.value_at_rational]
      simp [cartesianSequence,SharedResponseData.cartesian_initial]
    rw [hx0,he,sub_self,norm_zero]
    exact_mod_cast (hv 0 (by norm_num)).2.1
  have h := AffinePolynomialStep.chain_sound cartesianSequence 32 (h := 13/640)
    (by norm_num) hv hdur hjn (cartesianOperator r) (cartesianInput r) x hx
    (by intro t ht; apply hd t; norm_num at ht; exact ht)
    (fun k hk t ht => by simpa using (cartesian_coefficients r k hk t (by simpa using ht)).1)
    (fun k hk t ht => by simpa using (cartesian_coefficients r k hk t (by simpa using ht)).2)
    hi j hj u (by simpa using hu)
  have he : (cartesianSequence j).error≤SharedResponseData.cartesianError := by
    simp only [cartesianSequence,dif_pos hj]
    exact SharedResponseData.cartesian_errors ⟨j,hj⟩
  exact lt_of_lt_of_le (by simpa using h) (by exact_mod_cast he)

end GNC.OrbitalComparison.SharedResponseSystem
