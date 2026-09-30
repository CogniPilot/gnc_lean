import GNC.Applications.OrbitalComparison.TangentialResponseData.Checked
import GNC.Applications.OrbitalComparison.TangentialResponseColumns

/-! Certified finite response histories along the noncircular reference.
Reference-coefficient error, polynomial residuals and every mesh handoff
are included. Phase time here runs from 0 to 13/20, as in the reference
certificate; the physical prediction uses normalized time from 0 to 1.
-/
noncomputable section
open scoped Matrix
namespace GNC.OrbitalComparison.TangentialFiniteResponse
open Set PolynomialODE PolynomialOrbit PolynomialOrbitTransition PolynomialOrder
open TangentialReferenceMotion
open ThrustSupport (euclideanEquiv)

def phasePosition (r : Reference) (t : ℝ) : E := euclideanEquiv (position (r.w t))
def phaseForce (r : Reference) (i : Fin 3) (t : ℝ) : E :=
  (TangentialReferenceData.alpha:ℝ) •
    rotationIsometry (PlanarAttitudeFrame.rotation (r.w t) (r.positive t))
      (euclideanEquiv (Pi.single i 1))
abbrev PhaseResponse (r : Reference) (i : Fin 3) :=
  GravityLinearResponse.Response 1 1 (phasePosition r) (phaseForce r i)

theorem exists_response (r : Reference) (i : Fin 3) : Nonempty (PhaseResponse r i) := by
  apply GravityLinearResponse.Response.exists 1 1
    (euclideanEquiv.continuous.comp (PlanarReferenceMotion.position_continuous r.continuous)) _
    ((euclideanEquiv.continuous.comp
      (PlanarReferenceMotion.rotated_continuous r.continuous r.positive (Pi.single i 1))).const_smul _)
  intro t
  apply norm_ne_zero_iff.mp
  change enorm (position (r.w t))≠0
  rw [position_norm]
  exact (r.positive _).ne'

def packed (p v : E) : Fin 6 → ℝ :=
  ![(euclideanEquiv.symm p) 0,(euclideanEquiv.symm p) 1,(euclideanEquiv.symm p) 2,
    (euclideanEquiv.symm v) 0,(euclideanEquiv.symm v) 1,(euclideanEquiv.symm v) 2]
def phaseOperator (r : Reference) (t : ℝ) : Fin 6 → Fin 6 → ℝ :=
  let g := gravityMatrix (lift (r.w t))
  !![0,0,0,1,0,0; 0,0,0,0,1,0; 0,0,0,0,0,1;
    g 0 0,g 0 1,g 0 2,0,0,0; g 1 0,g 1 1,g 1 2,0,0,0;
    g 2 0,g 2 1,g 2 2,0,0,0]
def phaseInput (r : Reference) (i : Fin 3) (t : ℝ) : Fin 6 → ℝ :=
  let f := fun k => (TangentialReferenceData.alpha:ℝ)*polynomialFrame (lift (r.w t)) k i
  ![0,0,0,f 0,f 1,f 2]

theorem packed_continuous (r : Reference) (i : Fin 3) (S : PhaseResponse r i) :
    Continuous (fun t => packed (S.p t) (S.v t)) := by
  have hp := euclideanEquiv.symm.continuous.comp S.continuous_p
  have hv := euclideanEquiv.symm.continuous.comp S.continuous_v
  apply continuous_pi
  intro k
  fin_cases k <;> simp [packed,Matrix.cons_val_succ] <;> fun_prop

theorem packed_derivative (r : Reference) (i : Fin 3) (S : PhaseResponse r i)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) (13/20)) :
    HasDerivAt (fun u => packed (S.p u) (S.v u))
      (fun k => (∑ l, phaseOperator r t k l*packed (S.p t) (S.v t) l)+phaseInput r i t k) t := by
  have ht1 : t ∈ Icc (0:ℝ) 1 := ⟨ht.1,by linarith [ht.2]⟩
  have hp := euclideanEquiv.symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t
    (S.derivative_p t ht1)
  have hv := euclideanEquiv.symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t
    (S.derivative_v t ht1)
  have hg : euclideanEquiv.symm (Gravity.gradient 1 (phasePosition r t) (S.p t))=
      gravityMatrix (lift (r.w t)) *ᵥ euclideanEquiv.symm (S.p t) := by
    exact gravity_matrix (r.w t) (euclideanEquiv.symm (S.p t))
  have hf : euclideanEquiv.symm (phaseForce r i t)=
      fun k => (TangentialReferenceData.alpha:ℝ)*polynomialFrame (lift (r.w t)) k i := by
    ext k
    simp [phaseForce,rotationIsometry,euclideanEquiv,rotate,PlanarAttitudeFrame.rotation,
      Matrix.mulVec,dotProduct,Pi.single_apply]
  change HasDerivAt (fun u => euclideanEquiv.symm (S.v u))
    (euclideanEquiv.symm (1 • (Gravity.gradient 1 (phasePosition r t) (S.p t)+phaseForce r i t))) t at hv
  simp only [one_smul,map_add,hg,hf] at hv
  apply hasDerivAt_pi.mpr
  intro k
  fin_cases k
  all_goals first
    | simpa [packed,phaseOperator,phaseInput,Matrix.mulVec,dotProduct,
        Fin.sum_univ_succ,Matrix.cons_val_succ] using hasDerivAt_pi.mp hp 0
    | simpa [packed,phaseOperator,phaseInput,Matrix.mulVec,dotProduct,
        Fin.sum_univ_succ,Matrix.cons_val_succ] using hasDerivAt_pi.mp hp 1
    | simpa [packed,phaseOperator,phaseInput,Matrix.mulVec,dotProduct,
        Fin.sum_univ_succ,Matrix.cons_val_succ] using hasDerivAt_pi.mp hp 2
    | simpa [packed,phaseOperator,phaseInput,Matrix.mulVec,dotProduct,
        Fin.sum_univ_succ,Matrix.cons_val_succ] using hasDerivAt_pi.mp hv 0
    | simpa [packed,phaseOperator,phaseInput,Matrix.mulVec,dotProduct,
        Fin.sum_univ_succ,Matrix.cons_val_succ] using hasDerivAt_pi.mp hv 1
    | simpa [packed,phaseOperator,phaseInput,Matrix.mulVec,dotProduct,
        Fin.sum_univ_succ,Matrix.cons_val_succ] using hasDerivAt_pi.mp hv 2

def sequence (i : Fin 3) (j : ℕ) : AffinePolynomialStep.Step 6 :=
  if hj : j<32 then TangentialResponseData.steps ⟨j,hj⟩ i else TangentialResponseData.step0 i

theorem coefficient_errors (r : Reference) (i : Fin 3) (j : ℕ) (hj : j<32)
    (u : ℝ) (hu : u ∈ Icc (0:ℝ) (13/640)) :
    (∀ k l, |phaseOperator r ((j:ℝ)*(13/640)+u) k l-
      value ((sequence i j).operator k l) u|≤((sequence i j).operatorError:ℝ)) ∧
    (∀ k, |phaseInput r i ((j:ℝ)*(13/640)+u) k-
      value ((sequence i j).input k) u|≤((sequence i j).inputError:ℝ)) := by
  have hg := TangentialReference.gradient_pieces r.w r.continuous r.positive r.derivative r.initial j hj u hu
  have hf := TangentialReference.frameInput_pieces r.w r.continuous r.positive r.derivative r.initial j hj u hu
  have hg0 : (0:ℝ)≤(TangentialReference.gradientBudget:ℝ) := by
    norm_num [TangentialReference.gradientBudget,TangentialReferenceData.errorBound]
  have hf0 : (0:ℝ)≤(TangentialReference.thrustBudget:ℝ) := by
    norm_num [TangentialReference.thrustBudget,TangentialReferenceData.errorBound,TangentialReferenceData.alpha]
  simp only [sequence,dif_pos hj,TangentialResponseData.operators,TangentialResponseData.inputs,
    TangentialResponseData.operatorErrors,TangentialResponseData.inputErrors]
  simp only [TangentialReference.observable,TangentialReference.sequence,dif_pos hj] at hg hf
  constructor
  · intro k l
    fin_cases k <;> fin_cases l <;>
      simp only [phaseOperator,TangentialResponseData.operator,Matrix.cons_val_succ,Matrix.cons_val_zero]
    all_goals first
      | simpa only [value] using hg 0 0
      | simpa only [value] using hg 0 1
      | simpa only [value] using hg 0 2
      | simpa only [value] using hg 1 0
      | simpa only [value] using hg 1 1
      | simpa only [value] using hg 1 2
      | simpa only [value] using hg 2 0
      | simpa only [value] using hg 2 1
      | simpa only [value] using hg 2 2
      | simpa [value,Planning.PolynomialKernel.evaluate] using hg0
  · intro k
    fin_cases k <;>
      simp only [phaseInput,TangentialResponseData.input,Matrix.cons_val_succ,Matrix.cons_val_zero]
    all_goals first
      | simpa only [value] using hf 0 i
      | simpa only [value] using hf 1 i
      | simpa only [value] using hf 2 i
      | simpa [value,Planning.PolynomialKernel.evaluate] using hf0

theorem response_pieces (r : Reference) (i : Fin 3) (S : PhaseResponse r i)
    (j : ℕ) (hj : j<32) (u : ℝ) (hu : u ∈ Icc (0:ℝ) (13/640)) :
    ‖packed (S.p ((j:ℝ)*(13/640)+u)) (S.v ((j:ℝ)*(13/640)+u))-
      curve (sequence i j).coefficients u‖<(TangentialResponseData.errorBound:ℝ) := by
  have hdur (k : ℕ) (hk : k<32) : (sequence i k).duration=13/640 := by
    simp [sequence,hk,TangentialResponseData.durations,TangentialReferenceData.stepLength]
  have hv (k : ℕ) (hk : k<32) : (sequence i k).Valid := by
    simpa [sequence,hk] using TangentialResponseData.valid ⟨k,hk⟩ i
  have hjoin (k : ℕ) (hk : k+1<32) :
      AffinePolynomialStep.Compatible (sequence i k) (sequence i (k+1)) := by
    have hk' : k<32 := by omega
    simpa [sequence,hk,hk'] using TangentialResponseData.joins ⟨k,by omega⟩ i
  have hi : ‖packed (S.p 0) (S.v 0)-curve (sequence i 0).coefficients 0‖≤
      ((sequence i 0).initialError:ℝ) := by
    have he : curve (sequence i 0).coefficients 0=0 := by
      ext k
      change PolynomialOrder.value _ 0=0
      rw [show (0:ℝ)=((0:ℚ):ℝ) by norm_num,PolynomialOrder.value_at_rational]
      simp [sequence,TangentialResponseData.initial_values]
    rw [S.initial_p,S.initial_v,he]
    have hz : packed 0 0=0 := by ext k; fin_cases k <;> simp [packed,Matrix.cons_val_succ]
    rw [hz,sub_self,norm_zero]
    exact_mod_cast (hv 0 (by norm_num)).2.1
  have h := AffinePolynomialStep.chain_sound (sequence i) 32 (h := 13/640)
    (by norm_num) hv hdur hjoin (phaseOperator r) (phaseInput r i)
    (fun t => packed (S.p t) (S.v t)) (packed_continuous r i S)
    (by intro t ht; apply packed_derivative r i S; norm_num at ht; exact ht)
    (fun k hk t ht => by simpa using (coefficient_errors r i k hk t (by simpa using ht)).1)
    (fun k hk t ht => by simpa using (coefficient_errors r i k hk t (by simpa using ht)).2)
    hi j hj u (by simpa using hu)
  have he : (sequence i j).error≤TangentialResponseData.errorBound := by
    simp only [sequence,dif_pos hj]
    exact TangentialResponseData.errors ⟨j,hj⟩ i
  apply lt_of_lt_of_le (by simpa using h)
  exact_mod_cast he

end GNC.OrbitalComparison.TangentialFiniteResponse
