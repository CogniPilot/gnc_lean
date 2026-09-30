import GNC.Applications.OrbitalComparison.TangentialFiniteResponse

/-! Full nonlinear deputy to a finite polynomial response prediction.
The polynomial is evaluated over the reals here. Floating-point and
transcendental evaluation errors are separate obligations. -/
noncomputable section
namespace GNC.OrbitalComparison.TangentialFiniteResponse
open Set TangentialReferenceMotion TangentialMountingMotion TangentialResponseCertificate
open PolynomialODE
open ThrustSupport (euclideanEquiv)

def normalizedResponse (r : Reference) (i : Fin 3) (S : PhaseResponse r i) :
    GravityLinearResponse.Response mu 1 r.q (columnForce r i) where
  p := fun t => S.p (horizon*t)
  v := fun t => horizon • S.v (horizon*t)
  continuous_p := S.continuous_p.comp (continuous_const.mul continuous_id)
  continuous_v := (S.continuous_v.comp (continuous_const.mul continuous_id)).const_smul _
  initial_p := by simp [S.initial_p]
  initial_v := by simp [S.initial_v]
  derivative_p := fun t ht => by
    have ht1 : horizon*t ∈ Icc (0:ℝ) 1 :=
      ⟨(time_mem ht).1,(time_mem ht).2.trans (by norm_num)⟩
    simpa using (S.derivative_p _ ht1).scomp t ((hasDerivAt_id t).const_mul horizon)
  derivative_v := fun t ht => by
    have ht1 : horizon*t ∈ Icc (0:ℝ) 1 :=
      ⟨(time_mem ht).1,(time_mem ht).2.trans (by norm_num)⟩
    have hd := ((S.derivative_v _ ht1).scomp t
      ((hasDerivAt_id t).const_mul horizon)).const_smul horizon
    have hg : Gravity.gradient mu (r.q t) (S.p (horizon*t))=
        horizon^2 • Gravity.gradient 1 (phasePosition r (horizon*t)) (S.p (horizon*t)) := by
      simp only [mu,Reference.q,phasePosition,Gravity.gradient,smul_sub,smul_smul]
      module
    convert hd using 1
    rw [one_smul,hg]
    simp only [one_smul,phaseForce,columnForce,Reference.frame,acceleration,smul_add,smul_smul]
    module

def polynomialColumn (i : Fin 3) (j : ℕ) (u : ℝ) : E :=
  euclideanEquiv ![curve (sequence i j).coefficients u 0,
    curve (sequence i j).coefficients u 1,curve (sequence i j).coefficients u 2]

theorem column_error (r : Reference) (i : Fin 3) (S : PhaseResponse r i)
    (j : ℕ) (hj : j<32) (u : ℝ) (hu : u ∈ Icc (0:ℝ) (13/640)) :
    ‖S.p ((j:ℝ)*(13/640)+u)-polynomialColumn i j u‖≤
      2*(TangentialResponseData.errorBound:ℝ) := by
  have h := (response_pieces r i S j hj u hu).le
  let d : Vec3 := euclideanEquiv.symm (S.p ((j:ℝ)*(13/640)+u))-
    ![curve (sequence i j).coefficients u 0,
      curve (sequence i j).coefficients u 1,curve (sequence i j).coefficients u 2]
  change enorm d≤2*(TangentialResponseData.errorBound:ℝ)
  apply (enorm_le_two_pi_norm d).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply (pi_norm_le_iff_of_nonneg
    (by norm_num [TangentialResponseData.errorBound] : (0:ℝ)≤TangentialResponseData.errorBound)).mpr
  intro k
  fin_cases k
  all_goals first
    | simpa [d,packed,Matrix.cons_val_succ] using
        (norm_le_pi_norm (_-curve (sequence i j).coefficients u) 0).trans h
    | simpa [d,packed,Matrix.cons_val_succ] using
        (norm_le_pi_norm (_-curve (sequence i j).coefficients u) 1).trans h
    | simpa [d,packed,Matrix.cons_val_succ] using
        (norm_le_pi_norm (_-curve (sequence i j).coefficients u) 2).trans h

def finitePosition (φ : Vec3) (j : ℕ) (u : ℝ) : E :=
  polynomialPosition j u+∑ i : Fin 3, direction φ i • polynomialColumn i j u
def totalPositionError (t : ℝ) : ℝ := positionError t+
  2*(TangentialReferenceData.errorBound:ℝ)+6*angleRadius*(TangentialResponseData.errorBound:ℝ)

theorem reported_total_error : (7000000:ℝ)*totalPositionError 1<3/1000000000 := by
  have h := reported_error
  have hb : (7000000:ℝ)*(2*(TangentialReferenceData.errorBound:ℝ)+
      6*angleRadius*(TangentialResponseData.errorBound:ℝ))<2/1000000000 := by
    norm_num [angleRadius,TangentialReferenceData.errorBound,TangentialResponseData.errorBound]
  unfold totalPositionError
  linarith

/-- The complete finite predictor, with numerical reference and response
errors, encloses every physical motion in the prescribed mounting ball. -/
theorem finite_prediction (r : Reference) (φ : Vec3) (hφ : enorm φ≤angleRadius)
    (X : Motion r φ) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ∃ j : ℕ, j<32 ∧ ∃ u ∈ Icc (0:ℝ) (13/640),
      horizon*t=(j:ℝ)*(13/640)+u ∧
        ‖X.p t-finitePosition φ j u‖≤totalPositionError t ∧
        (7000000:ℝ)*‖X.p t-finitePosition φ j u‖<3/1000000000 := by
  let S : ∀ i : Fin 3, PhaseResponse r i := fun i => Classical.choice (exists_response r i)
  let C : Columns r := fun i => normalizedResponse r i (S i)
  obtain ⟨j,hj,u,hu,htj,hq⟩ := reference_approximation r ht
  have hp := (prediction r φ hφ X (from_columns r C φ) t ht).1
  have hw : enorm (direction φ)≤angleRadius := by
    have h := RotationCenteredError.rotation_difference_bound φ PlanarReferenceMotion.tangent
      (hφ.trans_lt (by norm_num [angleRadius]; linarith [Real.pi_gt_three]))
    simpa [direction,PlanarReferenceMotion.tangent_norm] using h.trans
      (by simpa [PlanarReferenceMotion.tangent_norm] using hφ)
  have hc : ‖(from_columns r C φ).p t-
      ∑ i : Fin 3, direction φ i • polynomialColumn i j u‖≤
        6*angleRadius*(TangentialResponseData.errorBound:ℝ) := by
    rw [from_columns_position,←Finset.sum_sub_distrib]
    have hb (i : Fin 3) : ‖direction φ i • (C i).p t-
        direction φ i • polynomialColumn i j u‖≤
        angleRadius*(2*(TangentialResponseData.errorBound:ℝ)) := by
      rw [←smul_sub,norm_smul,Real.norm_eq_abs]
      apply mul_le_mul ((component_le_enorm _ i).trans hw) _ (norm_nonneg _)
        (by norm_num [angleRadius])
      change ‖(S i).p (horizon*t)-polynomialColumn i j u‖≤_
      rw [htj]
      exact column_error r i (S i) j hj u hu
    exact (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun i _ => hb i)).trans_eq (by simp; ring))
  have he : X.p t-finitePosition φ j u=
      (X.p t-(r.q t+(from_columns r C φ).p t))+(r.q t-polynomialPosition j u)+
      ((from_columns r C φ).p t-∑ i : Fin 3, direction φ i • polynomialColumn i j u) := by
    unfold finitePosition
    abel
  have hb : ‖X.p t-finitePosition φ j u‖≤totalPositionError t := by
    rw [he]
    have hab : ‖(X.p t-(r.q t+(from_columns r C φ).p t))+
        (r.q t-polynomialPosition j u)‖≤
        positionError t+2*(TangentialReferenceData.errorBound:ℝ) :=
      (norm_add_le _ _).trans (add_le_add hp hq)
    exact (norm_add_le _ _).trans (add_le_add hab hc)
  refine ⟨j,hj,u,hu,htj,hb,?_⟩
  have hend : totalPositionError t≤totalPositionError 1 := by
    unfold totalPositionError
    linarith [TangentialResponseCertificate.position_le_endpoint ht]
  exact (mul_le_mul_of_nonneg_left (hb.trans hend) (by norm_num)).trans_lt reported_total_error

/-- A physical witness for every mounting error, with a fully finite
reference/response predictor. No exact response or numerical ephemeris is
a hypothesis of this statement. -/
theorem exists_certified_burn :
    ∃ r : Reference, ∀ φ : Vec3, enorm φ≤angleRadius →
      ∃ X : Motion r φ,
        (∀ t ∈ Icc (0:ℝ) 1, orbitRadius≤‖X.p t‖) ∧
        ∀ t ∈ Icc (0:ℝ) 1, ∃ j : ℕ, j<32 ∧ ∃ u ∈ Icc (0:ℝ) (13/640),
          horizon*t=(j:ℝ)*(13/640)+u ∧
            ‖X.p t-finitePosition φ j u‖≤totalPositionError t ∧
            (7000000:ℝ)*‖X.p t-finitePosition φ j u‖<3/1000000000 := by
  obtain ⟨r⟩ := exists_reference
  refine ⟨r,fun φ hφ => ⟨trajectory r φ hφ,fun _ ht => trajectory_radius r φ hφ ht,?_⟩⟩
  exact fun t ht => finite_prediction r φ hφ _ ht

end GNC.OrbitalComparison.TangentialFiniteResponse
