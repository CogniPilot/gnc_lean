import GNC.Applications.OrbitalComparison.TangentialMountingMotion
import GNC.Analysis.EuclideanBox

/-! Reachability about the computed noncircular reference, with its numerical
error included. The exact polynomial center is not assumed to be the true
reference. This is a common coarse tube, not a predictor-error comparison.
-/
noncomputable section
namespace GNC.OrbitalComparison.TangentialMountingMotion
open Set TangentialReferenceMotion TangentialReferenceData PolynomialODE PolynomialOrbit
open PolynomialOrbitTransition
open ThrustSupport (euclideanEquiv)

def polynomialPosition (j : ℕ) (u : ℝ) : E :=
  euclideanEquiv ![curve (TangentialReference.sequence j).coefficients u 0,
    curve (TangentialReference.sequence j).coefficients u 1,0]

theorem reference_approximation (r : Reference) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ∃ j : ℕ, j<32 ∧ ∃ u ∈ Icc (0:ℝ) (13/640),
      horizon*t=(j:ℝ)*(13/640)+u ∧
        ‖r.q t-polynomialPosition j u‖≤2*(errorBound:ℝ) := by
  obtain ⟨j,hj,u,hu,htj,he⟩ := TangentialReference.physical_enclosure r.w
    r.continuous r.positive r.derivative r.initial _ (time_mem ht)
  refine ⟨j,hj,u,hu,htj,?_⟩
  let d : Vec3 := position (r.w (horizon*t))-
    ![curve (TangentialReference.sequence j).coefficients u 0,
      curve (TangentialReference.sequence j).coefficients u 1,0]
  change enorm d≤2*(errorBound:ℝ)
  apply (enorm_le_two_pi_norm d).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply (pi_norm_le_iff_of_nonneg (by norm_num [errorBound] : (0:ℝ)≤errorBound)).mpr
  intro i
  fin_cases i
  · simpa [d,position,lift] using (norm_le_pi_norm
      (lift (r.w (horizon*t))-curve (TangentialReference.sequence j).coefficients u) 0).trans he.le
  · simpa [d,position,lift] using (norm_le_pi_norm
      (lift (r.w (horizon*t))-curve (TangentialReference.sequence j).coefficients u) 1).trans he.le
  · norm_num [d,position,Matrix.cons_val_two,errorBound]

theorem position_formula (t : ℝ) :
    positionBound t=angleRadius*acceleration*(t^2/2+t^4/24+t^6/720+t^8/39600) := by
  norm_num [positionBound,MonomialSupersolution.value,MonomialSupersolution.polynomial,
    MonomialSupersolution.pair,MonomialSupersolution.four,MonomialSupersolution.six]
  ring_nf <;> simp

theorem position_le_endpoint {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    positionBound t≤positionBound 1 :=
  mul_le_mul_of_nonneg_left
    (MonomialSupersolution.value_le_endpoint 0 (by norm_num) (by norm_num) ht)
    (by norm_num [angleRadius,acceleration,horizon,alpha])

/-- The displayed 0.395 m is an outward report of a derived formula,
including reference error, not an allowance inserted in a proof. -/
theorem reported_radius :
    (7000000:ℝ)*(positionBound 1+2*(errorBound:ℝ))<395/1000 := by
  rw [position_formula]
  norm_num [angleRadius,acceleration,horizon,alpha,errorBound]

/-- Continuous-time enclosure about the *computed* piecewise polynomial.
Every initial mounting angle in the three-dimensional ball is covered. -/
theorem computed_reference_tube (r : Reference) (φ : Vec3) (hφ : enorm φ≤angleRadius)
    (X : Motion r φ) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ∃ j : ℕ, j<32 ∧ ∃ u ∈ Icc (0:ℝ) (13/640),
      horizon*t=(j:ℝ)*(13/640)+u ∧
        ‖X.p t-polynomialPosition j u‖≤positionBound t+2*(errorBound:ℝ) ∧
        (7000000:ℝ)*‖X.p t-polynomialPosition j u‖<395/1000 := by
  obtain ⟨j,hj,u,hu,htj,hq⟩ := reference_approximation r ht
  have htriangle : ‖X.p t-polynomialPosition j u‖≤
      ‖X.p t-r.q t‖+‖r.q t-polynomialPosition j u‖ := by
    simpa only [sub_add_sub_cancel] using
      norm_add_le (X.p t-r.q t) (r.q t-polynomialPosition j u)
  have h := htriangle.trans
    (add_le_add (reference_tube r φ hφ X t ht).1 hq)
  refine ⟨j,hj,u,hu,htj,h,?_⟩
  exact (mul_le_mul_of_nonneg_left
    (h.trans (add_le_add (position_le_endpoint ht) le_rfl)) (by norm_num)).trans_lt reported_radius

/-- The certificate has an actual physical witness for each angle, rather
than a premise asserting the existence of the uncertain deputy. -/
theorem exists_certified_motion (r : Reference) (φ : Vec3) (hφ : enorm φ≤angleRadius) :
    ∃ X : Motion r φ,
      (∀ t ∈ Icc (0:ℝ) 1, orbitRadius≤‖X.p t‖) ∧
      ∀ t ∈ Icc (0:ℝ) 1, ∃ j : ℕ, j<32 ∧ ∃ u ∈ Icc (0:ℝ) (13/640),
        horizon*t=(j:ℝ)*(13/640)+u ∧
          ‖X.p t-polynomialPosition j u‖≤positionBound t+2*(errorBound:ℝ) ∧
          (7000000:ℝ)*‖X.p t-polynomialPosition j u‖<395/1000 := by
  refine ⟨trajectory r φ hφ,fun _ ht => trajectory_radius r φ hφ ht,?_⟩
  exact fun _ ht => computed_reference_tube r φ hφ _ ht

end GNC.OrbitalComparison.TangentialMountingMotion
