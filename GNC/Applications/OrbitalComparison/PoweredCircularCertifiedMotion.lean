import GNC.Applications.OrbitalComparison.PoweredCircularExistence
import GNC.Applications.OrbitalComparison.FiniteBatchEvaluation

/-! A complete physical-IVP-to-prediction certificate for the powered burn.

No actual trajectory, exact linear response, log lift or numerical residual
is supplied. Existence and uniqueness of the physical trajectory are proved,
and the finite polynomial predictor and rounded evaluator are certified
against it. The conclusion is scoped to this prescribed-thrust model, not
to arbitrary spacecraft or to an IEEE implementation.
-/
noncomputable section
namespace GNC.OrbitalComparison.PoweredCircularCertifiedMotion
open Set
open PoweredCircularLogTube
open PoweredCircularExistence
open FiniteEvaluation (angle embed)

/-- Whole-interval physical certificate, uniform over the complete 3D
attitude ball. The existential witness solves nonlinear gravity; the
accuracy conclusion is about the explicit finite predictor. -/
theorem certified_motion (φ : Vec3) (hφ : enorm φ≤angleRadius) :
    ∃ X : Motion φ,
      (∀ t ∈ Icc (0:ℝ) 1, orbitRadius≤‖X.p t‖ ∧
        lengthScale*‖X.p t-FiniteCircularCertificate.prediction φ t‖<1/1000) ∧
      (∀ Y : Motion φ, ∀ t ∈ Icc (0:ℝ) 1, Y.p t=X.p t ∧ Y.v t=X.v t) := by
  let X := trajectory φ hφ
  refine ⟨X,?_,unique φ hφ⟩
  have hc := FiniteCircularCertificate.submillimeter φ hφ X.p X.v
    X.continuous_p X.continuous_v X.derivative_p X.derivative_v X.initial_p X.initial_v
  exact fun t ht => ⟨trajectory_radius φ hφ ht,hc t ht⟩

/-- A reachable set in physical position units. Its center is the certified
finite predictor; its radius includes the reconstruction truncation error. -/
def positionTube (t : ℝ) : Set GeometricSTMPrediction.E :=
  {p | ∃ φ : Vec3, enorm φ≤angleRadius ∧
    ‖p-lengthScale • FiniteCircularCertificate.prediction φ t‖<1/1000}

/-- Every actual position belongs to the explicitly defined tube, at every
time, without discretizing either the time interval or attitude ball. -/
theorem reachable_containment (φ : Vec3) (hφ : enorm φ≤angleRadius)
    (X : Motion φ) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    lengthScale • X.p t ∈ positionTube t := by
  refine ⟨φ,hφ,?_⟩
  rw [←smul_sub, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by norm_num [lengthScale] : 0≤lengthScale)]
  exact FiniteCircularCertificate.submillimeter φ hφ X.p X.v
    X.continuous_p X.continuous_v X.derivative_p X.derivative_v X.initial_p X.initial_v t ht

/-- End-to-end certificate for the specified dyadic evaluator: its returned
SI positions are compared to a proved-existing nonlinear orbit. Every
admissible rational query is covered, including after shared preparation.
These are 0.913 mm and 0.313 mm bounds, not fitted numerical tolerances. -/
theorem certified_evaluation (φ : Fin 3 → ℚ)
    (hφ : enorm (angle φ)≤angleRadius) :
    ∃ X : Motion (angle φ),
      (∀ Y : Motion (angle φ), ∀ t ∈ Icc (0:ℝ) 1, Y.p t=X.p t ∧ Y.v t=X.v t) ∧
      ∀ t : ℚ, (t:ℝ)∈Icc (0:ℝ) 1 →
        ‖lengthScale • X.p (t:ℝ)-embed
          (FiniteBatchEvaluation.physicalPrediction
            FiniteBatchData.geometricQuery FiniteBatchData.geometricOutputs
            (FiniteBatchEvaluation.prepare FiniteBatchData.geometricPrepare t) φ)‖<913/1000000 ∧
        ‖lengthScale • X.p (t:ℝ)-embed
          (FiniteBatchEvaluation.physicalPrediction
            FiniteBatchData.cartesianQuery FiniteBatchData.cartesianOutputs
            (FiniteBatchEvaluation.prepare FiniteBatchData.cartesianPrepare t) φ)‖<313/1000000 := by
  let X := trajectory (angle φ) hφ
  exact ⟨X,unique (angle φ) hφ,FiniteBatchEvaluation.certificates φ hφ X.p X.v
    X.continuous_p X.continuous_v X.derivative_p X.derivative_v X.initial_p X.initial_v⟩

end GNC.OrbitalComparison.PoweredCircularCertifiedMotion
