import GNC.Applications.OrbitalComparison.TangentialSharedInput

/-! Matched geometric and exact-component certificates on the same
noncircular physical mission and the same 3D initial-attitude ball.
The Cartesian comparator receives the identical gravity envelope. Both
use ideal continuous responses; finite evaluation is not certified here.
-/
noncomputable section
namespace GNC.OrbitalComparison.TangentialSharedComparison
open Set TangentialReferenceMotion TangentialSharedInput
open TangentialMountingMotion (angleRadius orbitRadius)
open TangentialResponseCertificate (responseRadius gravityBudget)
open LieRadiusFrame (left)

def forcing (r : Reference) (φ : Vec3) (t : ℝ) : E :=
  TangentialSharedInput.thrust r φ t-r.thrust t

abbrev ComponentResponse (r : Reference) (φ : Vec3) :=
  GravityLinearResponse.Response TangentialReferenceMotion.mu 1 r.q (forcing r φ)

theorem exists_response (r : Reference) (φ : Vec3) : Nonempty (ComponentResponse r φ) := by
  apply GravityLinearResponse.Response.exists TangentialReferenceMotion.mu 1 (q_continuous r) _
    ((TangentialSharedInput.thrust_continuous r φ).sub
      (TangentialReferenceMotion.thrust_continuous r))
  intro t
  apply norm_ne_zero_iff.mp
  change enorm (PolynomialOrbitTransition.position (r.w (horizon*t)))≠0
  rw [PolynomialOrbitTransition.position_norm]
  exact (r.positive _).ne'

theorem prediction (r : Reference) (φ : Vec3) (hφ : enorm φ≤angleRadius)
    (X : Motion r φ) (S : ComponentResponse r φ) :
    ∀ t ∈ Icc (0:ℝ) 1,
      ‖X.p t-(r.q t+S.p t)‖≤TangentialResponseCertificate.positionError t ∧
      ‖X.v t-(r.v t+S.v t)‖≤TangentialResponseCertificate.velocityError t := by
  have hc := TangentialResponseCertificate.checks
  have hs := Gravity.retained_response_shape TangentialReferenceMotion.mu lowerRadius (angleRadius*acceleration)
    hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1 r.q S.p S.v (forcing r φ)
    (fun _ ht => q_radius r ht) (fun t _ => input_difference r φ hφ t)
    S.continuous_p S.continuous_v S.derivative_p
    (by simpa only [one_smul] using S.derivative_v) S.initial_p S.initial_v
  have h := Gravity.retained_monomial_prediction TangentialReferenceMotion.mu lowerRadius responseRadius 0 1
    hc.1 hc.2.2.2.2.1 hc.2.2.2.2.2.1 (by norm_num)
    (by norm_num) (by norm_num) hc.2.2.2.2.2.2.1
    (by simpa [gravityBudget] using hc.2.2.2.2.2.2.2)
    X.p X.v r.q r.v S.p S.v r.thrust (forcing r φ) (forcing r φ)
    (fun _ ht => q_radius r ht) hs (by intros; simp)
    X.continuous_p X.continuous_v (q_continuous r) (v_continuous r)
    S.continuous_p S.continuous_v X.derivative_p
    (by simpa [forcing] using X.derivative_v)
    (fun _ ht => q_derivative r ht) (fun _ ht => v_derivative r ht)
    S.derivative_p (by simpa only [one_smul] using S.derivative_v)
    (by simpa [S.initial_p] using X.initial_p)
    (by simpa [S.initial_v] using X.initial_v)
  simpa [TangentialResponseCertificate.positionError,TangentialResponseCertificate.velocityError,gravityBudget] using h

/-- Both predictors meet 1 mm for the very same physical trajectories.
The stronger Cartesian bound is reported, rather than hidden by the target.
This is an accuracy theorem, not an end-to-end computational cost theorem. -/
theorem exists_matched_predictions :
    ∃ r : Reference, ∀ φ : Vec3, enorm φ≤angleRadius →
      ∃ X : Motion r φ, ∃ G : Response r φ, ∃ C : ComponentResponse r φ,
        (∀ t ∈ Icc (0:ℝ) 1, orbitRadius≤‖X.p t‖) ∧
        ∀ t ∈ Icc (0:ℝ) 1,
          (7000000:ℝ)*‖X.p t-(r.q t+left φ (G.p t))‖<568/1000000 ∧
          (7000000:ℝ)*‖X.p t-(r.q t+C.p t)‖<1/1000000000 := by
  obtain ⟨r⟩ := exists_reference
  refine ⟨r,fun φ hφ => ?_⟩
  obtain ⟨X,hX⟩ := TangentialSharedInput.exists_motion r φ hφ
  obtain ⟨G⟩ := TangentialSharedInput.exists_response r φ
  obtain ⟨C⟩ := exists_response r φ
  refine ⟨X,G,C,hX,?_⟩
  intro t ht
  constructor
  · exact (mul_le_mul_of_nonneg_left
      ((TangentialSharedInput.prediction r φ hφ X G t ht).1.trans
        (TangentialSharedInput.position_le_endpoint ht)) (by norm_num)).trans_lt
      TangentialSharedInput.reported_error
  · exact (mul_le_mul_of_nonneg_left
      ((prediction r φ hφ X C t ht).1.trans
        (TangentialResponseCertificate.position_le_endpoint ht)) (by norm_num)).trans_lt
      TangentialResponseCertificate.reported_error

end GNC.OrbitalComparison.TangentialSharedComparison
