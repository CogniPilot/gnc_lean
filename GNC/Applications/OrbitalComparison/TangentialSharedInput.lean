import GNC.Applications.OrbitalComparison.TangentialResponseCertificate
import GNC.Applications.OrbitalComparison.GeometricSTMPrediction

/-! The noncircular EP reference with a fixed inertial attitude offset.
This is the shared-body-input family R=Exp(phi) Rbar, distinct from the
body mounting family R=Rbar Exp(phi). The geometric response retains the
time-varying reference gravity gradient. Existence and its physical error
bound are proved, not inferred from a numerical comparison.

These are ideal continuous response bounds. They do not certify the
separate Python response solver, floating evaluation, or its work counts.
-/
noncomputable section
namespace GNC.OrbitalComparison.TangentialSharedInput
open Set TangentialReferenceMotion TangentialReferenceData
open TangentialMountingMotion (angleRadius orbitRadius extensionRadius innerRadius region_checks)
open TangentialResponseCertificate (responseRadius)
open GeometricSTMPrediction (force cross)
open LieRadiusFrame (left)

def thrust (r : Reference) (φ : Vec3) (t : ℝ) : E := force φ (r.thrust t)

theorem thrust_continuous (r : Reference) (φ : Vec3) : Continuous (thrust r φ) :=
  (rotationIsometry (rotationExp φ)).continuous.comp (TangentialReferenceMotion.thrust_continuous r)

theorem input_difference (r : Reference) (φ : Vec3) (hφ : enorm φ≤angleRadius) (t : ℝ) :
    ‖thrust r φ t-r.thrust t‖≤angleRadius*acceleration := by
  have h := RotationCenteredError.rotation_difference_bound φ (r.thrust t).ofLp
    (hφ.trans_lt (by norm_num [angleRadius]; linarith [Real.pi_gt_three]))
  change ‖thrust r φ t-r.thrust t‖≤enorm φ*‖r.thrust t‖ at h
  rw [TangentialReferenceMotion.thrust_norm] at h
  exact h.trans (mul_le_mul_of_nonneg_right hφ (by norm_num [acceleration,horizon,alpha]))

structure Motion (r : Reference) (φ : Vec3) where
  p : ℝ → E
  v : ℝ → E
  continuous_p : Continuous p
  continuous_v : Continuous v
  initial_p : p 0=r.q 0
  initial_v : v 0=r.v 0
  derivative_p : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt p (v t) t
  derivative_v : ∀ t ∈ Icc (0:ℝ) 1,
    HasDerivAt v (Gravity.field TangentialReferenceMotion.mu (p t)+thrust r φ t) t

theorem exists_motion (r : Reference) (φ : Vec3) (hφ : enorm φ≤angleRadius) :
    ∃ X : Motion r φ, ∀ t ∈ Icc (0:ℝ) 1, orbitRadius≤‖X.p t‖ := by
  obtain ⟨p,v,hp,hv,hp0,hv0,hdp,hdv,hr⟩ := Gravity.exists_near_candidate
    (μ := TangentialReferenceMotion.mu) (scale := 1) (r := orbitRadius) (R := extensionRadius)
    (by norm_num [TangentialReferenceMotion.mu,horizon]) (by norm_num) region_checks.2.2.1 region_checks.2.1.le
    (by simpa using region_checks.2.2.2.2.2.2.1)
    r.q r.v (fun t => Gravity.field TangentialReferenceMotion.mu (r.q t)+r.thrust t) (thrust r φ)
    (q_continuous r) (v_continuous r) (TangentialMountingMotion.acceleration_continuous r)
    (thrust_continuous r φ)
    (fun _ ht => q_derivative r ht) (fun _ ht => v_derivative r ht)
    (fun t ht => by rw [region_checks.2.2.2.2.1]; exact q_radius r ht)
    (D := angleRadius*acceleration) (by norm_num [angleRadius,acceleration,horizon,alpha])
    (fun t _ => by simpa only [one_smul,add_sub_add_left_eq_sub] using input_difference r φ hφ t)
    region_checks.2.2.2.2.2.2.2.1
  exact ⟨⟨p,v,hp,hv,hp0,hv0,hdp,by simpa only [one_smul] using hdv⟩,hr⟩

def crossMap (φ : Vec3) : E →ₗ[ℝ] E :=
  ThrustSupport.euclideanEquiv.toLinearMap.comp
    ((crossProduct φ).comp ThrustSupport.euclideanEquiv.symm.toLinearMap)

abbrev Response (r : Reference) (φ : Vec3) :=
  GravityLinearResponse.Response TangentialReferenceMotion.mu 1 r.q (fun t => cross φ (r.thrust t))

theorem exists_response (r : Reference) (φ : Vec3) : Nonempty (Response r φ) := by
  apply GravityLinearResponse.Response.exists TangentialReferenceMotion.mu 1 (q_continuous r) _
    ((crossMap φ).continuous_of_finiteDimensional.comp (TangentialReferenceMotion.thrust_continuous r))
  intro t
  apply norm_ne_zero_iff.mp
  change enorm (PolynomialOrbitTransition.position (r.w (horizon*t)))≠0
  rw [PolynomialOrbitTransition.position_norm]
  exact (r.positive _).ne'

def gradientBudget : ℝ := 2*TangentialReferenceMotion.mu/(lowerRadius:ℝ)^3*angleRadius*responseRadius
def curvatureBudget : ℝ := 4*TangentialReferenceMotion.mu/((lowerRadius:ℝ)-responseRadius)^4*responseRadius^2
def positionError (t : ℝ) : ℝ := gradientBudget*MonomialSupersolution.value 1 2 t+
  curvatureBudget*MonomialSupersolution.value 1 4 t
def velocityError (t : ℝ) : ℝ := gradientBudget*MonomialSupersolution.velocity 1 2 t+
  curvatureBudget*MonomialSupersolution.velocity 1 4 t

theorem closure :
    (gradientBudget+curvatureBudget)*PolynomialSupersolution.value 1 1<responseRadius := by
  norm_num [gradientBudget,curvatureBudget,responseRadius,TangentialReferenceMotion.mu,horizon,lowerRadius,inverseBound,
    angleRadius,acceleration,alpha,PolynomialSupersolution.value,PolynomialSupersolution.polynomial]

theorem prediction (r : Reference) (φ : Vec3) (hφ : enorm φ≤angleRadius)
    (X : Motion r φ) (S : Response r φ) :
    ∀ t ∈ Icc (0:ℝ) 1,
      ‖X.p t-(r.q t+left φ (S.p t))‖≤positionError t ∧
      ‖X.v t-(r.v t+left φ (S.v t))‖≤velocityError t := by
  have hc := TangentialResponseCertificate.checks
  have hs := GeometricSTMPrediction.response_shape TangentialReferenceMotion.mu lowerRadius angleRadius acceleration
    hc.1 hc.2.1 (by norm_num [angleRadius]) (by norm_num [acceleration,horizon,alpha])
    hc.2.2.2.1 φ hφ r.q S.p S.v r.thrust (fun _ ht => q_radius r ht)
    (fun t _ => (TangentialReferenceMotion.thrust_norm r t).le)
    S.continuous_p S.continuous_v S.derivative_p
    (by simpa only [one_smul] using S.derivative_v) S.initial_p S.initial_v
  have h := GeometricSTMPrediction.certificate TangentialReferenceMotion.mu lowerRadius responseRadius angleRadius 1
    hc.1 hc.2.1 hc.2.2.2.2.1 hc.2.2.2.2.2.1
    (by norm_num [angleRadius]) (by norm_num [angleRadius]) (by norm_num) (by norm_num)
    hc.2.2.2.2.2.2.1 (by simpa [gradientBudget,curvatureBudget] using closure)
    φ hφ X.p X.v r.q r.v S.p S.v r.thrust
    (fun _ ht => q_radius r ht) hs
    X.continuous_p X.continuous_v (q_continuous r) (v_continuous r)
    S.continuous_p S.continuous_v X.derivative_p X.derivative_v
    (fun _ ht => q_derivative r ht) (fun _ ht => v_derivative r ht)
    S.derivative_p (by simpa only [one_smul] using S.derivative_v)
    (by simp [S.initial_p,X.initial_p]) (by simp [S.initial_v,X.initial_v])
  simpa only [positionError,velocityError,gradientBudget,curvatureBudget] using h

theorem position_le_endpoint {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    positionError t≤positionError 1 := by
  have hμ : 0≤TangentialReferenceMotion.mu := by norm_num [TangentialReferenceMotion.mu,horizon]
  have hL := TangentialResponseCertificate.checks.2.2.2.2.1
  have hr := TangentialResponseCertificate.checks.2.1
  exact add_le_add
    (mul_le_mul_of_nonneg_left
      (MonomialSupersolution.value_le_endpoint 2 (by norm_num) (by norm_num) ht)
      (by unfold gradientBudget angleRadius; positivity))
    (mul_le_mul_of_nonneg_left
      (MonomialSupersolution.value_le_endpoint 4 (by norm_num) (by norm_num) ht)
      (by unfold curvatureBudget; positivity))

/-- Outward reporting of the analytic budget, not an imposed allowance. -/
theorem reported_error : (7000000:ℝ)*positionError 1<568/1000000 := by
  norm_num [positionError,gradientBudget,curvatureBudget,responseRadius,TangentialReferenceMotion.mu,horizon,lowerRadius,inverseBound,
    angleRadius,acceleration,alpha,PolynomialSupersolution.value,PolynomialSupersolution.polynomial,
    MonomialSupersolution.value,MonomialSupersolution.polynomial,MonomialSupersolution.pair,
    MonomialSupersolution.four,MonomialSupersolution.six]

/-- A known noncircular reference, a physical noncolliding deputy, and the
geometric variational response all exist, uniformly over the 3D angle ball.
The response is ideal: numerical response error must still be charged. -/
theorem exists_certified_prediction :
    ∃ r : Reference, ∀ φ : Vec3, enorm φ≤angleRadius →
      ∃ X : Motion r φ, ∃ S : Response r φ,
        (∀ t ∈ Icc (0:ℝ) 1, orbitRadius≤‖X.p t‖) ∧
        ∀ t ∈ Icc (0:ℝ) 1,
          ‖X.p t-(r.q t+left φ (S.p t))‖≤positionError t ∧
          ‖X.v t-(r.v t+left φ (S.v t))‖≤velocityError t ∧
          (7000000:ℝ)*‖X.p t-(r.q t+left φ (S.p t))‖<1/1000 := by
  obtain ⟨r⟩ := exists_reference
  refine ⟨r,fun φ hφ => ?_⟩
  obtain ⟨X,hX⟩ := exists_motion r φ hφ
  obtain ⟨S⟩ := exists_response r φ
  refine ⟨X,S,hX,fun t ht => ?_⟩
  obtain ⟨hp,hv⟩ := prediction r φ hφ X S t ht
  exact ⟨hp,hv,(mul_le_mul_of_nonneg_left (hp.trans (position_le_endpoint ht))
    (by norm_num)).trans_lt (reported_error.trans_le (by norm_num))⟩

end GNC.OrbitalComparison.TangentialSharedInput
