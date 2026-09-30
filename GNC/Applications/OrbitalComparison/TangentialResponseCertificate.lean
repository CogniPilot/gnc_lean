import GNC.Applications.OrbitalComparison.TangentialMountingCertificate
import GNC.Dynamics.GravityLinearResponse
import GNC.Dynamics.RetainedMonomialCertificate

/-! Finite-angle prediction along the certified noncircular EP reference.
The retained response keeps the exact rotated thrust direction and the full
time-varying reference gravity gradient. Only the spatial gravity remainder
is bounded. This is an ideal continuous response certificate; numerical
response construction and evaluation errors are not silently set to zero.
-/
noncomputable section
namespace GNC.OrbitalComparison.TangentialResponseCertificate
open Set TangentialReferenceMotion TangentialReferenceData
open TangentialMountingMotion GravityLinearResponse

def forcing (r : Reference) (φ : Vec3) (t : ℝ) : E :=
  TangentialMountingMotion.thrust r φ t-r.thrust t

abbrev Response (r : Reference) (φ : Vec3) :=
  GravityLinearResponse.Response mu 1 r.q (forcing r φ)

theorem exists_response (r : Reference) (φ : Vec3) : Nonempty (Response r φ) := by
  apply GravityLinearResponse.Response.exists mu 1 (q_continuous r) _
    ((TangentialMountingMotion.thrust_continuous r φ).sub
      (TangentialReferenceMotion.thrust_continuous r))
  intro t
  apply norm_ne_zero_iff.mp
  change enorm (PolynomialOrbitTransition.position (r.w (horizon*t)))≠0
  rw [PolynomialOrbitTransition.position_norm]
  exact (r.positive _).ne'

def responseRadius : ℝ := angleRadius*acceleration*
  PolynomialSupersolution.value (2*mu/(lowerRadius:ℝ)^3) 1
def gravityBudget : ℝ := 3*mu/((lowerRadius:ℝ)-responseRadius)^4*responseRadius^2
def positionError (t : ℝ) : ℝ := gravityBudget*MonomialSupersolution.value 1 4 t
def velocityError (t : ℝ) : ℝ := gravityBudget*MonomialSupersolution.velocity 1 4 t

/-- All domain and closure quantities are derived from the reference and
input ball. There is no assumed deputy tube or fitted numerical allowance. -/
theorem checks :
    0≤mu ∧ 0<(lowerRadius:ℝ) ∧ 0≤angleRadius*acceleration ∧
    2*mu/(lowerRadius:ℝ)^3<56 ∧ 0≤responseRadius ∧
    2*responseRadius<(lowerRadius:ℝ) ∧
    2*mu/((lowerRadius:ℝ)-2*responseRadius)^3≤1 ∧
    gravityBudget*PolynomialSupersolution.value 1 1<responseRadius := by
  norm_num [mu,horizon,lowerRadius,inverseBound,angleRadius,acceleration,alpha,
    responseRadius,gravityBudget,PolynomialSupersolution.value,PolynomialSupersolution.polynomial]

theorem response_shape (r : Reference) (φ : Vec3) (hφ : enorm φ≤angleRadius)
    (S : Response r φ) :
    ∀ t ∈ Icc (0:ℝ) 1, ‖S.p t‖≤responseRadius*t^2 := by
  exact Gravity.retained_response_shape mu lowerRadius (angleRadius*acceleration)
    checks.1 checks.2.1 checks.2.2.1 checks.2.2.2.1 r.q S.p S.v (forcing r φ)
    (fun _ ht => q_radius r ht) (fun t _ => input_difference r φ hφ t)
    S.continuous_p S.continuous_v S.derivative_p
    (by simpa only [one_smul] using S.derivative_v) S.initial_p S.initial_v

/-- The complete nonlinear physical ODE is compared with the retained
response, uniformly in time and over the three-dimensional mounting ball. -/
theorem prediction (r : Reference) (φ : Vec3) (hφ : enorm φ≤angleRadius)
    (X : Motion r φ) (S : Response r φ) :
    ∀ t ∈ Icc (0:ℝ) 1,
      ‖X.p t-(r.q t+S.p t)‖≤positionError t ∧
      ‖X.v t-(r.v t+S.v t)‖≤velocityError t := by
  have h := Gravity.retained_monomial_prediction mu lowerRadius responseRadius 0 1
    checks.1 checks.2.2.2.2.1 checks.2.2.2.2.2.1 (by norm_num)
    (by norm_num) (by norm_num) checks.2.2.2.2.2.2.1
    (by simpa [gravityBudget] using checks.2.2.2.2.2.2.2)
    X.p X.v r.q r.v S.p S.v r.thrust (forcing r φ) (forcing r φ)
    (fun _ ht => q_radius r ht) (response_shape r φ hφ S) (by intros; simp)
    X.continuous_p X.continuous_v (q_continuous r) (v_continuous r)
    S.continuous_p S.continuous_v X.derivative_p
    (by simpa [forcing] using X.derivative_v)
    (fun _ ht => q_derivative r ht) (fun _ ht => v_derivative r ht)
    S.derivative_p (by simpa only [one_smul] using S.derivative_v)
    (by simpa [S.initial_p] using X.initial_p)
    (by simpa [S.initial_v] using X.initial_v)
  simpa [positionError,velocityError,gravityBudget] using h

theorem position_formula (t : ℝ) :
    positionError t=gravityBudget*(t^6/30+t^8/1680+t^10/151200+t^12/19807200) := by
  norm_num [positionError,MonomialSupersolution.value,MonomialSupersolution.polynomial,
    MonomialSupersolution.pair,MonomialSupersolution.four,MonomialSupersolution.six]
  ring_nf <;> simp

theorem position_le_endpoint {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    positionError t≤positionError 1 :=
  mul_le_mul_of_nonneg_left
    (MonomialSupersolution.value_le_endpoint 4 (by norm_num) (by norm_num) ht)
    (by have h := checks.1; unfold gravityBudget; positivity)

/-- Outward decimal reporting of the formula, not a fitted tolerance. -/
theorem reported_error : (7000000:ℝ)*positionError 1<1/1000000000 := by
  rw [position_formula]
  norm_num [gravityBudget,responseRadius,mu,horizon,lowerRadius,inverseBound,
    angleRadius,acceleration,alpha,PolynomialSupersolution.value,PolynomialSupersolution.polynomial]

/-- Replacing the exact reference position by its certified polynomial adds
its own error. The response in this statement still uses the exact reference. -/
theorem computed_reference_prediction (r : Reference) (φ : Vec3) (hφ : enorm φ≤angleRadius)
    (X : Motion r φ) (S : Response r φ) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ∃ j : ℕ, j<32 ∧ ∃ u ∈ Icc (0:ℝ) (13/640),
      horizon*t=(j:ℝ)*(13/640)+u ∧
        ‖X.p t-(polynomialPosition j u+S.p t)‖≤positionError t+2*(errorBound:ℝ) := by
  obtain ⟨j,hj,u,hu,htj,hq⟩ := reference_approximation r ht
  refine ⟨j,hj,u,hu,htj,?_⟩
  have he : X.p t-(polynomialPosition j u+S.p t)=
      (X.p t-(r.q t+S.p t))+(r.q t-polynomialPosition j u) := by abel
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add (prediction r φ hφ X S t ht).1 hq)

theorem reported_computed_reference_error :
    (7000000:ℝ)*(positionError 1+2*(errorBound:ℝ))<3/1000000000 := by
  have h := reported_error
  have href : (7000000:ℝ)*(2*(errorBound:ℝ))<2/1000000000 := by norm_num [errorBound]
  linarith

/-- Both the reference response and the full nonlinear deputy exist.
This statement has no assumed physical trajectory or closeness hypothesis. -/
theorem exists_certified_prediction (r : Reference) (φ : Vec3) (hφ : enorm φ≤angleRadius) :
    ∃ X : Motion r φ, ∃ S : Response r φ,
      (∀ t ∈ Icc (0:ℝ) 1, orbitRadius≤‖X.p t‖) ∧
      ∀ t ∈ Icc (0:ℝ) 1,
        ‖X.p t-(r.q t+S.p t)‖≤positionError t ∧
        ‖X.v t-(r.v t+S.v t)‖≤velocityError t ∧
        (7000000:ℝ)*‖X.p t-(r.q t+S.p t)‖<1/1000000000 := by
  obtain ⟨S⟩ := exists_response r φ
  let X := trajectory r φ hφ
  refine ⟨X,S,fun _ ht => trajectory_radius r φ hφ ht,?_⟩
  intro t ht
  obtain ⟨hp,hv⟩ := prediction r φ hφ X S t ht
  exact ⟨hp,hv,(mul_le_mul_of_nonneg_left
    (hp.trans (position_le_endpoint ht)) (by norm_num)).trans_lt reported_error⟩

end GNC.OrbitalComparison.TangentialResponseCertificate
