import GNC.Applications.OrbitalComparison.TangentialReferenceMotion
import GNC.Dynamics.CandidateOrbitExistence
import GNC.Dynamics.ForcedOrbitUniqueness
import GNC.Dynamics.RotationCenteredError
import GNC.Dynamics.MonomialOrbitCertificate
import Mathlib.Analysis.Real.Pi.Bounds

/-! A three-dimensional nonlinear deputy during the noncircular EP burn.
The mounting angle is fixed in the prescribed reference RTN frame, not in
inertial space. Existence, uniqueness and an all-time coarse reachable tube
are derived for the whole angle ball. The tube is common to both predictors;
it is not an assertion of a geometric-versus-Cartesian accuracy advantage.
-/
noncomputable section
namespace GNC.OrbitalComparison.TangentialMountingMotion
open Set TangentialReferenceMotion TangentialReferenceData
open ThrustSupport (euclideanEquiv)

def angleRadius : ℝ := 1/50
def innerRadius : ℚ := (2*lowerRadius+2*(13/20)^2/lowerRadius^2)/3
def extensionRadius : ℚ := (lowerRadius-innerRadius)/4
def orbitRadius : ℝ := ((lowerRadius:ℝ)+(innerRadius:ℝ))/2

/-- The construction annulus is computed from the certified reference radius
and gravity gain. It is not added to the final reachable-tube error budget. -/
theorem region_checks :
    0<(innerRadius:ℝ) ∧ 0<extensionRadius ∧ 0<orbitRadius ∧
    (innerRadius:ℝ)<orbitRadius ∧
    orbitRadius+2*(extensionRadius:ℝ)=(lowerRadius:ℝ) ∧
    2*mu/(innerRadius:ℝ)^3≤1 ∧ 2*mu/orbitRadius^3≤1 ∧
    4*(angleRadius*acceleration)≤(extensionRadius:ℝ) ∧
    (angleRadius*acceleration)*PolynomialSupersolution.value 1 1<2*(extensionRadius:ℝ) := by
  norm_num [innerRadius,extensionRadius,orbitRadius,lowerRadius,inverseBound,
    mu,horizon,angleRadius,acceleration,alpha,PolynomialSupersolution.value,
    PolynomialSupersolution.polynomial]

def thrust (r : Reference) (φ : Vec3) (t : ℝ) : E :=
  acceleration • rotationIsometry (r.frame t)
    (euclideanEquiv (rotate (rotationExp φ) PlanarReferenceMotion.tangent))

theorem thrust_continuous (r : Reference) (φ : Vec3) : Continuous (thrust r φ) :=
  (rotated_continuous r (rotate (rotationExp φ) PlanarReferenceMotion.tangent)).const_smul _

theorem input_difference (r : Reference) (φ : Vec3) (hφ : enorm φ≤angleRadius) (t : ℝ) :
    ‖thrust r φ t-r.thrust t‖≤angleRadius*acceleration := by
  have h := RotationCenteredError.rotation_difference_bound φ PlanarReferenceMotion.tangent
    (hφ.trans_lt (by norm_num [angleRadius]; linarith [Real.pi_gt_three]))
  rw [PlanarReferenceMotion.tangent_norm,mul_one] at h
  have hA : 0≤acceleration := by norm_num [acceleration,horizon,alpha]
  rw [thrust,Reference.thrust,←smul_sub,←map_sub,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg hA,LinearIsometryEquiv.norm_map]
  change acceleration*enorm (rotate (rotationExp φ) PlanarReferenceMotion.tangent-
    PlanarReferenceMotion.tangent)≤angleRadius*acceleration
  exact (mul_le_mul_of_nonneg_left (h.trans hφ) hA).trans_eq (by ring)

theorem acceleration_continuous (r : Reference) :
    Continuous (fun t => Gravity.field mu (r.q t)+r.thrust t) := by
  have hq0 (t : ℝ) : ‖r.q t‖≠0 := by
    change enorm (PolynomialOrbitTransition.position (r.w (horizon*t)))≠0
    rw [PolynomialOrbitTransition.position_norm]
    exact (r.positive _).ne'
  have hc := q_continuous r
  exact ((continuous_const.div (hc.norm.pow 3)
    (fun t => pow_ne_zero 3 (hq0 t))).smul hc).add (TangentialReferenceMotion.thrust_continuous r)

structure Motion (r : Reference) (φ : Vec3) where
  p : ℝ → E
  v : ℝ → E
  continuous_p : Continuous p
  continuous_v : Continuous v
  initial_p : p 0=r.q 0
  initial_v : v 0=r.v 0
  derivative_p : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt p (v t) t
  derivative_v : ∀ t ∈ Icc (0:ℝ) 1,
    HasDerivAt v (Gravity.field mu (p t)+thrust r φ t) t

theorem exists_motion (r : Reference) (φ : Vec3) (hφ : enorm φ≤angleRadius) :
    ∃ X : Motion r φ, ∀ t ∈ Icc (0:ℝ) 1, orbitRadius≤‖X.p t‖ := by
  obtain ⟨p,v,hp,hv,hp0,hv0,hdp,hdv,hr⟩ := Gravity.exists_near_candidate
    (μ := mu) (scale := 1) (r := orbitRadius) (R := extensionRadius)
    (by norm_num [mu,horizon]) (by norm_num) region_checks.2.2.1 region_checks.2.1.le
    (by simpa using region_checks.2.2.2.2.2.2.1)
    r.q r.v (fun t => Gravity.field mu (r.q t)+r.thrust t) (thrust r φ)
    (q_continuous r) (v_continuous r) (acceleration_continuous r) (thrust_continuous r φ)
    (fun _ ht => q_derivative r ht) (fun _ ht => v_derivative r ht)
    (fun t ht => by rw [region_checks.2.2.2.2.1]; exact q_radius r ht)
    (D := angleRadius*acceleration) (by norm_num [angleRadius,acceleration,horizon,alpha])
    (fun t _ => by simpa only [one_smul,add_sub_add_left_eq_sub] using input_difference r φ hφ t)
    region_checks.2.2.2.2.2.2.2.1
  exact ⟨⟨p,v,hp,hv,hp0,hv0,hdp,by simpa only [one_smul] using hdv⟩,hr⟩

def trajectory (r : Reference) (φ : Vec3) (hφ : enorm φ≤angleRadius) : Motion r φ :=
  Classical.choose (exists_motion r φ hφ)

theorem trajectory_radius (r : Reference) (φ : Vec3) (hφ : enorm φ≤angleRadius)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) : orbitRadius≤‖(trajectory r φ hφ).p t‖ :=
  Classical.choose_spec (exists_motion r φ hφ) t ht

theorem unique (r : Reference) (φ : Vec3) (hφ : enorm φ≤angleRadius) (X : Motion r φ) :
    ∀ t ∈ Icc (0:ℝ) 1,
      X.p t=(trajectory r φ hφ).p t ∧ X.v t=(trajectory r φ hφ).v t := by
  let Y := trajectory r φ hφ
  apply ForcedOrbitUniqueness.unique mu 1 (by norm_num [mu,horizon]) (by norm_num)
    X.p X.v Y.p Y.v (thrust r φ) X.continuous_p X.continuous_v Y.continuous_p Y.continuous_v
    X.derivative_p (by simpa only [one_smul] using X.derivative_v)
    Y.derivative_p (by simpa only [one_smul] using Y.derivative_v)
    (X.initial_p.trans Y.initial_p.symm) (X.initial_v.trans Y.initial_v.symm)
    (r := (innerRadius:ℝ)) (M := orbitRadius-(innerRadius:ℝ))
    region_checks.1 (sub_pos.mpr region_checks.2.2.2.1)
    (by simpa using region_checks.2.2.2.2.2.1)
  intro t ht
  simpa only [add_sub_cancel] using trajectory_radius r φ hφ ht

def positionBound (t : ℝ) : ℝ :=
  (angleRadius*acceleration)*MonomialSupersolution.value 1 0 t
def velocityBound (t : ℝ) : ℝ :=
  (angleRadius*acceleration)*MonomialSupersolution.velocity 1 0 t

/-- This growing enclosure is uniform over all allowed three-axis mounting
offsets. No prior closeness of the actual deputy is a hypothesis. -/
theorem reference_tube (r : Reference) (φ : Vec3) (hφ : enorm φ≤angleRadius) (X : Motion r φ) :
    ∀ t ∈ Icc (0:ℝ) 1,
      ‖X.p t-r.q t‖≤positionBound t ∧ ‖X.v t-r.v t‖≤velocityBound t := by
  have h := Gravity.monomial_prediction mu (by norm_num [mu,horizon])
    X.p X.v r.q r.v (fun t => Gravity.field mu (r.q t)+r.thrust t) (thrust r φ)
    (fun _ : Fin 1 => angleRadius*acceleration) (fun _ : Fin 1 => 0)
    (κ := 1) (r := orbitRadius) (M := 2*(extensionRadius:ℝ))
    (by norm_num) (by norm_num) (by intro i; norm_num [angleRadius,acceleration,horizon,alpha])
    region_checks.2.2.1 (by simpa using region_checks.2.2.2.2.2.2.2.2)
    region_checks.2.2.2.2.2.2.1
    (fun t ht => by rw [region_checks.2.2.2.2.1]; exact q_radius r ht)
    X.continuous_p X.continuous_v (q_continuous r) (v_continuous r)
    X.derivative_p X.derivative_v (fun _ ht => q_derivative r ht) (fun _ ht => v_derivative r ht)
    X.initial_p X.initial_v (fun t _ => by simpa using input_difference r φ hφ t)
  simpa [positionBound,velocityBound] using h

end GNC.OrbitalComparison.TangentialMountingMotion
