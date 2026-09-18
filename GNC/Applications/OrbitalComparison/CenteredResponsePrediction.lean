import GNC.Applications.OrbitalComparison.CenteredResponseKinematics
import GNC.Dynamics.CandidateOrbitExistence
import GNC.Dynamics.PolynomialForcingCertificate

/-! Complete three-axis physical certificate for the centered Cartesian
quadratic predictor, including existence and the actual midpoint family.
Position is normalized by 7,000,000 m and time by 120 s. -/
noncomputable section
namespace GNC.OrbitalComparison.CenteredResponseData
open Set Planning.PolynomialKernel

theorem position_continuous (φ : Vec3) : Continuous (position φ) :=
  continuous_iff_continuousAt.mpr fun t => (position_derivative φ t).continuousAt
theorem velocity_continuous (φ : Vec3) : Continuous (velocity φ) :=
  continuous_iff_continuousAt.mpr fun t => (velocity_derivative φ t).continuousAt

theorem exact_force_continuous :
    Continuous (fun t => (WithLp.toLp 2 (JointErrorData.exactForce t) : E3)) := by
  simp_rw [JointErrorData.exactForce_model]
  dsimp [VaryingRateReference.thrust,SpatialRotatingFrame.mix,SpatialBurn.pack,JointErrorData.phase,
    JointErrorData.referenceRate,PolynomialOrder.value,evaluate]
  fun_prop

theorem thrust_continuous (φ : Vec3) : Continuous (thrust φ) :=
  (rotationIsometry (rotationExp φ)).continuous.comp exact_force_continuous

theorem acceleration_continuous (φ : Vec3) : Continuous (acceleration φ) := by
  have hq : Continuous nominal :=
    continuous_iff_continuousAt.mpr fun t => (JointErrorData.reference_position_derivative t).continuousAt
  have ha : Continuous (firstAcceleration (rotationWeights φ)) :=
    continuous_iff_continuousAt.mpr fun t =>
      (response_derivative (fun j => CartesianResponsePolynomial.derivative
        (CartesianResponsePolynomial.derivative (first j))) (rotationWeights φ) t).continuousAt
  have hb : Continuous (secondAcceleration (rotationWeights φ)) :=
    continuous_iff_continuousAt.mpr fun t =>
      (response_derivative (fun j => CartesianResponsePolynomial.derivative
        (CartesianResponsePolynomial.derivative (second j))) (productWeights (rotationWeights φ)) t).continuousAt
  have hc : Continuous (centeredAcceleration φ) := by
    unfold centeredAcceleration Gravity.field
    simp_rw [nominal_norm]
    exact ((hq.const_smul _).add exact_force_continuous).add (ha.add hb)
  exact (rotationIsometry (halfRotation φ)).continuous.comp hc

structure Motion (φ : Vec3) where
  p : ℝ → E3
  v : ℝ → E3
  continuous_p : Continuous p
  continuous_v : Continuous v
  initial_p : p 0=position φ 0
  initial_v : v 0=velocity φ 0
  derivative_p : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt p (v t) t
  derivative_v : ∀ t ∈ Icc (0:ℝ) 1,
    HasDerivAt v (Gravity.field (K:ℝ) (p t)+thrust φ t) t

theorem motion_initial_midpoint {φ : Vec3} (X : Motion φ) :
    X.p 0=WithLp.toLp 2 (RotationCenteredError.midpoint
      (rotationExp φ) JointErrorData.initialReferencePosition) ∧
    X.v 0=WithLp.toLp 2 (RotationCenteredError.midpoint
      (rotationExp φ) JointErrorData.initialReferenceVelocity) := by
  rw [X.initial_p,X.initial_v]
  exact ⟨position_initial φ,velocity_initial φ⟩

theorem region_positive : 0<1-2*(displacementRange:ℝ) := by
  have h : 2*(displacementRange:ℝ)<1 := by exact_mod_cast region_checked.2.2.2
  linarith

theorem physical_gain_bound :
    (1:ℝ)*(2*(K:ℝ)/(1-2*(displacementRange:ℝ))^3)≤(physicalGain:ℝ) := by
  simpa only [one_mul] using
    (show 2*(K:ℝ)/(1-2*(displacementRange:ℝ))^3≤(physicalGain:ℝ) by
      exact_mod_cast gravity_gain_checked.2.2.1)

theorem forcing_value (t : ℝ) : PolynomialOrder.value forcing t=(defectMagnitude:ℝ) := by
  simp [forcing,PolynomialOrder.value,evaluate]

theorem physical_defect_forcing (φ : Vec3) (hφ : enorm φ≤1/10)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ‖acceleration φ t-(Gravity.field (K:ℝ) (position φ t)+thrust φ t)‖≤
      PolynomialOrder.value forcing t := by
  rw [forcing_value]
  exact physical_defect φ hφ ht

theorem exists_motion (φ : Vec3) (hφ : enorm φ≤1/10) :
    ∃ X : Motion φ, ∀ t ∈ Icc (0:ℝ) 1, 1-2*(displacementRange:ℝ)≤‖X.p t‖ := by
  have hK : (0:ℝ)≤K := by exact_mod_cast K_nonnegative
  have hR : 0≤displacementRange/2 := div_nonneg region_checked.2.2.1.le (by norm_num)
  have hg : (1:ℝ)*(2*(K:ℝ)/(1-2*(displacementRange:ℝ))^3)≤1 :=
    physical_gain_bound.trans (by exact_mod_cast gravity_gain_checked.2.2.2)
  have hD : 0≤PolynomialOrder.value forcing 1 :=
    PolynomialOrder.value_nonnegative forcing physical_envelope_checked.1 (by norm_num)
  have he := PolynomialOrder.value_at_rational forcing 1
  norm_num only [Rat.cast_one] at he
  have hclose : 4*PolynomialOrder.value forcing 1≤((displacementRange/2:ℚ):ℝ) := by
    rw [he]
    exact_mod_cast physical_existence_checked
  obtain ⟨p,v,hp,hv,hip,hiv,hdp,hdv,hr⟩ := Gravity.exists_near_candidate
    hK (by norm_num : (0:ℝ)≤1) region_positive hR hg
    (position φ) (velocity φ) (acceleration φ) (thrust φ)
    (position_continuous φ) (velocity_continuous φ) (acceleration_continuous φ) (thrust_continuous φ)
    (fun t _ => position_derivative φ t) (fun t _ => velocity_derivative φ t)
    (fun t ht => by
      have h := position_radius φ hφ ht
      push_cast
      linarith) hD
    (fun t ht => by
      simpa only [one_smul,norm_sub_rev,forcing_value] using physical_defect φ hφ ht) hclose
  exact ⟨⟨p,v,hp,hv,hip,hiv,hdp,fun t ht => by simpa only [one_smul] using hdv t ht⟩,hr⟩

theorem certifies (φ : Vec3) (hφ : enorm φ≤1/10) (X : Motion φ) :
    ∀ t ∈ Icc (0:ℝ) 1,
      ‖X.p t-position φ t‖≤PolynomialOrder.value physicalEnvelope t ∧
      ‖X.v t-velocity φ t‖≤PolynomialOrder.value (differentiate physicalEnvelope) t := by
  have hK : (0:ℝ)≤K := by exact_mod_cast K_nonnegative
  have hclose : PolynomialOrder.value forcing 1*
      PolynomialSupersolution.value (physicalGain:ℝ) 1<(displacementRange:ℝ) := by
    have h : ((evaluate forcing 1:ℚ):ℝ)*(HarmonicCertificate.positionGain physicalGain:ℝ)<
        (displacementRange:ℝ) := by exact_mod_cast physical_closure_checked
    have he := PolynomialOrder.value_at_rational forcing 1
    norm_num only [Rat.cast_one] at he
    simpa only [he,HarmonicCertificate.positionGain_cast] using h
  exact Gravity.polynomial_prediction_curve (K:ℝ) 1 hK (by norm_num)
    X.p X.v (position φ) (velocity φ) (acceleration φ) (thrust φ)
    forcing physicalEnvelope physical_envelope_checked gravity_gain_checked.1 gravity_gain_checked.2.1
    region_positive hclose physical_gain_bound
    (fun t ht => by linarith [position_radius φ hφ ht]) X.continuous_p X.continuous_v
    (position_continuous φ) (velocity_continuous φ) X.derivative_p
    (fun t ht => by simpa only [one_smul] using X.derivative_v t ht)
    (fun t _ => position_derivative φ t) (fun t _ => velocity_derivative φ t)
    X.initial_p X.initial_v
    (fun t ht => by simpa only [one_smul,norm_sub_rev] using physical_defect_forcing φ hφ ht)

/-- Every three-axis attitude in the 0.1 rad ball, every time in the burn,
and every physical solution with the declared midpoint initial state. -/
theorem physical_prediction (φ : Vec3) (hφ : enorm φ≤1/10) :
    (∃ X : Motion φ, ∀ t ∈ Icc (0:ℝ) 1, 1-2*(displacementRange:ℝ)≤‖X.p t‖) ∧
    (∀ X : Motion φ, ∀ t ∈ Icc (0:ℝ) 1,
      7000000*‖X.p t-position φ t‖≤(positionUpper:ℝ) ∧
      (7000000/120)*‖X.v t-velocity φ t‖≤(velocityUpper:ℝ)) := by
  refine ⟨exists_motion φ hφ,?_⟩
  intro X t ht
  have hb := certifies φ hφ X t ht
  have hp := PolynomialOrder.value_le_endpoint physicalEnvelope physical_envelope_checked.2.1 ht
  have hv := PolynomialOrder.value_le_endpoint (differentiate physicalEnvelope) physical_envelope_checked.2.2.1 ht
  have ep := PolynomialOrder.value_at_rational physicalEnvelope 1
  have ev := PolynomialOrder.value_at_rational (differentiate physicalEnvelope) 1
  norm_num only [Rat.cast_one] at ep ev
  rw [ep] at hp
  rw [ev] at hv
  have hdp : (7000000:ℝ)*((evaluate physicalEnvelope 1:ℚ):ℝ)≤(positionUpper:ℝ) := by
    exact_mod_cast physical_display_checked.1
  have hdv : (7000000/120:ℝ)*((evaluate (differentiate physicalEnvelope) 1:ℚ):ℝ)≤(velocityUpper:ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).mpr physical_display_checked.2
    simpa only [Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] using h
  exact ⟨(mul_le_mul_of_nonneg_left (hb.1.trans hp) (by norm_num)).trans hdp,
    (mul_le_mul_of_nonneg_left (hb.2.trans hv) (by norm_num)).trans hdv⟩

end GNC.OrbitalComparison.CenteredResponseData
