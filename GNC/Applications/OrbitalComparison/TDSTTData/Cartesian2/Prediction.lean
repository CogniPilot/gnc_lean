import GNC.Applications.OrbitalComparison.TDSTTData.Cartesian2.Envelope
import GNC.Applications.OrbitalComparison.TDSTTData.Cartesian2.Kinematics
import GNC.Dynamics.CandidateOrbitExistence

/-! Full inverse-square, all-time certificate for the delivered Cartesian
rank-two polynomial query. Its velocity is the fitted tensor output, so
the proven kinematic discrepancy is added explicitly. All trajectories
start at the exact nominal state; no initial-map repair is assumed. -/
noncomputable section
namespace GNC.OrbitalComparison.TDSTTData.Cartesian2
open Set SpatialBurn Planning.PolynomialKernel

theorem position_continuous (x : Vec3) : Continuous (candidatePosition x) :=
  continuous_iff_continuousAt.mpr fun t => (position_derivative x t).continuousAt
theorem velocity_continuous (x : Vec3) : Continuous (candidateVelocity x) :=
  continuous_iff_continuousAt.mpr fun t => (velocity_derivative x t).continuousAt

theorem exactForce_continuous : Continuous (fun t =>
    (WithLp.toLp 2 (JointErrorData.exactForce t) : E3)) := by
  simp_rw [JointErrorData.exactForce_model]
  dsimp [VaryingRateReference.thrust,SpatialRotatingFrame.mix,pack,JointErrorData.phase,
    JointErrorData.referenceRate,PolynomialOrder.value,evaluate]
  fun_prop

theorem thrust_continuous (x : Vec3) : Continuous (thrust x) := by
  unfold thrust rotate
  have h : Continuous JointErrorData.exactForce :=
    (PiLp.continuous_ofLp 2 (fun _ : Fin 3 => ℝ)).comp exactForce_continuous
  fun_prop

theorem acceleration_continuous (x : Vec3) : Continuous (candidateAcceleration x) := by
  have hq : Continuous (fun t => (WithLp.toLp 2 (JointErrorData.exactReference t) : E3)) :=
    continuous_iff_continuousAt.mpr fun t => (JointErrorData.reference_position_derivative t).continuousAt
  have hn (t : ℝ) : ‖(WithLp.toLp 2 (JointErrorData.exactReference t) : E3)‖=1 :=
    JointErrorData.exactReference_norm t
  have hp : Continuous (fun t => PointingCapPolynomial.vectorValue
      (PointingCapPolynomial.derivative (PointingCapPolynomial.derivative position)) x t) :=
    continuous_iff_continuousAt.mpr fun t => (PointingCapPolynomial.vector_derivative _ _ t).continuousAt
  unfold candidateAcceleration Gravity.field
  simp_rw [hn]
  exact ((hq.const_smul _).add exactForce_continuous).add hp

structure Motion (x : Vec3) where
  p : ℝ → E3
  v : ℝ → E3
  continuous_p : Continuous p
  continuous_v : Continuous v
  initial_p : p 0=candidatePosition x 0
  initial_v : v 0=candidateVelocity x 0
  derivative_p : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt p (v t) t
  derivative_v : ∀ t ∈ Icc (0:ℝ) 1,
    HasDerivAt v (Gravity.field (physicalInput.K:ℝ) (p t)+thrust x t) t

theorem motion_initial_nominal {x : Vec3} (X : Motion x) :
    X.p 0=WithLp.toLp 2 (JointErrorData.exactReference 0) ∧
      X.v 0=JointErrorData.referenceVelocity 0 := by
  rw [X.initial_p,X.initial_v]
  exact ⟨position_initial x,velocity_initial x⟩

theorem candidate_radius {x : Vec3} {t : ℝ}
    (hx : x 0^2+x 1^2+x 2^2≤(sigma:ℝ)^2) (ht : t ∈ Icc (0:ℝ) 1) :
    1-(displacementMaximum:ℝ)≤‖candidatePosition x t‖ := by
  have h := CartesianRadiusDefect.candidate_radius (JointErrorData.exactReference t)
    (LieSTTOutput.value3 physicalInput.rho x t) (displacement_uniform hx ht)
  rw [JointErrorData.exactReference_norm] at h
  simpa only [candidatePosition,polynomial_value] using h.1

theorem physical_defect_forcing {x : Vec3} {t : ℝ}
    (hx : x 0^2+x 1^2+x 2^2≤(sigma:ℝ)^2) (ht : t ∈ Icc (0:ℝ) 1) :
    ‖candidateAcceleration x t-(Gravity.field (physicalInput.K:ℝ) (candidatePosition x t)+thrust x t)‖≤
      PolynomialOrder.value forcing t := by
  rw [physical_defect_value]
  exact (physical_defect_profile hx ht).trans (forcing_dominates ht.1)

theorem region_positive : 0<(radiusFloor:ℝ) := by exact_mod_cast region_checked.2

theorem exists_motion {x : Vec3} (hx : x 0^2+x 1^2+x 2^2≤(sigma:ℝ)^2) :
    ∃ X : Motion x, ∀ t ∈ Icc (0:ℝ) 1, (radiusFloor:ℝ)≤‖X.p t‖ := by
  have hK : 0≤(physicalInput.K:ℝ) := by exact_mod_cast JointErrorData.model_K_nonnegative
  have hP : 0≤excursion/2 := by linarith [region_checked.1]
  have hg : (1:ℝ)*(2*(physicalInput.K:ℝ)/(radiusFloor:ℝ)^3)≤1 := by
    have h : (exactGain:ℝ)≤1 := by exact_mod_cast gain_checked.2.2.2
    simpa only [exactGain,Rat.cast_mul,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat,one_mul] using h
  have he := PolynomialOrder.value_at_rational forcing 1
  norm_num only [Rat.cast_one] at he
  have hD : 0≤PolynomialOrder.value forcing 1 :=
    PolynomialOrder.value_nonnegative forcing envelope_checked.1 (by norm_num)
  have hclose : 4*PolynomialOrder.value forcing 1≤((excursion/2:ℚ):ℝ) := by
    rw [he]
    exact_mod_cast existence_checked
  obtain ⟨p,v,hp,hv,hip,hiv,hdp,hdv,hr⟩ := Gravity.exists_near_candidate
    hK (by norm_num : (0:ℝ)≤1) region_positive hP hg
    (candidatePosition x) (candidateVelocity x) (candidateAcceleration x) (thrust x)
    (position_continuous x) (velocity_continuous x) (acceleration_continuous x) (thrust_continuous x)
    (fun t _ => position_derivative x t) (fun t _ => velocity_derivative x t)
    (fun t ht => by
      have h := candidate_radius hx ht
      simp only [radiusFloor,Rat.cast_sub,Rat.cast_one,Rat.cast_div,Rat.cast_ofNat]
      linarith) hD
    (fun t ht => by
      simpa only [one_smul,norm_sub_rev] using
        (physical_defect_forcing hx ht).trans
          (PolynomialOrder.value_le_endpoint forcing envelope_checked.1 ht)) hclose
  exact ⟨⟨p,v,hp,hv,hip,hiv,hdp,fun t ht => by simpa only [one_smul] using hdv t ht⟩,hr⟩

theorem certifies {x : Vec3} (hx : x 0^2+x 1^2+x 2^2≤(sigma:ℝ)^2) (X : Motion x) :
    ∀ t ∈ Icc (0:ℝ) 1,
      ‖X.p t-candidatePosition x t‖≤PolynomialOrder.value envelope t ∧
      ‖X.v t-candidateVelocity x t‖≤PolynomialOrder.value (differentiate envelope) t := by
  have hK : 0≤(physicalInput.K:ℝ) := by exact_mod_cast JointErrorData.model_K_nonnegative
  have hclose : PolynomialOrder.value forcing 1*
      PolynomialSupersolution.value (gain:ℝ) 1<(excursion:ℝ) := by
    have h : ((evaluate forcing 1:ℚ):ℝ)*(HarmonicCertificate.positionGain gain:ℝ)<
        (excursion:ℝ) := by exact_mod_cast closure_checked
    have he := PolynomialOrder.value_at_rational forcing 1
    norm_num only [Rat.cast_one] at he
    simpa only [he,HarmonicCertificate.positionGain_cast] using h
  have hgain : (1:ℝ)*(2*(physicalInput.K:ℝ)/(radiusFloor:ℝ)^3)≤(gain:ℝ) := by
    have h : (exactGain:ℝ)≤(gain:ℝ) := by exact_mod_cast gain_checked.2.2.1
    simpa only [exactGain,Rat.cast_mul,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat,one_mul] using h
  exact Gravity.polynomial_prediction_curve (physicalInput.K:ℝ) 1 hK (by norm_num)
    X.p X.v (candidatePosition x) (candidateVelocity x) (candidateAcceleration x) (thrust x)
    forcing envelope envelope_checked gain_checked.1 gain_checked.2.1
    region_positive hclose hgain
    (fun t ht => by
      have h := candidate_radius hx ht
      simp only [radiusFloor,Rat.cast_sub,Rat.cast_one]
      linarith) X.continuous_p X.continuous_v
    (position_continuous x) (velocity_continuous x) X.derivative_p
    (fun t ht => by simpa only [one_smul] using X.derivative_v t ht)
    (fun t _ => position_derivative x t) (fun t _ => velocity_derivative x t)
    X.initial_p X.initial_v
    (fun t ht => by simpa only [one_smul,norm_sub_rev] using physical_defect_forcing hx ht)

theorem delivered_certificate {x : Vec3}
    (hx : x 0^2+x 1^2+x 2^2≤(sigma:ℝ)^2) (X : Motion x) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ‖X.p t-candidatePosition x t‖≤PolynomialOrder.value envelope t ∧
    ‖X.v t-deliveredVelocity x t‖≤PolynomialOrder.value (differentiate envelope) t+
      PolynomialOrder.value (kinematicRange.bound 1) t := by
  have h := certifies hx X t ht
  refine ⟨h.1,?_⟩
  exact (norm_sub_le_norm_sub_add_norm_sub (X.v t) (candidateVelocity x t) (deliveredVelocity x t)).trans
    (add_le_add h.2 (delivered_velocity_discrepancy hx ht.1))

/-- Displayed SI bounds apply at every burn time to the actual delivered
position and velocity queries, including the former warm-up interval. -/
theorem physical_prediction {x : Vec3} (hx : x 0^2+x 1^2+x 2^2≤(sigma:ℝ)^2) :
    (∃ X : Motion x, ∀ t ∈ Icc (0:ℝ) 1, (radiusFloor:ℝ)≤‖X.p t‖) ∧
    (∀ X : Motion x, ∀ t ∈ Icc (0:ℝ) 1,
      7000000*‖X.p t-candidatePosition x t‖≤(positionUpper:ℝ) ∧
      (7000000/120)*‖X.v t-deliveredVelocity x t‖≤(velocityUpper:ℝ)) := by
  refine ⟨exists_motion hx,?_⟩
  intro X t ht
  have hb := delivered_certificate hx X ht
  have hp := PolynomialOrder.value_le_endpoint envelope envelope_checked.2.1 ht
  have hv := PolynomialOrder.value_le_endpoint (differentiate envelope) envelope_checked.2.2.1 ht
  have hk := PolynomialOrder.value_le_endpoint (kinematicRange.bound 1) kinematic_profile_nonnegative ht
  have ep := PolynomialOrder.value_at_rational envelope 1
  have ev := PolynomialOrder.value_at_rational (differentiate envelope) 1
  have ek := PolynomialOrder.value_at_rational (kinematicRange.bound 1) 1
  norm_num only [Rat.cast_one] at ep ev ek
  rw [ep] at hp
  rw [ev] at hv
  rw [ek] at hk
  have hdp : (7000000:ℝ)*((evaluate envelope 1:ℚ):ℝ)≤(positionUpper:ℝ) := by
    exact_mod_cast displayed_bounds.1
  have hdv : (7000000/120:ℝ)*(((evaluate (differentiate envelope) 1:ℚ):ℝ)+
      ((evaluate (kinematicRange.bound 1) 1:ℚ):ℝ))≤(velocityUpper:ℝ) := by
    have h : ((7000000/120*(evaluate (differentiate envelope) 1+
        evaluate (kinematicRange.bound 1) 1):ℚ):ℝ)≤(velocityUpper:ℝ) := by
      exact_mod_cast displayed_bounds.2
    push_cast at h
    exact h
  exact ⟨(mul_le_mul_of_nonneg_left (hb.1.trans hp) (by norm_num)).trans hdp,
    (mul_le_mul_of_nonneg_left (hb.2.trans (add_le_add hv hk)) (by norm_num)).trans hdv⟩

end GNC.OrbitalComparison.TDSTTData.Cartesian2
