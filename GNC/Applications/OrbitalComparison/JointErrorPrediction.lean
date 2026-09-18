import GNC.Applications.OrbitalComparison.JointErrorData.Envelope
import GNC.Applications.OrbitalComparison.JointErrorInitialState
import GNC.Dynamics.CandidateOrbitExistence

/-! Complete trajectory certificate for the three-axis correlated initial
family. Position is normalized by 7000 km and time by 120 s. The candidate's
actual initial position and velocity are used, not the nominal's initial
state. Every allowed attitude and every burn time are covered. -/
noncomputable section
namespace GNC.OrbitalComparison.JointErrorData
open Set SpatialBurn Planning.PolynomialKernel

theorem position_continuous (x : Vec3) : Continuous (position x) :=
  continuous_iff_continuousAt.mpr fun t => (position_derivative x t).continuousAt

theorem velocity_continuous (x : Vec3) : Continuous (velocity x) :=
  continuous_iff_continuousAt.mpr fun t => (velocity_derivative x t).continuousAt

theorem exactForce_continuous : Continuous (fun t => (WithLp.toLp 2 (exactForce t) : E3)) := by
  simp_rw [exactForce_model]
  dsimp [VaryingRateReference.thrust,SpatialRotatingFrame.mix,pack,phase,
    referenceRate,PolynomialOrder.value,evaluate]
  fun_prop

theorem thrust_continuous (x : Vec3) : Continuous (thrust x) := by
  unfold thrust rotate
  have h : Continuous exactForce := by
    exact (PiLp.continuous_ofLp 2 (fun _ : Fin 3 => ℝ)).comp exactForce_continuous
  fun_prop

theorem acceleration_continuous (x : Vec3) : Continuous (acceleration x) := by
  have hq : Continuous (fun t => (WithLp.toLp 2 (exactReference t) : E3)) :=
    continuous_iff_continuousAt.mpr fun t => (reference_position_derivative t).continuousAt
  have hn (t : ℝ) : ‖(WithLp.toLp 2 (exactReference t) : E3)‖=1 := exactReference_norm t
  have hp : Continuous (fun t => LieRadiusFrame.left x
      (PointingCapPolynomial.vectorValue (PointingCapPolynomial.derivative
        (PointingCapPolynomial.derivative modelInput.rho)) x t)) :=
    continuous_iff_continuousAt.mpr fun t =>
      (LieRadiusFrame.left_derivative x (PointingCapPolynomial.vector_derivative _ _ t)).continuousAt
  unfold acceleration Gravity.field
  simp_rw [hn]
  exact ((hq.const_smul _).add exactForce_continuous).add hp

structure Motion (x : Vec3) where
  p : ℝ → E3
  v : ℝ → E3
  continuous_p : Continuous p
  continuous_v : Continuous v
  initial_p : p 0=position x 0
  initial_v : v 0=velocity x 0
  derivative_p : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt p (v t) t
  derivative_v : ∀ t ∈ Icc (0:ℝ) 1,
    HasDerivAt v (Gravity.field (modelInput.K:ℝ) (p t)+thrust x t) t

/-- The certified physical solutions start in the experiment's correlated
midpoint family, not merely at an uninterpreted polynomial initial state. -/
theorem motion_initial_midpoint {x : Vec3} (X : Motion x) :
    (X.p 0).ofLp=(1/2:ℝ) •
      (initialReferencePosition+rotate (rotationExp x) initialReferencePosition) ∧
    (X.v 0).ofLp=(1/2:ℝ) •
      (initialReferenceVelocity+rotate (rotationExp x) initialReferenceVelocity) := by
  rw [X.initial_p,X.initial_v]
  exact ⟨initial_position_midpoint x,initial_velocity_midpoint x⟩

theorem candidate_radius {x : Vec3} {t : ℝ}
    (hx : x 0^2+x 1^2+x 2^2≤(sigma:ℝ)^2) (ht : t ∈ Icc (0:ℝ) 1) :
    1-(rhoMaximum:ℝ)≤‖position x t‖ :=
  position_radius (attitude_bound hx).2 (rho_uniform hx ht)

theorem region_positive : 0<1-2*(rhoMaximum:ℝ) := by
  have h : 2*(rhoMaximum:ℝ)<1 := by exact_mod_cast uniform_ranges_checked.2.2.2.1
  linarith

theorem exists_motion {x : Vec3} (hx : x 0^2+x 1^2+x 2^2≤(sigma:ℝ)^2) :
    ∃ X : Motion x, ∀ t ∈ Icc (0:ℝ) 1, 1-2*(rhoMaximum:ℝ)≤‖X.p t‖ := by
  have hK : 0≤(modelInput.K:ℝ) := by exact_mod_cast model_K_nonnegative
  have hP : 0≤rhoMaximum/2 := by linarith [uniform_ranges_checked.2.2.1]
  have hg : (1:ℝ)*(2*(modelInput.K:ℝ)/(1-2*(rhoMaximum:ℝ))^3)≤1 := by
    have h : (exactGain:ℝ)≤1 := by exact_mod_cast gain_checked.2.2.2
    simpa only [exactGain,Rat.cast_mul,Rat.cast_div,Rat.cast_sub,Rat.cast_pow,
      Rat.cast_ofNat,Rat.cast_one,one_mul] using h
  have he := PolynomialOrder.value_at_rational forcing 1
  norm_num only [Rat.cast_one] at he
  have hD : 0≤PolynomialOrder.value forcing 1 :=
    PolynomialOrder.value_nonnegative forcing envelope_checked.1 (by norm_num)
  have hclose : 4*PolynomialOrder.value forcing 1≤((rhoMaximum/2:ℚ):ℝ) := by
    rw [he]
    exact_mod_cast existence_checked
  obtain ⟨p,v,hp,hv,hip,hiv,hdp,hdv,hr⟩ := Gravity.exists_near_candidate
    hK (by norm_num : (0:ℝ)≤1) region_positive hP hg
    (position x) (velocity x) (acceleration x) (thrust x)
    (position_continuous x) (velocity_continuous x) (acceleration_continuous x) (thrust_continuous x)
    (fun t _ => position_derivative x t) (fun t _ => velocity_derivative x t)
    (fun t ht => by
      have h := candidate_radius hx ht
      push_cast
      linarith) hD
    (fun t ht => by
      simpa only [one_smul,norm_sub_rev] using
        (physical_defect_forcing hx ht).trans
          (PolynomialOrder.value_le_endpoint forcing envelope_checked.1 ht)) hclose
  exact ⟨⟨p,v,hp,hv,hip,hiv,hdp,fun t ht => by simpa only [one_smul] using hdv t ht⟩,hr⟩

/-- The time profile bounds every prefix of every physical solution with
the declared initial state, not only the constructed existence witness. -/
theorem certifies {x : Vec3} (hx : x 0^2+x 1^2+x 2^2≤(sigma:ℝ)^2) (X : Motion x) :
    ∀ t ∈ Icc (0:ℝ) 1,
      ‖X.p t-position x t‖≤PolynomialOrder.value envelope t ∧
      ‖X.v t-velocity x t‖≤PolynomialOrder.value (differentiate envelope) t := by
  have hK : 0≤(modelInput.K:ℝ) := by exact_mod_cast model_K_nonnegative
  have hclose : PolynomialOrder.value forcing 1*
      PolynomialSupersolution.value (gain:ℝ) 1<(rhoMaximum:ℝ) := by
    have h : ((evaluate forcing 1:ℚ):ℝ)*(HarmonicCertificate.positionGain gain:ℝ)<
        (rhoMaximum:ℝ) := by exact_mod_cast closure_checked
    have he := PolynomialOrder.value_at_rational forcing 1
    norm_num only [Rat.cast_one] at he
    simpa only [he,HarmonicCertificate.positionGain_cast] using h
  have hgain : (1:ℝ)*(2*(modelInput.K:ℝ)/(1-2*(rhoMaximum:ℝ))^3)≤(gain:ℝ) := by
    have h : (exactGain:ℝ)≤(gain:ℝ) := by exact_mod_cast gain_checked.2.2.1
    simpa only [exactGain,Rat.cast_mul,Rat.cast_div,Rat.cast_sub,Rat.cast_pow,
      Rat.cast_ofNat,Rat.cast_one,one_mul] using h
  exact Gravity.polynomial_prediction_curve (modelInput.K:ℝ) 1 hK (by norm_num)
    X.p X.v (position x) (velocity x) (acceleration x) (thrust x)
    forcing envelope envelope_checked gain_checked.1 gain_checked.2.1
    region_positive hclose hgain
    (fun t ht => by linarith [candidate_radius hx ht]) X.continuous_p X.continuous_v
    (position_continuous x) (velocity_continuous x) X.derivative_p
    (fun t ht => by simpa only [one_smul] using X.derivative_v t ht)
    (fun t _ => position_derivative x t) (fun t _ => velocity_derivative x t)
    X.initial_p X.initial_v
    (fun t ht => by simpa only [one_smul,norm_sub_rev] using physical_defect_forcing hx ht)

/-- SI-unit uniform error bounds. The position and velocity scales are the
declared 7,000,000 m reference radius and 120 s duration. -/
theorem physical_prediction {x : Vec3} (hx : x 0^2+x 1^2+x 2^2≤(sigma:ℝ)^2) :
    (∃ X : Motion x, ∀ t ∈ Icc (0:ℝ) 1, 1-2*(rhoMaximum:ℝ)≤‖X.p t‖) ∧
    (∀ X : Motion x, ∀ t ∈ Icc (0:ℝ) 1,
      7000000*‖X.p t-position x t‖≤(positionUpper:ℝ) ∧
      (7000000/120)*‖X.v t-velocity x t‖≤(velocityUpper:ℝ)) := by
  refine ⟨exists_motion hx,?_⟩
  intro X t ht
  have hb := certifies hx X t ht
  have hp := PolynomialOrder.value_le_endpoint envelope envelope_checked.2.1 ht
  have hv := PolynomialOrder.value_le_endpoint (differentiate envelope) envelope_checked.2.2.1 ht
  have ep := PolynomialOrder.value_at_rational envelope 1
  have ev := PolynomialOrder.value_at_rational (differentiate envelope) 1
  norm_num only [Rat.cast_one] at ep ev
  rw [ep] at hp
  rw [ev] at hv
  have hdp : (7000000:ℝ)*((evaluate envelope 1:ℚ):ℝ)≤(positionUpper:ℝ) := by
    exact_mod_cast displayed_bounds.1
  have hdv : (7000000/120:ℝ)*((evaluate (differentiate envelope) 1:ℚ):ℝ)≤(velocityUpper:ℝ) := by
    have h : (((7000000/120)*evaluate (differentiate envelope) 1 : ℚ):ℝ)≤(velocityUpper:ℝ) :=
      Rat.cast_le.mpr displayed_bounds.2
    simpa only [Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] using h
  exact ⟨(mul_le_mul_of_nonneg_left (hb.1.trans hp) (by norm_num)).trans hdp,
    (mul_le_mul_of_nonneg_left (hb.2.trans hv) (by norm_num)).trans hdv⟩

end GNC.OrbitalComparison.JointErrorData
