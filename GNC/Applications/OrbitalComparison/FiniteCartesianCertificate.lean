import GNC.Applications.OrbitalComparison.FiniteCartesianResponse
import GNC.Applications.OrbitalComparison.FiniteCircularCertificate

/-! Matched physical certificates for the finite Cartesian competitors.
Identical actual trajectories, reference, attitude ball, residual checker,
first-exit closure and accuracy target are used by both coordinate methods.
No rounding or optimal-cost claim is implied. -/
noncomputable section
namespace GNC.OrbitalComparison.FiniteCartesianCertificate
open Set
open PoweredCircularLogTube (μ U angleRadius reference referenceVelocity thrust lengthScale)
open GeometricSTMPrediction (E force)
open FiniteCartesianData (Variant responseRadius gain inputError error F4 predictionBudget)
open FiniteCartesianResponse (position velocity acceleration)
open FiniteCircularCertificate (input_casts)

def prediction (v : Variant) (φ : Vec3) (t : ℝ) : E := reference t+position v φ t

theorem radius_identity (v : Variant) : (responseRadius v:ℝ)=
    (angleRadius*U+(inputError v:ℝ)+(error v:ℝ))*PolynomialSupersolution.value (2*μ) 1 := by
  simp only [FiniteCartesianData.responseRadius, Rat.cast_mul, Rat.cast_add]
  rw [MonomialRational.cast_constant, input_casts.2.1, input_casts.2.2]
  simp only [Rat.cast_mul, Rat.cast_ofNat, input_casts.1]

theorem gain_identity (v : Variant) : (gain v:ℝ)=2*μ/(1-2*(responseRadius v:ℝ))^3 := by
  simp only [FiniteCartesianData.gain, Rat.cast_div, Rat.cast_mul, Rat.cast_sub,
    Rat.cast_pow, Rat.cast_ofNat, Rat.cast_one, input_casts.1]

theorem force_cast (v : Variant) :
    (F4 v:ℝ)=3*μ/(1-(responseRadius v:ℝ))^4*(responseRadius v:ℝ)^2 := by
  simp only [FiniteCartesianData.F4, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_sub, Rat.cast_one, Rat.cast_ofNat, input_casts.1]

theorem checked_closure (v : Variant) : ((inputError v:ℝ)+(error v:ℝ)+
    3*μ/(1-(responseRadius v:ℝ))^4*(responseRadius v:ℝ)^2)*
      PolynomialSupersolution.value (gain v:ℝ) 1<(responseRadius v:ℝ) := by
  have h : ((inputError v+error v+F4 v:ℚ):ℝ)*(MonomialRational.endpoint (gain v) 0:ℝ)<
      (responseRadius v:ℝ) := by exact_mod_cast (FiniteCartesianData.closure v).2.2.2.2
  simpa only [Rat.cast_add, MonomialRational.cast_constant, force_cast] using h

/-- Uniform nonlinear physical prediction bound for either exact-component
or quadratic-angle features, with an explicit degree-eight time polynomial. -/
theorem certificate (v : Variant) (φ : Vec3) (hφ : enorm φ≤angleRadius) (x xv : ℝ → E)
    (hx : Continuous x) (hxv : Continuous xv)
    (hdx : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt x (xv t) t)
    (hdxv : ∀ t ∈ Icc (0:ℝ) 1,
      HasDerivAt xv (Gravity.field μ (x t)+force φ (thrust t)) t)
    (hix : x 0=reference 0) (hixv : xv 0=referenceVelocity 0) :
    ∀ t ∈ Icc (0:ℝ) 1, ‖x t-prediction v φ t‖≤(predictionBudget v:ℝ) := by
  have hR : 0≤(responseRadius v:ℝ) := by exact_mod_cast (FiniteCartesianData.closure v).1
  have hregion : 2*(responseRadius v:ℝ)<1 := by exact_mod_cast (FiniteCartesianData.closure v).2.1
  have hk0 : 0≤(gain v:ℝ) := by exact_mod_cast (FiniteCartesianData.closure v).2.2.1
  have hk : (gain v:ℝ)<56 := by exact_mod_cast (FiniteCartesianData.closure v).2.2.2.1
  have he0 : 0≤(error v:ℝ) := by exact_mod_cast (FiniteCartesianData.nonnegative v).2.2.1
  have hd0 : 0≤(inputError v:ℝ) := by exact_mod_cast (FiniteCartesianData.nonnegative v).2.2.2
  have hμ := PoweredCircularLogTube.μ_nonneg
  have hU := PoweredCircularLogTube.U_nonneg
  have hθ : 0≤angleRadius := by norm_num [PoweredCircularLogTube.angleRadius]
  have hθpi : angleRadius<2*Real.pi := by
    norm_num [PoweredCircularLogTube.angleRadius]
    linarith [Real.pi_gt_three]
  have hy : Continuous (position v φ) := continuous_iff_continuousAt.mpr
    (fun t => (FiniteCartesianResponse.position_derivative v φ t).continuousAt)
  have hyv : Continuous (velocity v φ) := continuous_iff_continuousAt.mpr
    (fun t => (FiniteCartesianResponse.velocity_derivative v φ t).continuousAt)
  have hcq : Continuous reference := continuous_iff_continuousAt.mpr
    (fun t => (PoweredCircularLogTube.reference_derivative t).continuousAt)
  have hcqv : Continuous referenceVelocity := continuous_iff_continuousAt.mpr
    (fun t => (PoweredCircularLogTube.reference_velocity_derivative t).continuousAt)
  have hshape := Gravity.response_shape_of_defect μ 1 (angleRadius*U)
    ((inputError v:ℝ)+(error v:ℝ)) 0 hμ (by norm_num) (mul_nonneg hθ hU) (add_nonneg hd0 he0)
    (by simpa using PoweredCircularLogTube.gain_range.2)
    reference (position v φ) (velocity v φ) (acceleration v φ) (fun t => force φ (thrust t)-thrust t)
    (fun t _ => (PoweredCircularLogTube.reference_norm t).ge) (by
      intro t _
      have h := RotationFeatureBounds.exact_norm φ (thrust t).ofLp hφ hθpi
      rw [RotationFeatureBounds.exact_apply] at h
      change ‖force φ (thrust t)-thrust t‖≤angleRadius*‖thrust t‖ at h
      simpa only [PoweredCircularLogTube.thrust_norm] using h) (by
      intro t ht
      have h := FiniteCartesianResponse.physical_residual v φ hφ ht
      have hpow := mul_le_of_le_one_right he0 (pow_le_one₀ ht.1 ht.2 : t^7≤1)
      simpa only [pow_zero, mul_one] using h.trans (add_le_add_right hpow (inputError v:ℝ)))
    hy hyv (fun t _ => FiniteCartesianResponse.position_derivative v φ t)
    (fun t _ => FiniteCartesianResponse.velocity_derivative v φ t)
    (FiniteCartesianResponse.position_initial v φ) (FiniteCartesianResponse.velocity_initial v φ)
  have hb : ∀ t ∈ Icc (0:ℝ) 1, ‖position v φ t‖≤(responseRadius v:ℝ)*t^2 := by
    simpa only [one_pow, div_one, radius_identity, add_assoc] using hshape
  have hcert := Gravity.retained_finite_prediction μ 1 (responseRadius v:ℝ)
    (inputError v:ℝ) (error v:ℝ) (gain v:ℝ) 7 hμ hR hregion hd0 he0 hk0 hk
    (by simpa using (gain_identity v).ge) (by simpa using checked_closure v)
    x xv reference referenceVelocity (position v φ) (velocity v φ) (acceleration v φ) thrust
    (fun t => force φ (thrust t)-thrust t)
    (fun t _ => (PoweredCircularLogTube.reference_norm t).ge) hb
    (fun _ ht => FiniteCartesianResponse.physical_residual v φ hφ ht)
    hx hxv hcq hcqv hy hyv hdx (by intro t ht; simpa using hdxv t ht)
    (fun t _ => PoweredCircularLogTube.reference_derivative t)
    (fun t _ => PoweredCircularLogTube.reference_velocity_derivative t)
    (fun t _ => FiniteCartesianResponse.position_derivative v φ t)
    (fun t _ => FiniteCartesianResponse.velocity_derivative v φ t)
    (by simp [hix, FiniteCartesianResponse.position_initial])
    (by simp [hixv, FiniteCartesianResponse.velocity_initial])
  have hf4 : 0≤(F4 v:ℝ) := by rw [force_cast]; positivity
  intro t ht
  have hc := (hcert t ht).1
  simp only [one_pow, div_one, ←force_cast] at hc
  refine hc.trans ?_
  have h0 := mul_le_mul_of_nonneg_left (MonomialSupersolution.value_le_endpoint 0 hk0 hk ht) hd0
  have h7 := mul_le_mul_of_nonneg_left (MonomialSupersolution.value_le_endpoint 7 hk0 hk ht) he0
  have h4 := mul_le_mul_of_nonneg_left (MonomialSupersolution.value_le_endpoint 4 hk0 hk ht) hf4
  simpa only [FiniteCartesianData.predictionBudget, Rat.cast_add, Rat.cast_mul,
    MonomialRational.cast_endpoint] using add_le_add (add_le_add h0 h7) h4

/-- Same 1 mm / 600 s target and full attitude ball as the geometric theorem. -/
theorem submillimeter (v : Variant) (φ : Vec3) (hφ : enorm φ≤angleRadius) (x xv : ℝ → E)
    (hx : Continuous x) (hxv : Continuous xv)
    (hdx : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt x (xv t) t)
    (hdxv : ∀ t ∈ Icc (0:ℝ) 1,
      HasDerivAt xv (Gravity.field μ (x t)+force φ (thrust t)) t)
    (hix : x 0=reference 0) (hixv : xv 0=referenceVelocity 0) :
    ∀ t ∈ Icc (0:ℝ) 1, lengthScale*‖x t-prediction v φ t‖<1/1000 := by
  have htarget : (7000000:ℝ)*(predictionBudget v:ℝ)<1/1000 := by
    have h := (Rat.cast_lt (K := ℝ)).mpr (FiniteCartesianData.submillimeter v)
    simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat, Rat.cast_one] using h
  intro t ht
  exact (mul_le_mul_of_nonneg_left
    (certificate v φ hφ x xv hx hxv hdx hdxv hix hixv t ht)
    (by norm_num [lengthScale])).trans_lt htarget

end GNC.OrbitalComparison.FiniteCartesianCertificate
