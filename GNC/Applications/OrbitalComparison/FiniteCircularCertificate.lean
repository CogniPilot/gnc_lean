import GNC.Applications.OrbitalComparison.FiniteCircularResponse
import GNC.Applications.OrbitalComparison.FiniteGeometricPrediction
import GNC.Lie.JacobianAffine

/-! A concrete finite polynomial predictor, certified against the full
nonlinear inverse-square physical ODE for the entire three-dimensional
pointing ball. Only the actual spacecraft trajectory is supplied; neither
an exact response nor an assumed numerical residual is an input. -/
noncomputable section
namespace GNC.OrbitalComparison.FiniteCircularCertificate
open Set
open PoweredCircularLogTube (μ U angleRadius rate reference referenceVelocity thrust lengthScale)
open GeometricSTMPrediction (E cross force)
open LieRadiusFrame (left)
open FiniteCircularResponse (position velocity acceleration)
open FiniteResponseData (responseRadius gain error F2 F4 predictionBudget reconstructionTail)

def prediction (φ : Vec3) (t : ℝ) : E := reference t+
  WithLp.toLp 2 (JacobianAffine.apply φ (position φ t).ofLp)

theorem input_casts : (FiniteResponseData.mu:ℝ)=μ ∧ (FiniteResponseData.thrust:ℝ)=U ∧
    (FiniteResponseData.theta:ℝ)=angleRadius := by
  norm_num [FiniteResponseData.mu, FiniteResponseData.thrust, FiniteResponseData.theta,
    PoweredCircularLogTube.μ, PoweredCircularLogTube.U, PoweredCircularLogTube.angleRadius,
    PoweredCircularLogTube.earthMu, PoweredCircularLogTube.physicalAcceleration,
    PoweredCircularLogTube.duration, PoweredCircularLogTube.lengthScale]

theorem radius_identity : (responseRadius:ℝ)=
    (angleRadius*U+(error:ℝ))*PolynomialSupersolution.value (2*μ) 1 := by
  simp only [FiniteResponseData.responseRadius, Rat.cast_mul, Rat.cast_add]
  rw [MonomialRational.cast_constant, input_casts.2.1, input_casts.2.2]
  simp only [Rat.cast_mul, Rat.cast_ofNat, input_casts.1]

theorem gain_identity : (gain:ℝ)=2*μ/(1-2*(responseRadius:ℝ))^3 := by
  simp only [FiniteResponseData.gain, Rat.cast_div, Rat.cast_mul, Rat.cast_sub,
    Rat.cast_pow, Rat.cast_ofNat, Rat.cast_one, input_casts.1]

theorem force_casts : (F2:ℝ)=2*μ*angleRadius*(responseRadius:ℝ) ∧
    (F4:ℝ)=4*μ/(1-(responseRadius:ℝ))^4*(responseRadius:ℝ)^2 := by
  simp only [FiniteResponseData.F2, FiniteResponseData.F4, Rat.cast_mul, Rat.cast_div,
    Rat.cast_pow, Rat.cast_sub, Rat.cast_one, Rat.cast_ofNat, input_casts.1, input_casts.2.2,
    and_self]

theorem checked_closure : ((error:ℝ)+2*μ*angleRadius*(responseRadius:ℝ)+
    4*μ/(1-(responseRadius:ℝ))^4*(responseRadius:ℝ)^2)*
      PolynomialSupersolution.value (gain:ℝ) 1<(responseRadius:ℝ) := by
  have h : ((error+F2+F4:ℚ):ℝ)*(MonomialRational.endpoint gain 0:ℝ)<(responseRadius:ℝ) := by
    exact_mod_cast FiniteResponseData.closure.2.2.2.2
  simpa only [Rat.cast_add, MonomialRational.cast_constant, force_casts.1, force_casts.2] using h

theorem tail_identity : (reconstructionTail:ℝ)=JacobianAffine.tail angleRadius := by
  norm_num [FiniteResponseData.reconstructionTail, FiniteResponseData.theta,
    JacobianAffine.tail, LieRadiusQuadratic.tail, PoweredCircularLogTube.angleRadius]

/-- Hard all-time position bound for an explicitly given degree-seven
polynomial and affine Jacobian reconstruction. The force is Q times the
prescribed reference thrust, Q=Exp(phi), with arbitrary axis ||phi||<=0.02.
The reference has radius 7000 km and acceleration 0.1 mm/s^2 for 600 s.
The result is a real-arithmetic certificate; IEEE rounding is a separate cost. -/
theorem certificate (φ : Vec3) (hφ : enorm φ≤angleRadius) (x xv : ℝ → E)
    (hx : Continuous x) (hxv : Continuous xv)
    (hdx : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt x (xv t) t)
    (hdxv : ∀ t ∈ Icc (0:ℝ) 1,
      HasDerivAt xv (Gravity.field μ (x t)+force φ (thrust t)) t)
    (hix : x 0=reference 0) (hixv : xv 0=referenceVelocity 0) :
    ∀ t ∈ Icc (0:ℝ) 1, ‖x t-prediction φ t‖≤(predictionBudget:ℝ)+(reconstructionTail:ℝ)*(responseRadius:ℝ) := by
  have hR : 0≤(responseRadius:ℝ) := by exact_mod_cast FiniteResponseData.closure.1
  have hregion : 2*(responseRadius:ℝ)<1 := by exact_mod_cast FiniteResponseData.closure.2.1
  have hk0 : 0≤(gain:ℝ) := by exact_mod_cast FiniteResponseData.closure.2.2.1
  have hk : (gain:ℝ)<56 := by exact_mod_cast FiniteResponseData.closure.2.2.2.1
  have he0 : 0≤(error:ℝ) := by exact_mod_cast FiniteResponseData.budgets_nonneg.2.2.2
  have hμ := PoweredCircularLogTube.μ_nonneg
  have hU := PoweredCircularLogTube.U_nonneg
  have hθ : 0≤angleRadius := by norm_num [PoweredCircularLogTube.angleRadius]
  have hθ1 : angleRadius≤1 := by norm_num [PoweredCircularLogTube.angleRadius]
  have hy : Continuous (position φ) := continuous_iff_continuousAt.mpr
    (fun t => (FiniteCircularResponse.position_derivative φ t).continuousAt)
  have hyv : Continuous (velocity φ) := continuous_iff_continuousAt.mpr
    (fun t => (FiniteCircularResponse.velocity_derivative φ t).continuousAt)
  have hcq : Continuous reference := continuous_iff_continuousAt.mpr
    (fun t => (PoweredCircularLogTube.reference_derivative t).continuousAt)
  have hcqv : Continuous referenceVelocity := continuous_iff_continuousAt.mpr
    (fun t => (PoweredCircularLogTube.reference_velocity_derivative t).continuousAt)
  have hshape := Gravity.response_shape_of_defect μ 1 (angleRadius*U) (error:ℝ) 6 hμ
    (by norm_num) (mul_nonneg hθ hU) he0 (by simpa using PoweredCircularLogTube.gain_range.2)
    reference (position φ) (velocity φ) (acceleration φ) (fun t => cross φ (thrust t))
    (fun t _ => (PoweredCircularLogTube.reference_norm t).ge) (by
      intro t _
      have h := cross_enorm_le φ (thrust t).ofLp
      change ‖cross φ (thrust t)‖≤enorm φ*‖thrust t‖ at h
      rw [PoweredCircularLogTube.thrust_norm] at h
      exact h.trans (mul_le_mul_of_nonneg_right hφ hU))
    (fun _ ht => FiniteCircularResponse.residual_bound φ hφ ht) hy hyv
    (fun t _ => FiniteCircularResponse.position_derivative φ t)
    (fun t _ => FiniteCircularResponse.velocity_derivative φ t)
    (FiniteCircularResponse.position_initial φ) (FiniteCircularResponse.velocity_initial φ)
  have hb : ∀ t ∈ Icc (0:ℝ) 1, ‖position φ t‖≤(responseRadius:ℝ)*t^2 := by
    simpa only [one_pow, div_one, ←radius_identity] using hshape
  have hcert := FiniteGeometricPrediction.certificate μ 1 (responseRadius:ℝ) angleRadius
    (gain:ℝ) (error:ℝ) 6 hμ (by norm_num) hR hregion hθ hθ1 he0 hk0 hk
    (by simpa using gain_identity.ge) (by simpa using checked_closure)
    φ hφ x xv reference referenceVelocity (position φ) (velocity φ) (acceleration φ) thrust
    (fun t _ => (PoweredCircularLogTube.reference_norm t).ge) hb
    (fun _ ht => FiniteCircularResponse.residual_bound φ hφ ht)
    hx hxv hcq hcqv hy hyv hdx hdxv
    (fun t _ => PoweredCircularLogTube.reference_derivative t)
    (fun t _ => PoweredCircularLogTube.reference_velocity_derivative t)
    (fun t _ => FiniteCircularResponse.position_derivative φ t)
    (fun t _ => FiniteCircularResponse.velocity_derivative φ t)
    (by simp [hix, FiniteCircularResponse.position_initial])
    (by simp [hixv, FiniteCircularResponse.velocity_initial])
  have hf2 : 0≤(F2:ℝ) := by rw [force_casts.1]; positivity
  have hf4 : 0≤(F4:ℝ) := by rw [force_casts.2]; positivity
  intro t ht
  have hideal : ‖x t-(reference t+left φ (position φ t))‖≤(predictionBudget:ℝ) := by
    have hc := (hcert t ht).1
    simp only [one_pow, div_one, ←force_casts.1, ←force_casts.2] at hc
    refine hc.trans ?_
    have h6 := mul_le_mul_of_nonneg_left (MonomialSupersolution.value_le_endpoint 6 hk0 hk ht) he0
    have h2 := mul_le_mul_of_nonneg_left (MonomialSupersolution.value_le_endpoint 2 hk0 hk ht) hf2
    have h4 := mul_le_mul_of_nonneg_left (MonomialSupersolution.value_le_endpoint 4 hk0 hk ht) hf4
    simpa only [FiniteResponseData.predictionBudget, Rat.cast_add, Rat.cast_mul,
      MonomialRational.cast_endpoint] using add_le_add (add_le_add h6 h2) h4
  have hyR := (hb t ht).trans (mul_le_of_le_one_right hR (pow_le_one₀ ht.1 ht.2))
  have ha := JacobianAffine.prediction_bound φ (x t).ofLp (reference t).ofLp (position φ t).ofLp
    hφ hyR hideal
  have hfinal : ‖x t-prediction φ t‖≤(predictionBudget:ℝ)+(reconstructionTail:ℝ)*(responseRadius:ℝ) := by
    simpa only [prediction, tail_identity] using ha
  exact hfinal

/-- The explicit finite predictor meets the stated physical accuracy target. -/
theorem submillimeter (φ : Vec3) (hφ : enorm φ≤angleRadius) (x xv : ℝ → E)
    (hx : Continuous x) (hxv : Continuous xv)
    (hdx : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt x (xv t) t)
    (hdxv : ∀ t ∈ Icc (0:ℝ) 1,
      HasDerivAt xv (Gravity.field μ (x t)+force φ (thrust t)) t)
    (hix : x 0=reference 0) (hixv : xv 0=referenceVelocity 0) :
    ∀ t ∈ Icc (0:ℝ) 1, lengthScale*‖x t-prediction φ t‖<1/1000 := by
  have htarget : (7000000:ℝ)*((predictionBudget:ℝ)+(reconstructionTail:ℝ)*(responseRadius:ℝ))<1/1000 := by
    have h := (Rat.cast_lt (K := ℝ)).mpr FiniteResponseData.submillimeter
    simpa only [Rat.cast_mul, Rat.cast_add, Rat.cast_div, Rat.cast_ofNat, Rat.cast_one] using h
  intro t ht
  exact (mul_le_mul_of_nonneg_left (certificate φ hφ x xv hx hxv hdx hdxv hix hixv t ht)
    (by norm_num [lengthScale])).trans_lt htarget

end GNC.OrbitalComparison.FiniteCircularCertificate
