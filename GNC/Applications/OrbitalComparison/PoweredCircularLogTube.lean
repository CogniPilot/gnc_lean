import GNC.Applications.OrbitalComparison.GeometricSTMPrediction
import GNC.Applications.OrbitalComparison.VaryingRateReference

/-! A concrete ideal-response certificate, with an analytic powered chief.
The constants are physical inputs: Earth mu, 7000 km reference radius,
600 s horizon, 0.1 mm/s^2 acceleration and 0.02 rad attitude uncertainty.
Time and length are nondimensionalized. The 1 mm conclusion is an accuracy
target; no numerical integration tolerance or fitted allowance is used.
This does not verify floating evaluation of the ideal linear response. -/
noncomputable section
namespace GNC.OrbitalComparison.PoweredCircularLogTube
open Set Real Matrix
open GeometricSTMPrediction (E cross force)
open LieRadiusFrame (left)

def lengthScale : ℝ := 7000000
def duration : ℝ := 600
def earthMu : ℝ := 398600441800000
def physicalAcceleration : ℝ := 1/10000
def angleRadius : ℝ := 1/50
def μ : ℝ := earthMu*duration^2/lengthScale^3
def U : ℝ := physicalAcceleration*duration^2/lengthScale
def rate : ℝ := sqrt (μ-U)
def L : ℝ := angleRadius*U*PolynomialSupersolution.value (2*μ) 1
def κ : ℝ := 2*μ/(1-2*L)^3
def F₂ : ℝ := 2*μ*angleRadius*L
def F₄ : ℝ := 4*μ/(1-L)^4*L^2
def errorBudget (t : ℝ) : ℝ :=
  F₂*MonomialSupersolution.value κ 2 t+F₄*MonomialSupersolution.value κ 4 t

theorem μ_nonneg : 0≤μ := by norm_num [μ, earthMu, duration, lengthScale]
theorem U_nonneg : 0≤U := by norm_num [U, physicalAcceleration, duration, lengthScale]
theorem rate_sq : rate^2=μ-U := by
  exact sq_sqrt (by norm_num [μ, U, earthMu, physicalAcceleration, duration, lengthScale])
theorem gain_range : 0≤2*μ ∧ 2*μ<56 := by
  norm_num [μ, earthMu, duration, lengthScale]

theorem checks : 0≤L ∧ 2*L<1 ∧ 0≤κ ∧ κ<56 ∧
    (F₂+F₄)*PolynomialSupersolution.value κ 1<L := by
  norm_num [L, κ, F₂, F₄, μ, U, angleRadius, earthMu, physicalAcceleration,
    duration, lengthScale, PolynomialSupersolution.value, PolynomialSupersolution.polynomial]

theorem submillimeter : lengthScale*errorBudget 1<1/1000 := by
  norm_num [errorBudget, L, κ, F₂, F₄, μ, U, angleRadius, earthMu, physicalAcceleration,
    duration, lengthScale, PolynomialSupersolution.value, PolynomialSupersolution.polynomial,
    MonomialSupersolution.value, MonomialSupersolution.polynomial,
    MonomialSupersolution.pair, MonomialSupersolution.four, MonomialSupersolution.six]

def reference (t : ℝ) : E := VaryingRateReference.position 1 (rate*t)
def referenceVelocity (t : ℝ) : E := VaryingRateReference.velocity 1 (rate*t) rate
def thrust (t : ℝ) : E := U • reference t

theorem reference_norm (t : ℝ) : ‖reference t‖=1 :=
  VaryingRateReference.position_norm 1 (rate*t) (by norm_num)

theorem thrust_model (t : ℝ) :
    VaryingRateReference.thrust μ 1 (rate*t) rate 0=thrust t := by
  simp only [VaryingRateReference.thrust, one_pow, div_one, one_mul, mul_zero, rate_sq]
  have he : μ-(μ-U)=U := by ring
  rw [he]
  simpa [thrust, reference, VaryingRateReference.position] using
    SpatialRotatingFrame.mix_smul (rate*t) U 1 0 0

theorem reference_derivative (t : ℝ) : HasDerivAt reference (referenceVelocity t) t :=
  VaryingRateReference.position_derivative 1 (by simpa using (hasDerivAt_id t).const_mul rate)

theorem reference_velocity_derivative (t : ℝ) :
    HasDerivAt referenceVelocity (Gravity.field μ (reference t)+thrust t) t := by
  have h := VaryingRateReference.physical_velocity_derivative μ 1 (by norm_num)
    (show HasDerivAt (fun s => rate*s) rate t by simpa using (hasDerivAt_id t).const_mul rate)
    (hasDerivAt_const t rate)
  simpa only [thrust_model] using h

theorem thrust_norm (t : ℝ) : ‖thrust t‖=U := by
  rw [thrust, norm_smul, Real.norm_eq_abs, abs_of_nonneg U_nonneg, reference_norm, mul_one]

/-- Uniform over the whole three-dimensional 0.02-radian attitude ball and
all times in the 600 s burn. The actual nonlinear orbit is supplied as a
classical solution; the *prediction error* is proved, never assumed. -/
theorem certificate (φ : Vec3) (hφ : enorm φ≤angleRadius)
    (x xv y yv : ℝ → E) (hx : Continuous x) (hxv : Continuous xv)
    (hy : Continuous y) (hyv : Continuous yv)
    (hdx : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt x (xv t) t)
    (hdxv : ∀ t ∈ Icc (0:ℝ) 1,
      HasDerivAt xv (Gravity.field μ (x t)+force φ (thrust t)) t)
    (hdy : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt y (yv t) t)
    (hdyv : ∀ t ∈ Icc (0:ℝ) 1,
      HasDerivAt yv (Gravity.gradient μ (reference t) (y t)+cross φ (thrust t)) t)
    (hiy : y 0=0) (hiyv : yv 0=0)
    (hix : x 0=reference 0) (hixv : xv 0=referenceVelocity 0) :
    ∀ t ∈ Icc (0:ℝ) 1,
      lengthScale*‖x t-(reference t+left φ (y t))‖<1/1000 := by
  have hshape := GeometricSTMPrediction.response_shape μ 1 angleRadius U μ_nonneg
    (by norm_num) (by norm_num [angleRadius]) U_nonneg (by simpa using gain_range.2)
    φ hφ reference y yv thrust (fun t _ => (reference_norm t).ge)
    (fun t _ => (thrust_norm t).le) hy hyv hdy hdyv hiy hiyv
  have hcq : Continuous reference := continuous_iff_continuousAt.mpr
    (fun t => (reference_derivative t).continuousAt)
  have hcqv : Continuous referenceVelocity := continuous_iff_continuousAt.mpr
    (fun t => (reference_velocity_derivative t).continuousAt)
  have h := GeometricSTMPrediction.certificate μ 1 L angleRadius κ μ_nonneg (by norm_num)
    checks.1 checks.2.1 (by norm_num [angleRadius]) (by norm_num [angleRadius])
    checks.2.2.1 checks.2.2.2.1 le_rfl
    (by simpa [F₂, F₄] using checks.2.2.2.2)
    φ hφ x xv reference referenceVelocity y yv thrust
    (fun t _ => (reference_norm t).ge) (by simpa [L] using hshape)
    hx hxv hcq hcqv hy hyv hdx hdxv
    (fun t _ => reference_derivative t) (fun t _ => reference_velocity_derivative t)
    hdy hdyv (by simp [hiy, hix]) (by simp [hiyv, hixv])
  have hμ := μ_nonneg
  have hL := checks.1
  have hf2 : 0≤F₂ := by unfold F₂ angleRadius; positivity
  have hf4 : 0≤F₄ := by unfold F₄; positivity
  intro t ht
  have hb : ‖x t-(reference t+left φ (y t))‖≤errorBudget t := by
    simpa [errorBudget, F₂, F₄] using (h t ht).1
  have he : errorBudget t≤errorBudget 1 := add_le_add
    (mul_le_mul_of_nonneg_left (MonomialSupersolution.value_le_endpoint 2 checks.2.2.1 checks.2.2.2.1 ht) hf2)
    (mul_le_mul_of_nonneg_left (MonomialSupersolution.value_le_endpoint 4 checks.2.2.1 checks.2.2.2.1 ht) hf4)
  exact (mul_le_mul_of_nonneg_left (hb.trans he) (by norm_num [lengthScale])).trans_lt submillimeter

end GNC.OrbitalComparison.PoweredCircularLogTube
