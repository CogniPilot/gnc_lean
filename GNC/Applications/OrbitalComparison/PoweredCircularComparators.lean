import GNC.Applications.OrbitalComparison.PoweredCircularLogTube
import GNC.Lie.RotationTaylorBound
import GNC.Dynamics.RotationCenteredError

/-! Matched Cartesian certificates for the powered circular example.
The bound comparison is between sufficient analytic envelopes, not a lower
bound on any method's true error. The exact-component baseline has the
smaller gravity-only envelope and must not be hidden in a coordinate claim.
-/
noncomputable section
namespace GNC.OrbitalComparison.PoweredCircularComparators
open Set Real
open PoweredCircularLogTube
open GeometricSTMPrediction (E force cross)

def angleDefect : ℝ := angleRadius^2/2*U
def gravityDefect : ℝ := 3*μ/(1-L)^4*L^2
def budget (ε t : ℝ) : ℝ := ε*MonomialSupersolution.value κ 0 t+
  gravityDefect*MonomialSupersolution.value κ 4 t

theorem numerical_checks : 0≤angleDefect ∧
    (angleDefect+gravityDefect)*PolynomialSupersolution.value κ 1<L ∧
    6*errorBudget 1<budget angleDefect 1 ∧
    budget 0 1<errorBudget 1 ∧
    lengthScale*budget angleDefect 1<4/1000 ∧ lengthScale*budget 0 1<1/1000000000 := by
  norm_num [budget, angleDefect, gravityDefect, errorBudget, L, κ, F₂, F₄, μ, U,
    angleRadius, earthMu, physicalAcceleration, duration, lengthScale,
    PolynomialSupersolution.value, PolynomialSupersolution.polynomial,
    MonomialSupersolution.value, MonomialSupersolution.polynomial,
    MonomialSupersolution.pair, MonomialSupersolution.four, MonomialSupersolution.six]

/-- Outward-rounded display bounds: 0.554 mm, 3.859 mm, and 0.904 nm.
These are checked consequences of the exact formulas, not allowances. -/
theorem reported_bounds : lengthScale*errorBudget 1≤554/1000000 ∧
    lengthScale*budget angleDefect 1≤3859/1000000 ∧
    lengthScale*budget 0 1≤904/1000000000000 := by
  norm_num [budget, angleDefect, gravityDefect, errorBudget, L, κ, F₂, F₄, μ, U,
    angleRadius, earthMu, physicalAcceleration, duration, lengthScale,
    PolynomialSupersolution.value, PolynomialSupersolution.polynomial,
    MonomialSupersolution.value, MonomialSupersolution.polynomial,
    MonomialSupersolution.pair, MonomialSupersolution.four, MonomialSupersolution.six]

theorem budget_le_endpoint {ε t : ℝ} (hε : 0≤ε) (ht : t ∈ Icc (0:ℝ) 1) :
    budget ε t≤budget ε 1 := by
  have hμ := μ_nonneg
  have hL := checks.1
  exact add_le_add
    (mul_le_mul_of_nonneg_left
      (MonomialSupersolution.value_le_endpoint 0 checks.2.2.1 checks.2.2.2.1 ht) hε)
    (mul_le_mul_of_nonneg_left
      (MonomialSupersolution.value_le_endpoint 4 checks.2.2.1 checks.2.2.2.1 ht)
      (by unfold gravityDefect; positivity))

theorem reported_cartesian_bounds_on {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    lengthScale*budget angleDefect t≤3859/1000000 ∧
    lengthScale*budget 0 t≤904/1000000000000 := by
  have hl : 0≤lengthScale := by norm_num [lengthScale]
  exact ⟨(mul_le_mul_of_nonneg_left (budget_le_endpoint numerical_checks.1 ht) hl).trans reported_bounds.2.1,
    (mul_le_mul_of_nonneg_left (budget_le_endpoint (by norm_num) ht) hl).trans reported_bounds.2.2⟩

theorem angle_input_bound (φ : Vec3) (hφ : enorm φ≤angleRadius) (t : ℝ) :
    ‖force φ (thrust t)-thrust t-cross φ (thrust t)‖≤angleDefect := by
  have h := RotationTaylorBound.bound φ (thrust t).ofLp
  change ‖force φ (thrust t)-thrust t-cross φ (thrust t)‖≤enorm φ^2/2*‖thrust t‖ at h
  rw [thrust_norm] at h
  exact h.trans (mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right (pow_le_pow_left₀ (enorm_nonneg _) hφ 2) (by norm_num)) U_nonneg)

theorem input_sizes (φ : Vec3) (hφ : enorm φ≤angleRadius) (t : ℝ) :
    ‖cross φ (thrust t)‖≤angleRadius*U ∧
    ‖force φ (thrust t)-thrust t‖≤angleRadius*U := by
  have ht := thrust_norm t
  have hc := cross_enorm_le φ (thrust t).ofLp
  have he := RotationCenteredError.rotation_difference_bound φ (thrust t).ofLp
    (hφ.trans_lt (by norm_num [angleRadius]; linarith [pi_gt_three]))
  change ‖cross φ (thrust t)‖≤enorm φ*‖thrust t‖ at hc
  change ‖force φ (thrust t)-thrust t‖≤enorm φ*‖thrust t‖ at he
  rw [ht] at hc he
  exact ⟨hc.trans (mul_le_mul_of_nonneg_right hφ U_nonneg),
    he.trans (mul_le_mul_of_nonneg_right hφ U_nonneg)⟩

/-- Set du=cross(phi,u), epsilon=angleDefect for the angle STM; set
du=Rot(phi)u-u, epsilon=0 for the exact-component STM. `input_sizes` and
`angle_input_bound` discharge the input checks uniformly over the ball. -/
theorem certificate (φ : Vec3) (x xv y yv du : ℝ → E) {ε : ℝ}
    (hε : 0≤ε) (hεmax : ε≤angleDefect)
    (hu : ∀ t ∈ Icc (0:ℝ) 1, ‖du t‖≤angleRadius*U)
    (he : ∀ t ∈ Icc (0:ℝ) 1, ‖force φ (thrust t)-thrust t-du t‖≤ε)
    (hx : Continuous x) (hxv : Continuous xv) (hy : Continuous y) (hyv : Continuous yv)
    (hdx : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt x (xv t) t)
    (hdxv : ∀ t ∈ Icc (0:ℝ) 1,
      HasDerivAt xv (Gravity.field μ (x t)+force φ (thrust t)) t)
    (hdy : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt y (yv t) t)
    (hdyv : ∀ t ∈ Icc (0:ℝ) 1,
      HasDerivAt yv (Gravity.gradient μ (reference t) (y t)+du t) t)
    (hiy : y 0=0) (hiyv : yv 0=0)
    (hix : x 0=reference 0) (hixv : xv 0=referenceVelocity 0) :
    ∀ t ∈ Icc (0:ℝ) 1, ‖x t-(reference t+y t)‖≤budget ε t := by
  have hμ := μ_nonneg
  have hL := checks.1
  have hb := PolynomialSupersolution.bounds checks.2.2.1 checks.2.2.2.1
    (show (1:ℝ) ∈ Icc 0 1 by norm_num)
  have hclose : (ε+gravityDefect)*PolynomialSupersolution.value κ 1<L :=
    (mul_le_mul_of_nonneg_right (add_le_add hεmax le_rfl) hb.1).trans_lt numerical_checks.2.1
  have hshape := Gravity.retained_response_shape μ 1 (angleRadius*U) μ_nonneg
    (by norm_num) (mul_nonneg (by norm_num [angleRadius]) U_nonneg)
    (by simpa using gain_range.2) reference y yv du
    (fun t _ => (reference_norm t).ge) hu hy hyv hdy hdyv hiy hiyv
  have h := Gravity.retained_monomial_prediction μ 1 L ε κ μ_nonneg hL checks.2.1
    hε checks.2.2.1 checks.2.2.2.1 le_rfl hclose x xv reference referenceVelocity
    y yv thrust du (fun t => force φ (thrust t)-thrust t)
    (fun t _ => (reference_norm t).ge) (by simpa [L] using hshape) he
    hx hxv (continuous_iff_continuousAt.mpr (fun t => (reference_derivative t).continuousAt))
    (continuous_iff_continuousAt.mpr (fun t => (reference_velocity_derivative t).continuousAt))
    hy hyv hdx (by simpa using hdxv)
    (fun t _ => reference_derivative t) (fun t _ => reference_velocity_derivative t)
    hdy hdyv (by simp [hix, hiy]) (by simp [hixv, hiyv])
  exact fun t ht => (h t ht).1

end GNC.OrbitalComparison.PoweredCircularComparators
