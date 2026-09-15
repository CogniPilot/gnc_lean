import GNC.Control.ReferenceSupport
import GNC.Control.PointingAngle

/-! Finite-horizon directional bounds for time-varying pointing disturbances.

The actual error ODE and the adjoint ODE are hypotheses. No infinite-horizon
stability, sensor-fault-to-attitude gain, or assumed nonlinear tube closure
is asserted. A regional proof must discharge the residual supply bound.
Unlike a coherent constant pointing parameter, a time-varying direction
is bounded inside the response integral.
-/
noncomputable section
open Matrix MeasureTheory Set
namespace GNC.ThrustSupport

/-- Fixed-magnitude pointing uncertainty causes a one-sided axial error.
The reference and actual directions are physical unit vectors. -/
theorem axial_acceleration_bounds (n q : Vec3) {κ a : ℝ}
    (hn : n ⬝ᵥ n = 1) (hq : q ∈ Cap n κ) (ha : 0 ≤ a) :
    -a*(1-κ) ≤ n ⬝ᵥ (a • (q-n)) ∧ n ⬝ᵥ (a • (q-n)) ≤ 0 := by
  have hu := dot_le_enorm n q
  rw [unit_enorm n hn, unit_enorm q hq.1, one_mul] at hu
  simp only [dotProduct_smul, dotProduct_sub, hn, smul_eq_mul]
  constructor <;> nlinarith [mul_le_mul_of_nonneg_left hq.2 ha,
    mul_le_mul_of_nonneg_left hu ha]

/-- A directional thrust-error support bound retains the spherical cap.
Taking a norm ball is an optional relaxation, not a property of the input. -/
theorem cap_error_support (n h q : Vec3) {κ ell : ℝ}
    (hq : q ∈ Cap n κ) (hell : 0 ≤ ell) :
    h ⬝ᵥ (q-n) ≤ dualBound n h κ ell-h ⬝ᵥ n := by
  rw [dotProduct_sub]
  exact sub_le_sub_right (cap_support_bound n h q κ ell hq hell) _

/-- Separate actual thrust-magnitude error from the pointing contribution.
They may be correlated; the identity makes no independence assumption. -/
theorem thrust_error_split (n q : Vec3) (a nominal : ℝ) :
    a • q-nominal • n = nominal • (q-n)+(a-nominal) • q := by
  ext i
  simp
  ring

/-- Joint magnitude/pointing envelope, valid for every combination in the
stated bounds. An identified joint disturbance set may give a tighter bound. -/
theorem magnitude_pointing_error (n q : Vec3) {a nominal δ α : ℝ}
    (hn : n ⬝ᵥ n = 1) (hq : q ∈ Cap n (Real.cos α))
    (ha : 0 ≤ nominal) (hα : 0 ≤ α) (hπ : α ≤ Real.pi)
    (hδ : |a-nominal| ≤ δ) :
    enorm (a • q-nominal • n) ≤ δ+2*nominal*Real.sin (α/2) := by
  rw [thrust_error_split]
  have hs := enorm_add_le (nominal • (q-n)) ((a-nominal) • q)
  rw [enorm_smul (a-nominal) q, unit_enorm q hq.1, mul_one] at hs
  have hp := acceleration_angle_error n q hn hq hα hπ ha
  linarith

/-- Integrating an arbitrary pointing history preserves the one-sided axial
loss. The reference direction may change: this is accumulated instantaneous
thrust-axis loss, not a claim about final orbital position or inertial delta-v. -/
theorem accumulated_axial_loss (n q : ℝ → Vec3) (a κ : ℝ → ℝ) {T : ℝ}
    (hT : 0 ≤ T) (hn : ∀ t ∈ Icc (0:ℝ) T, n t ⬝ᵥ n t = 1)
    (hq : ∀ t ∈ Icc (0:ℝ) T, q t ∈ Cap (n t) (κ t))
    (ha : ∀ t ∈ Icc (0:ℝ) T, 0 ≤ a t)
    (hi : IntervalIntegrable (fun t => -(n t ⬝ᵥ (a t • (q t-n t)))) volume 0 T)
    (hb : IntervalIntegrable (fun t => a t*(1-κ t)) volume 0 T) :
    0 ≤ (∫ t in (0:ℝ)..T, -(n t ⬝ᵥ (a t • (q t-n t)))) ∧
      (∫ t in (0:ℝ)..T, -(n t ⬝ᵥ (a t • (q t-n t)))) ≤
        ∫ t in (0:ℝ)..T, a t*(1-κ t) := by
  constructor
  · apply intervalIntegral.integral_nonneg hT
    intro t ht
    exact neg_nonneg.mpr (axial_acceleration_bounds (n t) (q t) (hn t ht) (hq t ht) (ha t ht)).2
  · apply intervalIntegral.integral_mono_on hT hi hb
    intro t ht
    have h := (axial_acceleration_bounds (n t) (q t) (hn t ht) (hq t ht) (ha t ht)).1
    linarith

/-- Equal positive and negative tilts cancel transverse thrust, but their
mean retains the axial loss. This is an exact force identity. -/
theorem opposite_tilts_mean (θ a : ℝ) :
    (1/2 : ℝ) • (a • ![Real.cos θ, Real.sin θ, 0] +
      a • ![Real.cos (-θ), Real.sin (-θ), 0])-a • ![1,0,0] =
        (-a*(1-Real.cos θ)) • ![1,0,0] := by
  ext i
  fin_cases i
  · simp
    ring
  · simp
  · simp

end GNC.ThrustSupport

namespace GNC.ReferenceDisturbance
open ReferenceSupport
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Exact finite-horizon identity for an arbitrary continuous input history.
The known A(t), including reference gravity and frame terms, cancels through
the adjoint. No assumption of commuting generators is made. -/
theorem endpoint_identity (A : ℝ → E →L[ℝ] E)
    (B : ℝ → Vec3 →L[ℝ] E) (ell : ℝ → E →L[ℝ] ℝ) (x r : ℝ → E)
    (w : ℝ → Vec3) {T : ℝ} (hT : 0 ≤ T)
    (hellc : Continuous ell) (hBc : Continuous B) (hrc : Continuous r)
    (hwc : Continuous w)
    (hell : ∀ t ∈ Icc (0:ℝ) T, HasDerivAt ell (-(ell t).comp (A t)) t)
    (hx : ∀ t ∈ Icc (0:ℝ) T, HasDerivAt x (A t (x t)+B t (w t)+r t) t) :
    ell T (x T) = ell 0 (x 0)+
      (∫ t in (0:ℝ)..T, rows (ell t) (B t) ⬝ᵥ w t)+
      ∫ t in (0:ℝ)..T, ell t (r t) := by
  have hd (t : ℝ) (ht : t ∈ Icc (0:ℝ) T) :
      HasDerivAt (fun s => ell s (x s))
        (rows (ell t) (B t) ⬝ᵥ w t+ell t (r t)) t := by
    rw [input_pairing, ← map_add]
    exact adjoint_derivative A ell x (fun s => B s (w s)+r s) (hell t ht)
      (by simpa only [add_assoc] using hx t ht)
  have hi : IntervalIntegrable (fun t => rows (ell t) (B t) ⬝ᵥ w t) volume 0 T :=
    ((rows_continuous ell B hellc hBc).dotProduct hwc).intervalIntegrable 0 T
  have hj : IntervalIntegrable (fun t => ell t (r t)) volume 0 T :=
    (hellc.clm_apply hrc).intervalIntegrable 0 T
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hd t (by simpa only [uIcc_of_le hT] using ht)) (hi.add hj)
  rw [intervalIntegral.integral_add hi hj] at he
  linarith

/-- A directional finite-horizon certificate. The input support and residual
supply may vary throughout the burn. Applying it to the opposite terminal
functional gives the lower bound; multiple directions give an outer polytope. -/
theorem endpoint_bound (A : ℝ → E →L[ℝ] E)
    (B : ℝ → Vec3 →L[ℝ] E) (ell : ℝ → E →L[ℝ] ℝ) (x r : ℝ → E)
    (w : ℝ → Vec3) (input residual : ℝ → ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hellc : Continuous ell) (hBc : Continuous B) (hrc : Continuous r)
    (hwc : Continuous w)
    (hi : IntervalIntegrable input volume 0 T)
    (hr : IntervalIntegrable residual volume 0 T)
    (hell : ∀ t ∈ Icc (0:ℝ) T, HasDerivAt ell (-(ell t).comp (A t)) t)
    (hx : ∀ t ∈ Icc (0:ℝ) T, HasDerivAt x (A t (x t)+B t (w t)+r t) t)
    (hsupply : ∀ t ∈ Icc (0:ℝ) T, rows (ell t) (B t) ⬝ᵥ w t ≤ input t)
    (hresidual : ∀ t ∈ Icc (0:ℝ) T, ell t (r t) ≤ residual t) :
    ell T (x T) ≤ ell 0 (x 0)+(∫ t in (0:ℝ)..T, input t)+
      ∫ t in (0:ℝ)..T, residual t := by
  rw [endpoint_identity A B ell x r w hT hellc hBc hrc hwc hell hx]
  apply add_le_add
  · apply add_le_add le_rfl
    exact intervalIntegral.integral_mono_on hT
      (((rows_continuous ell B hellc hBc).dotProduct hwc).intervalIntegrable 0 T)
      hi hsupply
  · exact intervalIntegral.integral_mono_on hT
      ((hellc.clm_apply hrc).intervalIntegrable 0 T) hr hresidual

end GNC.ReferenceDisturbance
