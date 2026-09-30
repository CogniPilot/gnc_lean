import GNC.Control.DisturbedLogBackstepping
import GNC.Dynamics.RotationCenteredError
import GNC.Control.DecayingSupplyTube

/-! Exact all-axis connection from the log/rate energy to a physical thrust
disturbance. No fixed rotation plane and no small-angle force approximation
is assumed. A spherical acceleration bound can also be used in Cartesian
coordinates; this bridge does not assert a coordinate-performance advantage.
-/
noncomputable section
open Matrix Real Set
namespace GNC.AttitudeThrustBridge

theorem force_bound (Rbar : SO3) (q thrust disturbance : Vec3)
    {κ θ a δ : ℝ} (hκ : 0 < κ) (hθ : 0 ≤ θ) (hchart : θ < 2*π)
    (z : Vec3)
    (henergy : LogBackstepping.rateStorage κ q z ≤ κ*θ^2/2)
    (hthrust : enorm thrust ≤ a) (hd : enorm disturbance ≤ δ) :
    enorm (rotate (Rbar*rotationExp q) thrust-rotate Rbar thrust+disturbance) ≤
      a*θ+δ := by
  have hq := LogBackstepping.rateStorage_angle_bound q z hκ hθ henergy
  have hrot := RotationCenteredError.rotation_difference_bound q thrust (hq.trans_lt hchart)
  have hm := mul_le_mul hq hthrust (enorm_nonneg thrust) hθ
  have hr : enorm (rotate (Rbar*rotationExp q) thrust-rotate Rbar thrust) ≤ a*θ := by
    rw [rotate_mul, ← rotate_sub, rotate_enorm]
    exact hrot.trans (by nlinarith)
  exact (enorm_add_le _ _).trans (add_le_add hr hd)

/-- The established torque/rate controller supplies a uniform three-axis
force-error bound. This composes complete time-history bounds, not samples. -/
theorem force_bound_on (Rbar : ℝ → SO3) (q z d thrust disturbance : ℝ → Vec3)
    {κ kq kz c ell δτ θ a δf t₀ T : ℝ}
    (hκ : 0 < κ) (hc : 0 < c) (hell : 0 < ell)
    (hcq : c ≤ 2*kq) (hcz : c ≤ 2*kz-ell)
    (hθ : 0 ≤ θ) (hchart : θ < 2*π)
    (hq : ∀ t ∈ Icc t₀ T, HasDerivAt q
      (-kq • q t+Jacobian.inverseAt (-q t) (z t)) t)
    (hz : ∀ t ∈ Icc t₀ T, HasDerivAt z (-kz • z t-κ • q t+d t) t)
    (hd : ∀ t ∈ Icc t₀ T, enorm (d t) ≤ δτ)
    (hinit : LogBackstepping.rateStorage κ (q t₀) (z t₀) ≤ κ*θ^2/2)
    (hbudget : δτ^2/(2*ell*c) ≤ κ*θ^2/2)
    (hthrust : ∀ t ∈ Icc t₀ T, enorm (thrust t) ≤ a)
    (hf : ∀ t ∈ Icc t₀ T, enorm (disturbance t) ≤ δf) :
    ∀ t ∈ Icc t₀ T,
      enorm (rotate (Rbar t*rotationExp (q t)) (thrust t)-
        rotate (Rbar t) (thrust t)+disturbance t) ≤ a*θ+δf := by
  have he := LogBackstepping.disturbed_rate_uniform_bound hκ.le hc hell hcq hcz
    hq hz hd hinit hbudget
  intro t ht
  exact force_bound (Rbar t) (q t) (thrust t) (disturbance t) hκ hθ hchart
    (z t) (he t ht) (hthrust t ht) (hf t ht)

/-- Preserve the actual attitude-energy envelope in the physical force
supply. Q may depend on time when this pointwise theorem is applied; it need
not be replaced by a uniform angular cap. -/
theorem force_square_bound (Rbar : SO3) (q z thrust disturbance : Vec3)
    {κ Q a δ η : ℝ} (hκ : 0 < κ)
    (hη : 0 < η) (hchart : enorm q < 2*π)
    (henergy : LogBackstepping.rateStorage κ q z ≤ κ*Q/2)
    (hthrust : enorm thrust ≤ a) (hd : enorm disturbance ≤ δ) :
    enorm (rotate (Rbar*rotationExp q) thrust-rotate Rbar thrust+disturbance)^2 ≤
      (1+η)*a^2*Q+(1+1/η)*δ^2 := by
  have hq : enorm q ^ 2 ≤ Q := by
    unfold LogBackstepping.rateStorage at henergy
    rw [← enorm_sq, ← enorm_sq] at henergy
    nlinarith [sq_nonneg (enorm z)]
  have hr := RotationCenteredError.rotation_difference_bound q thrust hchart
  have hm := mul_le_mul_of_nonneg_left hthrust (enorm_nonneg q)
  have hforce : enorm (rotate (Rbar*rotationExp q) thrust-rotate Rbar thrust+disturbance) ≤
      a*enorm q+δ := by
    apply (enorm_add_le _ _).trans
    apply add_le_add _ hd
    rw [rotate_mul, ← rotate_sub, rotate_enorm]
    exact hr.trans (by nlinarith)
  have hsq : enorm (rotate (Rbar*rotationExp q) thrust-rotate Rbar thrust+disturbance)^2 ≤
      (a*enorm q+δ)^2 := by
    nlinarith [enorm_nonneg (rotate (Rbar*rotationExp q) thrust-rotate Rbar thrust+disturbance)]
  have hy := DecayingSupplyTube.weighted_force_square (a*enorm q) δ η hη
  have hmQ := mul_le_mul_of_nonneg_left hq (show 0 ≤ (1+η)*a^2 by positivity)
  nlinarith

/-- An ideal independent body-frame correction thruster allocation realizes
the inertial vector command without canceling the main-engine pointing error. -/
theorem correction_allocation (R : SO3) (thrust correction : Vec3) :
    rotate R (thrust+rotate R⁻¹ correction) = rotate R thrust+correction := by
  rw [rotate_add,← rotate_mul,mul_inv_cancel,rotate_one]

end GNC.AttitudeThrustBridge
