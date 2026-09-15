import GNC.Control.LocalLogBackstepping
import GNC.Control.ReferenceDisturbance

/-! An explicit rigid-body attitude controller with time-varying external torque.

The rate error is a dynamic state, not an assumed tracking input. The positive
weight κ has units of inverse time squared when angular rates use physical time.
The exact Jacobian cancels in the storage derivative. The physical theorem is
local to the principal chart and assumes realization of the requested torque
and command derivative; it does not certify actuator authority or flexible modes.
-/
noncomputable section
open Matrix Real Set
namespace GNC.LogBackstepping

def rateStorage (κ : ℝ) (q z : Vec3) : ℝ :=
  (κ*lengthSq q+lengthSq z)/2

theorem rateStorage_nonneg {κ : ℝ} (hκ : 0 ≤ κ) (q z : Vec3) :
    0 ≤ rateStorage κ q z := by
  exact div_nonneg (add_nonneg (mul_nonneg hκ (lengthSq_nonneg q))
    (lengthSq_nonneg z)) (by norm_num)

/-- Project the joint energy to an all-axis log-attitude bound. -/
theorem rateStorage_angle_bound (q z : Vec3) {κ α : ℝ} (hκ : 0 < κ) (hα : 0 ≤ α)
    (h : rateStorage κ q z ≤ κ*α^2/2) : enorm q ≤ α := by
  unfold rateStorage at h
  have hs : lengthSq q ≤ α^2 := by nlinarith [lengthSq_nonneg z]
  rw [← enorm_sq] at hs
  nlinarith [enorm_nonneg q]

/-- Known angular-momentum drift can be compensated. The residual must include
any error in the inertia-rate, mass-flux or actuator model. Merely substituting
a time-varying inertia in the constant-inertia Euler equation is not justified. -/
theorem torqueCommand_compensates_drift (I : Vec3 ≃ₗ[ℝ] Vec3)
    (w wc' z correction compensation drift external : Vec3) (k : ℝ) :
    I.symm (torqueCommand I w wc' z correction k+compensation-w ⨯₃ I w-drift+external) =
      wc'-k • z-correction+I.symm (compensation-drift+external) := by
  rw [show torqueCommand I w wc' z correction k+compensation-w ⨯₃ I w-drift+external =
    (torqueCommand I w wc' z correction k-w ⨯₃ I w)+(compensation-drift+external) by abel,
    map_add, torqueCommand_realizes]

/-- Exact nonlinear storage identity, including all three torque components.
No small-angle approximation of the inverse Jacobian is used. -/
theorem disturbed_rate_storage_derivative {q z : ℝ → Vec3} {d : Vec3}
    {κ kq kz t : ℝ}
    (hq : HasDerivAt q (-kq • q t+Jacobian.inverseAt (-q t) (z t)) t)
    (hz : HasDerivAt z (-kz • z t-κ • q t+d) t) :
    HasDerivAt (fun s => rateStorage κ (q s) (z s))
      (-κ*kq*lengthSq (q t)-kz*lengthSq (z t)+z t ⬝ᵥ d) t := by
  convert (((lengthSq_derivative hq).const_mul κ).add
    (lengthSq_derivative hz)).div_const 2 using 1
  simp only [dotProduct_add, dotProduct_sub, dotProduct_smul, smul_eq_mul,
    inverse_right_radial_pairing, dot_self_lengthSq, dotProduct_comm (z t) (q t)]
  ring

/-- Constant torque disturbance admits a nonzero pointing equilibrium.
Stability alone is not bias rejection; integral action or estimation would
need a separate controller and proof. -/
theorem constant_disturbance_equilibrium (q : Vec3) (κ kq kz : ℝ) :
    -kq • q+Jacobian.inverseAt (-q) (kq • q) = 0 ∧
      -kz • (kq • q)-κ • q+(κ+kq*kz) • q = 0 := by
  constructor
  · simp [Jacobian.inverseAt]
  · module

/-- A pointwise supply inequality with an explicit, freely selectable Young
weight ell. This parameter is mathematical optimization freedom, not a tolerance. -/
theorem disturbed_rate_supply (q z d : Vec3) {κ kq kz c ell : ℝ}
    (hκ : 0 ≤ κ) (hell : 0 < ell) (hcq : c ≤ 2*kq) (hcz : c ≤ 2*kz-ell) :
    -κ*kq*lengthSq q-kz*lengthSq z+z ⬝ᵥ d ≤
      -c*rateStorage κ q z+lengthSq d/(2*ell) := by
  have hdot := ThrustSupport.dot_le_enorm z d
  have hy : z ⬝ᵥ d ≤ ell/2*lengthSq z+lengthSq d/(2*ell) := by
    have he : ell/2*lengthSq z+lengthSq d/(2*ell) =
        (ell^2*lengthSq z+lengthSq d)/(2*ell) := by field_simp
    rw [he]
    apply (le_div_iff₀ (by positivity : 0 < 2*ell)).mpr
    have hs := sq_nonneg (ell*enorm z-enorm d)
    ring_nf at hs
    rw [enorm_sq, enorm_sq] at hs
    have hm := mul_le_mul_of_nonneg_left hdot (by positivity : 0 ≤ 2*ell)
    nlinarith
  have hq := mul_nonneg (mul_nonneg hκ (sub_nonneg.mpr hcq)) (lengthSq_nonneg q)
  have hz := mul_nonneg (sub_nonneg.mpr hcz) (lengthSq_nonneg z)
  unfold rateStorage
  nlinarith

/-- Finite-horizon peak-torque bound. The disturbance may vary arbitrarily
in time subject to the pointwise bound; no oscillatory cancellation is assumed. -/
theorem disturbed_rate_bound_on {q z d : ℝ → Vec3} {κ kq kz c ell δ a b : ℝ}
    (hκ : 0 ≤ κ) (hc : 0 < c) (hell : 0 < ell)
    (hcq : c ≤ 2*kq) (hcz : c ≤ 2*kz-ell)
    (hq : ∀ t ∈ Icc a b, HasDerivAt q (-kq • q t+Jacobian.inverseAt (-q t) (z t)) t)
    (hz : ∀ t ∈ Icc a b, HasDerivAt z (-kz • z t-κ • q t+d t) t)
    (hd : ∀ t ∈ Icc a b, enorm (d t) ≤ δ) :
    ∀ t ∈ Icc a b, rateStorage κ (q t) (z t) ≤
      rateStorage κ (q a) (z a)*exp (-c*(t-a))+
        (δ^2/(2*ell*c))*(1-exp (-c*(t-a))) := by
  have h := Lyapunov.disturbed_bound_on (c := c) (ε := δ^2/(2*ell)) hc.ne'
    (fun t ht => disturbed_rate_storage_derivative (hq t ht) (hz t ht)) (by
      intro t ht
      have hδ := hd t ⟨ht.1, ht.2.le⟩
      have hs : lengthSq (d t) ≤ δ^2 := by
        rw [← enorm_sq]
        nlinarith [enorm_nonneg (d t)]
      exact (disturbed_rate_supply (q t) (z t) (d t) hκ hell hcq hcz).trans
        (add_le_add_right (div_le_div_of_nonneg_right hs
          (by positivity : 0 ≤ 2*ell)) _))
  simpa only [div_div] using h

/-- A constant storage envelope follows from the peak-disturbance theorem,
including at the initial time. No strict numerical slack is retained. -/
theorem disturbed_rate_uniform_bound {q z d : ℝ → Vec3} {κ kq kz c ell δ B a b : ℝ}
    (hκ : 0 ≤ κ) (hc : 0 < c) (hell : 0 < ell)
    (hcq : c ≤ 2*kq) (hcz : c ≤ 2*kz-ell)
    (hq : ∀ t ∈ Icc a b, HasDerivAt q (-kq • q t+Jacobian.inverseAt (-q t) (z t)) t)
    (hz : ∀ t ∈ Icc a b, HasDerivAt z (-kz • z t-κ • q t+d t) t)
    (hd : ∀ t ∈ Icc a b, enorm (d t) ≤ δ)
    (hi : rateStorage κ (q a) (z a) ≤ B) (hbudget : δ^2/(2*ell*c) ≤ B) :
    ∀ t ∈ Icc a b, rateStorage κ (q t) (z t) ≤ B := by
  intro t ht
  have h := disturbed_rate_bound_on hκ hc hell hcq hcz hq hz hd t ht
  have he : exp (-c*(t-a)) ≤ 1 := exp_le_one_iff.mpr (by nlinarith [ht.1])
  have hinit := mul_le_mul_of_nonneg_right hi (exp_pos (-c*(t-a))).le
  have hdist := mul_le_mul_of_nonneg_right hbudget (sub_nonneg.mpr he)
  nlinarith

/-- Physical Euler dynamics with the actual external torque, connected to
the principal log of the rotation error and the explicit backstepping command.
The external torque may vary during both burns and coast. The same bound also
covers a rigorously bounded torque-allocation residual included in τ. -/
theorem physical_disturbed_torque_bound_on {X Y : ℝ → SE23}
    (acc accbar w wbar g gbar wc wc' τ : ℝ → Vec3)
    (I : Vec3 ≃ₗ[ℝ] Vec3) {κ kq kz c ell δ a b : ℝ}
    (hκ : 0 ≤ κ) (hc : 0 < c) (hell : 0 < ell)
    (hcq : c ≤ 2*kq) (hcz : c ≤ 2*kz-ell)
    (hX : ∀ t ∈ Icc a b, SpacecraftODEAt X (acc t) (w t) (g t) t)
    (hY : ∀ t ∈ Icc a b, SpacecraftODEAt Y (accbar t) (wbar t) (gbar t) t)
    (hchart : ∀ t ∈ Icc a b, SE23.error (Y t) (X t) ∈ PrincipalLog.domain)
    (hcommand : ∀ t ∈ Icc a b, wc t = angularCommand (principalError X Y t 2) (wbar t)
      (-kq • principalError X Y t 2))
    (hwc : ∀ t ∈ Icc a b, HasDerivAt wc (wc' t) t)
    (hw : ∀ t ∈ Icc a b, HasDerivAt w
      (I.symm (torqueCommand I (w t) (wc' t) (w t-wc t)
        (κ • principalError X Y t 2) kz-w t ⨯₃ I (w t)+τ t)) t)
    (hτ : ∀ t ∈ Icc a b, enorm (I.symm (τ t)) ≤ δ) :
    ∀ t ∈ Icc a b,
      rateStorage κ (principalError X Y t 2) (w t-wc t) ≤
        rateStorage κ (principalError X Y a 2) (w a-wc a)*exp (-c*(t-a))+
          (δ^2/(2*ell*c))*(1-exp (-c*(t-a))) := by
  apply disturbed_rate_bound_on hκ hc hell hcq hcz (d := fun t => I.symm (τ t))
  · intro t ht
    have h := principal_rotation_equation_at (hX t ht) (hY t ht) (hchart t ht)
    have hqt : enorm (principalError X Y t 2) < 2*π := by
      have hb := (PrincipalLog.log_spec (hchart t ht)).1
      change enorm (principalError X Y t 2) < π at hb
      linarith [pi_pos]
    have he : w t = angularCommand (principalError X Y t 2) (wbar t)
        (-kq • principalError X Y t 2)+(w t-wc t) := by
      rw [← hcommand t ht]
      abel
    rw [he, angularCommand_with_rate_error _ _ _ _ hqt] at h
    exact h
  · intro t ht
    have h := hw t ht
    rw [map_add, torqueCommand_realizes] at h
    convert h.sub (hwc t ht) using 1
    module
  · exact hτ

end GNC.LogBackstepping
