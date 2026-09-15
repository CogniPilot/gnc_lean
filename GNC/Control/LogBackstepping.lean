import GNC.Dynamics.PrincipalErrorDynamics
import GNC.Control.Lyapunov

/-! Exact log-attitude input inversion, connected to the physical ODE and
the constructed principal logarithm. Angular velocity is a virtual input;
moment and actuator realization are separate control layers.
-/
noncomputable section
open Matrix Real
namespace GNC.LogBackstepping

theorem rotation_drift_rewrite (q w wbar : Vec3) :
    -(w ⨯₃ q) + Jacobian.inverseAt q (w-wbar) =
      -(wbar ⨯₃ q) + Jacobian.inverseAt (-q) (w-wbar) := by
  ext i
  fin_cases i <;>
    simp [Jacobian.inverseAt, enorm_neg, crossProduct, vecHead, vecTail] <;> ring

def angularCommand (q wbar u : Vec3) : Vec3 :=
  wbar+Jacobian.leftAt (-q) (u+wbar ⨯₃ q)

theorem angularCommand_realizes (q wbar u : Vec3) (hq : enorm q < 2*π) :
    -(wbar ⨯₃ q)+Jacobian.inverseAt (-q) (angularCommand q wbar u-wbar) = u := by
  simp only [angularCommand, add_sub_cancel_left]
  rw [Jacobian.inverseAt_leftAt_all _ _ (by simpa only [enorm_neg] using hq)]
  abel

theorem angularCommand_with_rate_error (q wbar u z : Vec3) (hq : enorm q < 2*π) :
    -(wbar ⨯₃ q)+Jacobian.inverseAt (-q) (angularCommand q wbar u+z-wbar) =
      u+Jacobian.inverseAt (-q) z := by
  rw [show angularCommand q wbar u+z-wbar =
    (angularCommand q wbar u-wbar)+z by abel, Jacobian.inverseAt_add]
  rw [← add_assoc, angularCommand_realizes q wbar u hq]

def torqueCommand (I : Vec3 ≃ₗ[ℝ] Vec3) (w desiredDerivative rateError correction : Vec3)
    (k : ℝ) : Vec3 :=
  w ⨯₃ I w + I (desiredDerivative-k • rateError-correction)

/-- The actual Euler rigid-body equation under an invertible inertia map
realizes the angular-acceleration command. Surface/moment allocation is separate. -/
theorem torqueCommand_realizes (I : Vec3 ≃ₗ[ℝ] Vec3)
    (w desiredDerivative rateError correction : Vec3) (k : ℝ) :
    I.symm (torqueCommand I w desiredDerivative rateError correction k-w ⨯₃ I w) =
      desiredDerivative-k • rateError-correction := by
  simp [torqueCommand]

/-- The corrected reference-rate log rotation equation, derived from physical
position/velocity/rotation ODEs and the actual principal logarithm. -/
theorem principal_rotation_equation {X Y : ℝ → SE23}
    {a w abar wbar g gbar : Vec3} {t : ℝ}
    (hX : SpacecraftODEAt X a w g t) (hY : SpacecraftODEAt Y abar wbar gbar t)
    (hd : ∀ s, SE23.error (Y s) (X s) ∈ PrincipalLog.domain) :
    HasDerivAt (fun s => principalError X Y s 2)
      (-(wbar ⨯₃ principalError X Y t 2) +
        Jacobian.inverseAt (-(principalError X Y t 2)) (w-wbar)) t := by
  have hp := principalError_hasDerivAt hX hY (hd t)
  have he := congrArg (fun z : LogState => z 2) (principal_proposition1 hX hY hd)
  simp only [Pi.add_apply, logDrift, Pi.sub_apply, Matrix.cons_val,
    ad, Jacobian.controlInput, Jacobian.blockInverse, Jacobian.blockRightInverse,
    Pi.neg_apply, adjoint, velocityOnly, rotate_zero, Jacobian.inverseAt,
    map_zero, LinearMap.zero_apply, smul_zero, sub_zero, add_zero, zero_sub] at he
  have hre := rotation_drift_rewrite (principalError X Y t 2) w wbar
  change -(w ⨯₃ principalError X Y t 2)+
    Jacobian.inverseAt (principalError X Y t 2) (w-wbar) = _ at hre
  have hcomponent := hasDerivAt_pi.mp hp (2 : Fin 3)
  convert hcomponent using 1
  rw [he]
  exact hre.symm

/-- Choosing u = -k*q gives exact first-order log-attitude dynamics,
on the principal chart and with the commanded angular rate realized. -/
theorem principal_rotation_feedback {X Y : ℝ → SE23}
    {a abar wbar g gbar : Vec3} {k t : ℝ}
    (hX : SpacecraftODEAt X a
      (angularCommand (principalError X Y t 2) wbar (-k • principalError X Y t 2)) g t)
    (hY : SpacecraftODEAt Y abar wbar gbar t)
    (hd : ∀ s, SE23.error (Y s) (X s) ∈ PrincipalLog.domain) :
    HasDerivAt (fun s => principalError X Y s 2) (-k • principalError X Y t 2) t := by
  have h := principal_rotation_equation hX hY hd
  rw [angularCommand_realizes] at h
  · exact h
  · have hb := (PrincipalLog.log_spec (hd t)).1
    change enorm (principalError X Y t 2) < π at hb
    linarith [pi_pos]

/-- Radial pairing is unchanged by the inverse right Jacobian. Consequently
its adjoint applied to q is just q, simplifying attitude backstepping. -/
theorem inverse_right_radial_pairing (q z : Vec3) :
    q ⬝ᵥ Jacobian.inverseAt (-q) z = q ⬝ᵥ z := by
  simp [Jacobian.inverseAt, dotProduct_add, dotProduct_sub, dotProduct_smul]

theorem lengthSq_derivative {x : ℝ → Vec3} {dx : Vec3} {t : ℝ}
    (hx : HasDerivAt x dx t) :
    HasDerivAt (fun s => lengthSq (x s)) (2*(x t ⬝ᵥ dx)) t := by
  have h0 := (hasDerivAt_pi.mp hx (0 : Fin 3)).pow 2
  have h1 := (hasDerivAt_pi.mp hx (1 : Fin 3)).pow 2
  have h2 := (hasDerivAt_pi.mp hx (2 : Fin 3)).pow 2
  convert (h0.add h1).add h2 using 1
  simp [dotProduct, Fin.sum_univ_succ]
  ring

/-- Exact Euclidean energy comparison for log attitude and rate error,
using the radial identity rather than an assumed coupling adjoint. -/
theorem rotation_rate_energy_bound {q z : ℝ → Vec3} {kq kz k a b : ℝ}
    (hkq : k ≤ kq) (hkz : k ≤ kz)
    (hq : ∀ t, HasDerivAt q (-kq • q t+Jacobian.inverseAt (-q t) (z t)) t)
    (hz : ∀ t, HasDerivAt z (-kz • z t-q t) t) :
    ∀ t ∈ Set.Icc a b, (enorm (q t)^2+enorm (z t)^2)/2 ≤
      ((enorm (q a)^2+enorm (z a)^2)/2)*exp (-2*k*(t-a)) := by
  have hd : ∀ t, HasDerivAt (fun s => (lengthSq (q s)+lengthSq (z s))/2)
      (-kq*lengthSq (q t)-kz*lengthSq (z t)) t := by
    intro t
    convert ((lengthSq_derivative (hq t)).add (lengthSq_derivative (hz t))).div_const 2 using 1
    simp only [dotProduct_add, dotProduct_sub, dotProduct_smul, smul_eq_mul,
      inverse_right_radial_pairing, dot_self_lengthSq, dotProduct_comm (z t) (q t)]
    ring
  have h := Lyapunov.exponential_bound (c := 2*k) (a := a) (b := b) hd (by
    intro t ht
    nlinarith [mul_nonneg (sub_nonneg.mpr hkq) (lengthSq_nonneg (q t)),
      mul_nonneg (sub_nonneg.mpr hkz) (lengthSq_nonneg (z t))])
  simpa only [enorm_sq, neg_mul] using h

/-- Closed torque-feedback theorem for the actual principal log of the
physical rotational motion, coupled to Euler's rigid-body equation.
The virtual command is a function of q and the reference rate; its given
derivative must be its actual derivative. The principal chart and existence
of the physical trajectory remain explicit domain/solution hypotheses. -/
theorem physical_torque_energy_bound {X Y : ℝ → SE23}
    (acc accbar w wbar g gbar wc wc' : ℝ → Vec3)
    (I : Vec3 ≃ₗ[ℝ] Vec3) {kq kz k t₀ T : ℝ}
    (hkq : k ≤ kq) (hkz : k ≤ kz)
    (hX : ∀ t, SpacecraftODEAt X (acc t) (w t) (g t) t)
    (hY : ∀ t, SpacecraftODEAt Y (accbar t) (wbar t) (gbar t) t)
    (hd : ∀ t, SE23.error (Y t) (X t) ∈ PrincipalLog.domain)
    (hc : ∀ t, wc t = angularCommand (principalError X Y t 2) (wbar t)
      (-kq • principalError X Y t 2))
    (hwc : ∀ t, HasDerivAt wc (wc' t) t)
    (hw : ∀ t, HasDerivAt w
      (I.symm (torqueCommand I (w t) (wc' t) (w t-wc t)
        (principalError X Y t 2) kz - w t ⨯₃ I (w t))) t) :
    ∀ t ∈ Set.Icc t₀ T,
      (enorm (principalError X Y t 2)^2+enorm (w t-wc t)^2)/2 ≤
      ((enorm (principalError X Y t₀ 2)^2+enorm (w t₀-wc t₀)^2)/2)*
        exp (-2*k*(t-t₀)) := by
  apply rotation_rate_energy_bound hkq hkz
  · intro t
    have h := principal_rotation_equation (hX t) (hY t) hd
    have hqt : enorm (principalError X Y t 2) < 2*π := by
      have hb := (PrincipalLog.log_spec (hd t)).1
      change enorm (principalError X Y t 2) < π at hb
      linarith [pi_pos]
    have he : w t = angularCommand (principalError X Y t 2) (wbar t)
        (-kq • principalError X Y t 2)+(w t-wc t) := by
      rw [← hc t]
      abel
    rw [he, angularCommand_with_rate_error _ _ _ _ hqt] at h
    exact h
  · intro t
    have h := hw t
    rw [torqueCommand_realizes] at h
    convert h.sub (hwc t) using 1
    module

end GNC.LogBackstepping
