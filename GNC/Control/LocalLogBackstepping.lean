import GNC.Control.LogBackstepping

/-! Finite-domain versions of the physical log and torque results.
Locality of the logarithm is handled using its open domain and actual
trajectory continuity. No principal-chart hypothesis for all real time
is needed by these theorems.
-/
noncomputable section
open Matrix Real Filter
open scoped Topology Manifold Matrix Matrix.Norms.Operator
namespace GNC

theorem spacecraft_log_equation_eventually {X Y : ℝ → SE23} {x : ℝ → LogState}
    {dx ν νbar : LogState} {g gbar : Vec3} {t : ℝ}
    (hX : HasDerivAt (fun s => SE23.toMatrix (X s)) (spacecraftDerivative (X t) ν g) t)
    (hY : HasDerivAt (fun s => SE23.toMatrix (Y s)) (spacecraftDerivative (Y t) νbar gbar) t)
    (hx : HasDerivAt x dx t)
    (he : ∀ᶠ s in 𝓝 t, SE23.error (Y s) (X s) = groupExp (x s))
    (hqπ : enorm (x t 2) < π) :
    dx = logDrift ν (x t)+Jacobian.blockInverse (x t)
      (ν-νbar+velocityOnly (rotate (Y t).rot⁻¹ (g-gbar))) := by
  have h := matrix_error_derivative hX hY
  have ht := he.self_of_nhds
  have heM : (fun s => NormedSpace.exp (hat (x s))) =ᶠ[𝓝 t]
      (fun s => SE23.toMatrix (SE23.error (Y s) (X s))) :=
    he.mono fun s hs => by
      change NormedSpace.exp (hat (x s)) = SE23.toMatrix (SE23.error (Y s) (X s))
      rw [hs, groupExp_toMatrix]
  have h' := h.congr_of_eventuallyEq heM
  rw [ht, groupExp_toMatrix] at h'
  exact log_error_equation hx (by linarith [pi_pos]) h'

theorem principal_proposition1_at {X Y : ℝ → SE23} {a w abar wbar g gbar : Vec3} {t : ℝ}
    (hX : SpacecraftODEAt X a w g t) (hY : SpacecraftODEAt Y abar wbar gbar t)
    (hd : SE23.error (Y t) (X t) ∈ PrincipalLog.domain) :
    deriv (principalError X Y) t =
      logDrift (Jacobian.controlInput a w) (principalError X Y t)+
      Jacobian.blockInverse (principalError X Y t) (Jacobian.controlInput (a-abar) (w-wbar))+
      Jacobian.blockRightInverse (principalError X Y t) (adjoint (X t)⁻¹ (velocityOnly (g-gbar))) := by
  have hx := (spacecraft_ode_iff X a w g t).mp hX
  have hy := (spacecraft_ode_iff Y abar wbar gbar t).mp hY
  have hxc := (matrix_curve_mdifferentiableAt hx.differentiableAt).continuousAt
  have hyc := (matrix_curve_mdifferentiableAt hy.differentiableAt).continuousAt
  have hec : ContinuousAt (fun s => SE23.error (Y s) (X s)) t :=
    hyc.inv.mul hxc
  have hmem := hec.eventually (PrincipalLog.isOpen_domain.eventually_mem hd)
  have he : ∀ᶠ s in 𝓝 t, SE23.error (Y s) (X s) = groupExp (principalError X Y s) :=
    hmem.mono fun s hs => (PrincipalLog.log_spec hs).2.symm
  have hspec := PrincipalLog.log_spec hd
  change enorm (principalError X Y t 2) < π ∧
    groupExp (principalError X Y t) = SE23.error (Y t) (X t) at hspec
  have h := spacecraft_log_equation_eventually hx hy
    (principalError_hasDerivAt hX hY hd) he hspec.1
  rw [controlInput_sub, blockInverse_add _ _ _ (by linarith [pi_pos,hspec.1])] at h
  rw [gravity_right_transport (Y t) (X t) (principalError X Y t) (g-gbar)
    hspec.2.symm (by linarith [pi_pos,hspec.1])]
  exact h.trans (add_assoc _ _ _).symm

namespace LogBackstepping

theorem principal_rotation_equation_at {X Y : ℝ → SE23}
    {a w abar wbar g gbar : Vec3} {t : ℝ}
    (hX : SpacecraftODEAt X a w g t) (hY : SpacecraftODEAt Y abar wbar gbar t)
    (hd : SE23.error (Y t) (X t) ∈ PrincipalLog.domain) :
    HasDerivAt (fun s => principalError X Y s 2)
      (-(wbar ⨯₃ principalError X Y t 2)+
        Jacobian.inverseAt (-(principalError X Y t 2)) (w-wbar)) t := by
  have hp := principalError_hasDerivAt hX hY hd
  have he := congrArg (fun z : LogState => z 2) (principal_proposition1_at hX hY hd)
  simp only [Pi.add_apply, logDrift, Pi.sub_apply, Matrix.cons_val,
    ad, Jacobian.controlInput, Jacobian.blockInverse, Jacobian.blockRightInverse,
    Pi.neg_apply, adjoint, velocityOnly, rotate_zero, Jacobian.inverseAt,
    map_zero, LinearMap.zero_apply, smul_zero, sub_zero, add_zero, zero_sub] at he
  have hre := rotation_drift_rewrite (principalError X Y t 2) w wbar
  change -(w ⨯₃ principalError X Y t 2)+
    Jacobian.inverseAt (principalError X Y t 2) (w-wbar) = _ at hre
  have hc := hasDerivAt_pi.mp hp (2 : Fin 3)
  convert hc using 1
  rw [he]
  exact hre.symm

theorem rotation_rate_energy_bound_on {q z : ℝ → Vec3} {kq kz k a b : ℝ}
    (hkq : k ≤ kq) (hkz : k ≤ kz)
    (hq : ∀ t ∈ Set.Icc a b, HasDerivAt q (-kq • q t+Jacobian.inverseAt (-q t) (z t)) t)
    (hz : ∀ t ∈ Set.Icc a b, HasDerivAt z (-kz • z t-q t) t) :
    ∀ t ∈ Set.Icc a b, (enorm (q t)^2+enorm (z t)^2)/2 ≤
      ((enorm (q a)^2+enorm (z a)^2)/2)*exp (-2*k*(t-a)) := by
  have hd : ∀ t ∈ Set.Icc a b, HasDerivAt (fun s => (lengthSq (q s)+lengthSq (z s))/2)
      (-kq*lengthSq (q t)-kz*lengthSq (z t)) t := by
    intro t ht
    convert ((lengthSq_derivative (hq t ht)).add (lengthSq_derivative (hz t ht))).div_const 2 using 1
    simp only [dotProduct_add, dotProduct_sub, dotProduct_smul, smul_eq_mul,
      inverse_right_radial_pairing, dot_self_lengthSq, dotProduct_comm (z t) (q t)]
    ring
  have h := Lyapunov.exponential_bound_on (c := 2*k) (a := a) (b := b) hd (by
    intro t ht
    nlinarith [mul_nonneg (sub_nonneg.mpr hkq) (lengthSq_nonneg (q t)),
      mul_nonneg (sub_nonneg.mpr hkz) (lengthSq_nonneg (z t))])
  simpa only [enorm_sq, neg_mul] using h

theorem physical_torque_energy_bound_on {X Y : ℝ → SE23}
    (acc accbar w wbar g gbar wc wc' : ℝ → Vec3)
    (I : Vec3 ≃ₗ[ℝ] Vec3) {kq kz k t₀ T : ℝ}
    (hkq : k ≤ kq) (hkz : k ≤ kz)
    (hX : ∀ t ∈ Set.Icc t₀ T, SpacecraftODEAt X (acc t) (w t) (g t) t)
    (hY : ∀ t ∈ Set.Icc t₀ T, SpacecraftODEAt Y (accbar t) (wbar t) (gbar t) t)
    (hd : ∀ t ∈ Set.Icc t₀ T, SE23.error (Y t) (X t) ∈ PrincipalLog.domain)
    (hc : ∀ t ∈ Set.Icc t₀ T, wc t = angularCommand (principalError X Y t 2) (wbar t)
      (-kq • principalError X Y t 2))
    (hwc : ∀ t ∈ Set.Icc t₀ T, HasDerivAt wc (wc' t) t)
    (hw : ∀ t ∈ Set.Icc t₀ T, HasDerivAt w
      (I.symm (torqueCommand I (w t) (wc' t) (w t-wc t)
        (principalError X Y t 2) kz-w t ⨯₃ I (w t))) t) :
    ∀ t ∈ Set.Icc t₀ T,
      (enorm (principalError X Y t 2)^2+enorm (w t-wc t)^2)/2 ≤
      ((enorm (principalError X Y t₀ 2)^2+enorm (w t₀-wc t₀)^2)/2)*
        exp (-2*k*(t-t₀)) := by
  apply rotation_rate_energy_bound_on hkq hkz
  · intro t ht
    have h := principal_rotation_equation_at (hX t ht) (hY t ht) (hd t ht)
    have hqt : enorm (principalError X Y t 2) < 2*π := by
      have hb := (PrincipalLog.log_spec (hd t ht)).1
      change enorm (principalError X Y t 2) < π at hb
      linarith [pi_pos]
    have he : w t = angularCommand (principalError X Y t 2) (wbar t)
        (-kq • principalError X Y t 2)+(w t-wc t) := by
      rw [← hc t ht]
      abel
    rw [he, angularCommand_with_rate_error _ _ _ _ hqt] at h
    exact h
  · intro t ht
    have h := hw t ht
    rw [torqueCommand_realizes] at h
    convert h.sub (hwc t ht) using 1
    module

end LogBackstepping
end GNC
