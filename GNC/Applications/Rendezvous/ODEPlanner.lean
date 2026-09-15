import GNC.Analysis.ForcedResponse
import GNC.Dynamics.MixedErrorDynamics

/-! Proposition 3 for the actual variation-of-constants response. The
transfer blocks are extracted from the fundamental solution, and the affine
terms are its Bochner integrals; they are not independent input data. -/
noncomputable section
open Matrix
namespace GNC.ODEPlanner

abbrev End := LogState →L[ℝ] LogState

def block (F : End) (i j : Fin 3) : Vec3 →ₗ[ℝ] Vec3 :=
  (LinearMap.proj i).comp (F.toLinearMap.comp (LinearMap.single ℝ (fun _ : Fin 3 => Vec3) j))

theorem state_decomposition (p v r : Vec3) :
    (![p,v,r] : LogState) = Pi.single 0 p+Pi.single 1 v+Pi.single 2 r := by
  ext i j; fin_cases i <;> simp

theorem block_action (F : End) (p v r : Vec3) (i : Fin 3) :
    F ![p,v,r] i = block F i 0 p+block F i 1 v+block F i 2 r := by
  rw [state_decomposition]
  simp [block, map_add]

def transfer (Φ : ℝ → Endˣ) (u : ℝ → LogState) (T : ℝ)
    (pv : Vec3 ≃ₗ[ℝ] Vec3) : Planner.Transfer Vec3 where
  pp := block (Φ T).val 0 0
  pv := pv
  pR := block (Φ T).val 0 2
  vp := block (Φ T).val 1 0
  vv := block (Φ T).val 1 1
  vR := block (Φ T).val 1 2
  bp := ForcedResponse.response Φ u 0 T 0
  bv := ForcedResponse.response Φ u 0 T 1

/-- The position constraint is exactly the position of the integral response. -/
theorem transfer_position (Φ : ℝ → Endˣ) (u : ℝ → LogState) (T : ℝ)
    (pv : Vec3 ≃ₗ[ℝ] Vec3) (hpv : ∀ v, pv v = block (Φ T).val 0 1 v)
    (p v r d : Vec3) :
    (transfer Φ u T pv).position p v r d =
      ForcedResponse.response Φ u ![p,v+d,r] T 0 := by
  rw [ForcedResponse.response_affine]
  simp only [Pi.add_apply, block_action, Planner.Transfer.position, transfer, hpv]

theorem transfer_velocity (Φ : ℝ → Endˣ) (u : ℝ → LogState) (T : ℝ)
    (pv : Vec3 ≃ₗ[ℝ] Vec3) (p v r d : Vec3) :
    (transfer Φ u T pv).velocity p v r d =
      ForcedResponse.response Φ u ![p,v+d,r] T 1 := by
  rw [ForcedResponse.response_affine]
  simp only [Pi.add_apply, block_action, Planner.Transfer.velocity, transfer]

/-- The integral response of any trajectory with the prescribed post-impulse
initial state agrees with the planner's terminal constraints. -/
theorem terminal_blocks (Φ : ℝ → Endˣ) (A : ℝ → End)
    (hΦ : ∀ t, HasDerivAt (fun s => (Φ s).val) (A t*(Φ t).val) t)
    (h₀ : Φ 0 = 1) (u : ℝ → LogState) (hu : Continuous u) (T : ℝ)
    (pv : Vec3 ≃ₗ[ℝ] Vec3) (hpv : ∀ v, pv v = block (Φ T).val 0 1 v)
    (p v r d : Vec3) (f : ℝ → LogState)
    (hf : ∀ t, HasDerivAt f (A t (f t)+u t) t) (hi : f 0 = ![p,v+d,r]) :
    f T 0 = (transfer Φ u T pv).position p v r d ∧
    f T 1 = (transfer Φ u T pv).velocity p v r d := by
  have h := congrFun (ForcedResponse.response_unique Φ A hΦ h₀ u hu f hf) T
  rw [hi] at h
  rw [h, transfer_position Φ u T pv hpv, transfer_velocity Φ u T pv]
  exact ⟨rfl,rfl⟩

/-- Proposition 3: both impulses meet both terminal constraints for every
solution of the retained ODE with the corresponding initial jump. -/
theorem rendezvous (Φ : ℝ → Endˣ) (A : ℝ → End)
    (hΦ : ∀ t, HasDerivAt (fun s => (Φ s).val) (A t*(Φ t).val) t)
    (h₀ : Φ 0 = 1) (u : ℝ → LogState) (hu : Continuous u) (T : ℝ)
    (pv : Vec3 ≃ₗ[ℝ] Vec3) (hpv : ∀ v, pv v = block (Φ T).val 0 1 v)
    (p v r : Vec3) (f : ℝ → LogState)
    (hf : ∀ t, HasDerivAt f (A t (f t)+u t) t)
    (hi : f 0 = ![p,v+(transfer Φ u T pv).departure p v r,r]) :
    f T 0 = 0 ∧ f T 1+(transfer Φ u T pv).arrival p v r = 0 := by
  obtain ⟨hp,hv⟩ := terminal_blocks Φ A hΦ h₀ u hu T pv hpv p v r _ f hf hi
  rw [hp,hv]
  exact (transfer Φ u T pv).rendezvous p v r

/-- Uniqueness holds for the actual ODE response, not just a separate
affine model with unspecified transfer blocks. -/
theorem unique_pair (Φ : ℝ → Endˣ) (A : ℝ → End)
    (hΦ : ∀ t, HasDerivAt (fun s => (Φ s).val) (A t*(Φ t).val) t)
    (h₀ : Φ 0 = 1) (u : ℝ → LogState) (hu : Continuous u) (T : ℝ)
    (pv : Vec3 ≃ₗ[ℝ] Vec3) (hpv : ∀ v, pv v = block (Φ T).val 0 1 v)
    (p v r d₀ dT : Vec3) (f : ℝ → LogState)
    (hf : ∀ t, HasDerivAt f (A t (f t)+u t) t) (hi : f 0 = ![p,v+d₀,r])
    (hp : f T 0 = 0) (hv : f T 1+dT = 0) :
    d₀ = (transfer Φ u T pv).departure p v r ∧
    dT = (transfer Φ u T pv).arrival p v r := by
  obtain ⟨hp',hv'⟩ := terminal_blocks Φ A hΦ h₀ u hu T pv hpv p v r d₀ f hf hi
  rw [hp'] at hp
  rw [hv'] at hv
  exact (transfer Φ u T pv).unique_pair p v r d₀ dT hp hv

/-- A commanded log-velocity jump is realized by the exact inertial impulse. -/
theorem commanded_impulse (chief deputy : SE23) (x : LogState) (dv : Vec3)
    (hx : enorm (x 2) < Real.pi) (he : SE23.error chief deputy = groupExp x) :
    SE23.error chief (SE23.impulse deputy (physicalImpulse chief.rot (x 2) dv)) =
      groupExp (impulseCoordinates x dv) := by
  rw [GNC.impulse_coordinates chief deputy x _ hx he]
  simp only [physicalImpulse, ← rotate_mul, inv_mul_cancel, rotate_one,
    Jacobian.inverseAt_leftAt_all (x 2) dv (by linarith [Real.pi_pos])]

theorem translation_eq_of_error_zero (chief deputy : SE23)
    (hp : (SE23.error chief deputy).pos = 0) (hv : (SE23.error chief deputy).vel = 0) :
    deputy.pos = chief.pos ∧ deputy.vel = chief.vel := by
  rw [SE23.error_pos] at hp
  rw [SE23.error_vel] at hv
  have hp' := congrArg (rotate chief.rot) hp
  have hv' := congrArg (rotate chief.rot) hv
  simp only [← rotate_mul, mul_inv_cancel, rotate_one, rotate_zero] at hp' hv'
  exact ⟨sub_eq_zero.mp hp',sub_eq_zero.mp hv'⟩

/-- The paper's two terminal log constraints give actual equal positions and
velocities after applying the exact final impulse conversion. -/
theorem physical_rendezvous (chief deputy : SE23) (x : LogState) (dv : Vec3)
    (hx : enorm (x 2) < Real.pi) (he : SE23.error chief deputy = groupExp x)
    (hp : x 0 = 0) (hv : x 1+dv = 0) :
    deputy.pos = chief.pos ∧
      (SE23.impulse deputy (physicalImpulse chief.rot (x 2) dv)).vel = chief.vel := by
  apply translation_eq_of_error_zero chief (SE23.impulse deputy (physicalImpulse chief.rot (x 2) dv))
  · rw [commanded_impulse chief deputy x dv hx he]
    simp [groupExp, impulseCoordinates, hp]
  · rw [commanded_impulse chief deputy x dv hx he]
    simp [groupExp, impulseCoordinates, hv]

end GNC.ODEPlanner
