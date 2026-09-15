import GNC.Applications.Rendezvous.ODEPlanner

/-! Remark 9: exact nonzero physical waypoints and their unique two-impulse
solve, including the ODE response and the physical arrival conversion. -/
noncomputable section
namespace GNC
namespace Planner.Transfer
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

def waypointDeparture (F : Planner.Transfer V) (p v r target : V) : V :=
  F.departure p v r+F.pv.symm target

def waypointArrival (F : Planner.Transfer V) (p v r target : V) : V :=
  -F.velocity p v r (F.waypointDeparture p v r target)

theorem position_target_iff (F : Planner.Transfer V) (p v r target d : V) :
    F.position p v r d = target ↔ d = F.waypointDeparture p v r target := by
  let G : Planner.Transfer V := {F with bp := F.bp-target}
  have hp : G.position p v r d = F.position p v r d-target := by
    simp only [position, G]; abel
  have hd : G.departure p v r = F.waypointDeparture p v r target := by
    simp only [departure, waypointDeparture, G]
    rw [show F.pp p+F.pR r+(F.bp-target) = (F.pp p+F.pR r+F.bp)-target by abel,
      map_sub]
    abel
  rw [← sub_eq_zero, ← hp, G.position_zero_iff, hd]

theorem waypoint_rendezvous (F : Planner.Transfer V) (p v r target : V) :
    F.position p v r (F.waypointDeparture p v r target) = target ∧
    F.velocity p v r (F.waypointDeparture p v r target)+F.waypointArrival p v r target = 0 :=
  ⟨(F.position_target_iff p v r target _).mpr rfl, add_neg_cancel _⟩

theorem waypoint_unique_pair (F : Planner.Transfer V) (p v r target d₀ dT : V)
    (hp : F.position p v r d₀ = target) (hv : F.velocity p v r d₀+dT = 0) :
    d₀ = F.waypointDeparture p v r target ∧ dT = F.waypointArrival p v r target := by
  have hd := (F.position_target_iff p v r target d₀).mp hp
  refine ⟨hd, ?_⟩
  subst d₀
  exact eq_neg_of_add_eq_zero_right hv

end Planner.Transfer
namespace ODEPlanner

/-- Equation (94). -/
def waypointCoordinates (R : SO3) (q ρ : Vec3) : Vec3 :=
  Jacobian.inverseAt q (rotate R⁻¹ ρ)

theorem waypoint_coordinates_exact (R : SO3) (q ρ : Vec3) (hq : enorm q < Real.pi) :
    physicalImpulse R q (waypointCoordinates R q ρ) = ρ := by
  simp only [physicalImpulse, waypointCoordinates,
    Jacobian.leftAt_inverseAt_all q _ (by linarith [Real.pi_pos]),
    ← rotate_mul, mul_inv_cancel, rotate_one]

theorem physical_waypoint (chief deputy : SE23) (x : LogState) (ρ : Vec3)
    (hq : enorm (x 2) < Real.pi) (he : SE23.error chief deputy = groupExp x)
    (hp : x 0 = waypointCoordinates chief.rot (x 2) ρ) :
    deputy.pos = chief.pos+ρ := by
  rw [physical_separation chief deputy x he, hp, waypoint_coordinates_exact _ _ _ hq]

theorem physical_arrival_velocity (chief deputy : SE23) (x : LogState) (dv : Vec3)
    (hq : enorm (x 2) < Real.pi) (he : SE23.error chief deputy = groupExp x)
    (hv : x 1+dv = 0) :
    (SE23.impulse deputy (physicalImpulse chief.rot (x 2) dv)).vel = chief.vel := by
  have h := congrArg (fun X : SE23 => rotate chief.rot X.vel)
    (commanded_impulse chief deputy x dv hq he)
  simp only [SE23.error_vel, ← rotate_mul, mul_inv_cancel, rotate_one,
    groupExp, impulseCoordinates, Matrix.cons_val_one, Matrix.cons_val_zero,
    hv, Jacobian.leftAt_zero, rotate_zero] at h
  exact sub_eq_zero.mp h

theorem waypoint_ode_rendezvous (Φ : ℝ → Endˣ) (A : ℝ → End)
    (hΦ : ∀ t, HasDerivAt (fun s => (Φ s).val) (A t*(Φ t).val) t)
    (h₀ : Φ 0 = 1) (u : ℝ → LogState) (hu : Continuous u) (T : ℝ)
    (pv : Vec3 ≃ₗ[ℝ] Vec3) (hpv : ∀ v, pv v = block (Φ T).val 0 1 v)
    (p v r target : Vec3) (f : ℝ → LogState)
    (hf : ∀ t, HasDerivAt f (A t (f t)+u t) t)
    (hi : f 0 = ![p,v+(transfer Φ u T pv).waypointDeparture p v r target,r]) :
    f T 0 = target ∧ f T 1+(transfer Φ u T pv).waypointArrival p v r target = 0 := by
  obtain ⟨hp,hv⟩ := terminal_blocks Φ A hΦ h₀ u hu T pv hpv p v r _ f hf hi
  rw [hp,hv]
  exact (transfer Φ u T pv).waypoint_rendezvous p v r target

end ODEPlanner
end GNC
