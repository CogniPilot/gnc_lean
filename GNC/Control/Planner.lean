import Mathlib.LinearAlgebra.Prod
import Mathlib.Tactic

/-! Proposition 3 as a theorem for an affine transfer map with invertible pv
block. The transfer map is input data; deriving it from an ODE is separate.
-/
noncomputable section
namespace GNC
namespace Planner

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The six translational STM blocks and two forcing blocks of (84)–(87). -/
structure Transfer (V : Type*) [AddCommGroup V] [Module ℝ V] where
  pp : V →ₗ[ℝ] V
  pv : V ≃ₗ[ℝ] V
  pR : V →ₗ[ℝ] V
  vp : V →ₗ[ℝ] V
  vv : V →ₗ[ℝ] V
  vR : V →ₗ[ℝ] V
  bp : V
  bv : V

namespace Transfer
variable (F : Transfer V) (p v r d₀ dT : V)

def position : V := F.pp p + F.pv (v + d₀) + F.pR r + F.bp
def velocity : V := F.vp p + F.vv (v + d₀) + F.vR r + F.bv
def departure : V := -v - F.pv.symm (F.pp p + F.pR r + F.bp)
def arrival : V := -F.velocity p v r (F.departure p v r)

theorem position_zero_iff : F.position p v r d₀ = 0 ↔ d₀ = F.departure p v r := by
  have solve : F.position p v r d₀ = 0 ↔
      F.pv (v + d₀) = -(F.pp p + F.pR r + F.bp) := by
    unfold position
    constructor
    · intro h
      apply eq_neg_iff_add_eq_zero.mpr
      convert h using 1; abel
    · intro h
      rw [h]
      abel
  rw [solve]
  constructor
  · intro h
    have hh := congrArg F.pv.symm h
    simp only [LinearEquiv.symm_apply_apply, map_neg] at hh
    unfold departure
    calc
      d₀ = (v + d₀) - v := by abel
      _ = -F.pv.symm (F.pp p + F.pR r + F.bp) - v := by rw [hh]
      _ = _ := by abel
  · rintro rfl
    simp [departure, map_sub, map_neg]
    abel

/-- Equations (85) and (88) satisfy both terminal constraints. -/
theorem rendezvous :
    F.position p v r (F.departure p v r) = 0 ∧
    F.velocity p v r (F.departure p v r) + F.arrival p v r = 0 := by
  exact ⟨(F.position_zero_iff p v r _).mpr rfl, add_neg_cancel _⟩

/-- The pair is unique, including uniqueness of the arrival impulse. -/
theorem unique_pair (hp : F.position p v r d₀ = 0)
    (hv : F.velocity p v r d₀ + dT = 0) :
    d₀ = F.departure p v r ∧ dT = F.arrival p v r := by
  have hd := (F.position_zero_iff p v r d₀).mp hp
  refine ⟨hd, ?_⟩
  subst d₀
  exact eq_neg_of_add_eq_zero_right hv

/-- The arrival velocity is independent of the pre-departure velocity (86). -/
theorem arrival_velocity : F.velocity p v r (F.departure p v r) =
    (F.vp p - F.vv (F.pv.symm (F.pp p))) +
    (F.vR r - F.vv (F.pv.symm (F.pR r))) +
    (F.bv - F.vv (F.pv.symm F.bp)) := by
  simp [velocity, departure, map_sub, map_add, map_neg]
  abel

end Transfer

/-- Lemma 5's coordinate conversion, for any invertible R·J map. -/
theorem impulse_coordinates (RJ : V ≃ₗ[ℝ] V) (v dv : V) :
    RJ.symm (RJ v + dv) = v + RJ.symm dv := by simp

/-- The log-coordinate and physical rendezvous conditions (76) agree. -/
theorem physical_zero_iff (RJ : V ≃ₗ[ℝ] V) (x : V) : RJ x = 0 ↔ x = 0 := by simp

end Planner
end GNC
