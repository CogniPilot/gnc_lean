import GNC.Control.SharedBias
import GNC.Control.Propellant

/-! Exact two-burn scalar-channel fuel comparison. The signed transverse
sensitivities are explicit model assumptions; this example is not an orbit
trajectory certificate or a claim of novel robust optimization theory. -/
noncomputable section
open Matrix
namespace GNC.Applications.OrbitalFuel.SharedBiasExample
open GNC GNC.ThrustSupport

def axis : Vec3 := ![0, 0, 1]
def plus (κ tau : ℝ) : Vec3 := ![tau, 0, κ]
def minus (κ tau : ℝ) : Vec3 := ![-tau, 0, κ]
def progress (a u v : ℝ) (q r : Vec3) : ℝ :=
  u*(q 2+a*q 0)+v*(r 2-a*r 0)
def Common (κ a u v : ℝ) : Prop :=
  ∀ q, q ∈ Cap axis κ → 1 ≤ progress a u v q q
def Independent (κ a u v : ℝ) : Prop :=
  ∀ q r, q ∈ Cap axis κ → r ∈ Cap axis κ → 1 ≤ progress a u v q r

theorem boundary_mem {κ tau : ℝ} (hs : κ^2+tau^2 = 1) :
    plus κ tau ∈ Cap axis κ ∧ minus κ tau ∈ Cap axis κ := by
  constructor <;> constructor
  all_goals norm_num [axis, plus, minus, dotProduct, Fin.sum_univ_succ,
    Matrix.cons_val_two] <;> nlinarith

theorem coordinate_bounds {κ tau : ℝ} (hk : 0 ≤ κ) (ht : 0 ≤ tau)
    (hs : κ^2+tau^2 = 1) (q : Vec3) (hq : q ∈ Cap axis κ) :
    κ ≤ q 2 ∧ -tau ≤ q 0 ∧ q 0 ≤ tau := by
  rcases hq with ⟨hunit, hax⟩
  norm_num [axis, dotProduct, Fin.sum_univ_succ] at hunit hax
  have hsq : (q 0)^2 ≤ tau^2 := by nlinarith [sq_nonneg (q 1)]
  exact ⟨hax, by nlinarith, by nlinarith⟩

theorem common_balanced {κ a : ℝ} (hk : 0 < κ) :
    Common κ a (1/(2*κ)) (1/(2*κ)) := by
  intro q hq
  have hax := hq.2
  norm_num [axis, dotProduct, Fin.sum_univ_succ] at hax
  have hid : progress a (1/(2*κ)) (1/(2*κ)) q q = q 2/κ := by
    dsimp [progress]
    ring
  rw [hid]
  exact (one_le_div hk).mpr hax

theorem common_lower {κ tau a u v : ℝ} (hk : 0 < κ)
    (hs : κ^2+tau^2 = 1) (huv : Common κ a u v) : 1/κ ≤ u+v := by
  have hp := huv (plus κ tau) (boundary_mem hs).1
  have hm := huv (minus κ tau) (boundary_mem hs).2
  norm_num [progress, plus, minus, Matrix.cons_val_two] at hp hm
  apply (div_le_iff₀ hk).mpr
  nlinarith

theorem independent_lower {κ tau a u v : ℝ} (hden : 0 < κ-a*tau)
    (hs : κ^2+tau^2 = 1) (huv : Independent κ a u v) :
    1/(κ-a*tau) ≤ u+v := by
  have h := huv (minus κ tau) (plus κ tau) (boundary_mem hs).2 (boundary_mem hs).1
  norm_num [progress, plus, minus, Matrix.cons_val_two] at h
  apply (div_le_iff₀ hden).mpr
  nlinarith

theorem independent_feasible {κ tau a u v : ℝ} (hk : 0 ≤ κ) (ht : 0 ≤ tau)
    (ha : 0 ≤ a) (hs : κ^2+tau^2 = 1) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hcost : 1 ≤ (u+v)*(κ-a*tau)) : Independent κ a u v := by
  intro q r hq hr
  have hq' := coordinate_bounds hk ht hs q hq
  have hr' := coordinate_bounds hk ht hs r hr
  have hlo : κ-a*tau ≤ q 2+a*q 0 := by nlinarith
  have hhi : κ-a*tau ≤ r 2-a*r 0 := by nlinarith
  have hl := mul_le_mul_of_nonneg_left hlo hu
  have hh := mul_le_mul_of_nonneg_left hhi hv
  dsimp [progress]
  nlinarith

/-- The exact fractional delta-v saving over the independent outer model.
Propellant has the same strict ordering, but not this exact percentage. -/
theorem relative_saving {κ tau a : ℝ} (hk : κ ≠ 0) (hd : κ-a*tau ≠ 0) :
    (1/(κ-a*tau)-1/κ)/(1/(κ-a*tau)) = a*tau/κ := by
  field_simp
  ring

/-- Common-bias reserve has a quadratic axial loss in the transverse radius. -/
theorem common_reserve {κ tau : ℝ} (hk : 0 < κ) (hs : κ^2+tau^2 = 1) :
    1/κ-1 = tau^2/(κ*(1+κ)) := by
  have hk0 : κ ≠ 0 := ne_of_gt hk
  have hp : 1+κ ≠ 0 := by positivity
  field_simp
  nlinarith

theorem strict_propellant_saving {κ tau a m exhaust : ℝ}
    (hat : 0 < a*tau) (hd : 0 < κ-a*tau)
    (hm : 0 < m) (he : 0 < exhaust) :
    GNC.Propellant.consumedMass m exhaust (1/κ) <
      GNC.Propellant.consumedMass m exhaust (1/(κ-a*tau)) := by
  apply GNC.Propellant.consumed_strictMono hm he
  exact one_div_lt_one_div_of_lt hd (by linarith)

end GNC.Applications.OrbitalFuel.SharedBiasExample
