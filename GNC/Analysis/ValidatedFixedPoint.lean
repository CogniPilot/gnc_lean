import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic

/-! The a posteriori contraction certificate used by validated Picard/Taylor
integration. A checked defect and local Lipschitz bound prove an actual fixed
point in a prescribed ball. Checking the certificate does not require running
Picard iteration. Mathlib supplies Banach's fixed-point theorem.

To instantiate this for an ODE, T must be its Picard integral operator on a
complete path space, and the local bound must include truncation and arithmetic
errors. This module alone does not validate a Flow* or JuliaReach run.
-/
noncomputable section
open Metric Set
open scoped NNReal
namespace GNC.ValidatedFixedPoint
variable {E : Type*} [MetricSpace E] [CompleteSpace E]

theorem ball_certificate (T : E → E) (p : E) {k : ℝ≥0} {R δ : ℝ}
    (hk : k < 1) (hR : 0 ≤ R)
    (hL : LipschitzOnWith k T (closedBall p R))
    (hd : dist (T p) p ≤ δ) (hclose : δ+(k:ℝ)*R ≤ R) :
    ∃ z ∈ closedBall p R, T z = z ∧ dist z p ≤ δ/(1-(k:ℝ)) ∧
      ∀ w ∈ closedBall p R, T w = w → w = z := by
  have hp : p ∈ closedBall p R := mem_closedBall_self hR
  have hm : MapsTo T (closedBall p R) (closedBall p R) := by
    intro x hx
    change dist (T x) p ≤ R
    calc
      dist (T x) p ≤ dist (T x) (T p)+dist (T p) p := dist_triangle _ _ _
      _ ≤ (k:ℝ)*dist x p+δ := add_le_add (hL.dist_le_mul x hx p hp) hd
      _ ≤ (k:ℝ)*R+δ := add_le_add_left
        (mul_le_mul_of_nonneg_left hx k.coe_nonneg) _
      _ ≤ R := by linarith
  let S := closedBall p R
  have hs : IsComplete S := isClosed_closedBall.isComplete
  letI : CompleteSpace S := hs.completeSpace_coe
  letI : Nonempty S := ⟨⟨p,hp⟩⟩
  let F : S → S := fun x => ⟨T x, hm x.property⟩
  have hc : ContractingWith k F := by
    refine ⟨hk, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
    exact hL.dist_le_mul x x.property y y.property
  let z := hc.fixedPoint F
  have hz : F z = z := hc.fixedPoint_isFixedPt
  have hz' : T z.val = z.val := congrArg Subtype.val hz
  refine ⟨z.val,z.property,hz',?_,?_⟩
  · have he : dist (z:E) p ≤ (k:ℝ)*dist (z:E) p+δ := by
      calc
        dist (z:E) p = dist (T z.val) p := by rw [hz']
        _ ≤ dist (T z.val) (T p)+dist (T p) p := dist_triangle _ _ _
        _ ≤ (k:ℝ)*dist (z:E) p+δ :=
          add_le_add (hL.dist_le_mul z.val z.property p hp) hd
    have hkr : (k:ℝ) < 1 := by exact_mod_cast hk
    have hpos : (0:ℝ) < 1-k := by linarith
    apply (le_div_iff₀ hpos).mpr
    nlinarith
  · intro w hw hfix
    have hw' : F ⟨w,hw⟩ = ⟨w,hw⟩ := Subtype.ext hfix
    exact congrArg Subtype.val (hc.fixedPoint_unique' hw' hz)

/-- A closed-form radius certificate, with no inflation factor or convergence
tolerance. The contraction condition is mathematical, not a numerical fudge. -/
theorem direct_radius {k δ : ℝ} (hk : k < 1) :
    δ+k*(δ/(1-k)) = δ/(1-k) := by
  have hn : 1-k ≠ 0 := ne_of_gt (sub_pos.mpr hk)
  field_simp
  ring

end GNC.ValidatedFixedPoint
