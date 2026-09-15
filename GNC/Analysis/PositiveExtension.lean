import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.Calculus.Deriv.Basic

/-! A globally positive continuous representative of a finite-horizon curve.
Time projection is performed outside a neighborhood of the horizon, so the
curve and all local derivative statements agree at every mission time.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Filter
open scoped Topology
namespace GNC.PositiveExtension
variable {E : Type*} [TopologicalSpace E]

theorem exists_positive (x : ℝ → E) (hx : Continuous x) (r : E → ℝ) (hr : Continuous r)
    {T : ℝ} (hT : 0 ≤ T) (hp : ∀ t ∈ Icc (0:ℝ) T, 0 < r (x t)) :
    ∃ y : ℝ → E, Continuous y ∧ (∀ t, 0 < r (y t)) ∧
      ∀ t ∈ Icc (0:ℝ) T, y =ᶠ[𝓝 t] x := by
  obtain ⟨δ,hδ,hsub⟩ := isCompact_Icc.exists_cthickening_subset_open
    (isOpen_lt continuous_const (hr.comp hx)) hp
  let p : ℝ → ℝ := fun t => projIcc (-δ) (T+δ) (by linarith) t
  have hpc : Continuous p := continuous_subtype_val.comp continuous_projIcc
  have hpI (t : ℝ) : p t ∈ Icc (-δ) (T+δ) := (projIcc (-δ) (T+δ) (by linarith) t).property
  refine ⟨x ∘ p, hx.comp hpc, ?_, ?_⟩
  · intro t
    apply hsub
    by_cases hleft : p t < 0
    · apply mem_cthickening_of_dist_le (p t) 0 δ (Icc (0:ℝ) T) ⟨le_rfl,hT⟩
      rw [Real.dist_eq, sub_zero, abs_of_neg hleft]
      linarith [(hpI t).1]
    · by_cases hright : T < p t
      · apply mem_cthickening_of_dist_le (p t) T δ (Icc (0:ℝ) T) ⟨hT,le_rfl⟩
        rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hright)]
        linarith [(hpI t).2]
      · exact self_subset_cthickening (δ := δ) (Icc (0:ℝ) T) ⟨le_of_not_gt hleft,le_of_not_gt hright⟩
  · intro t ht
    have hm : Icc (-δ) (T+δ) ∈ 𝓝 t := Icc_mem_nhds (by linarith [ht.1]) (by linarith [ht.2])
    filter_upwards [hm] with s hs
    simp [Function.comp_apply, p, projIcc_of_mem _ hs]

end GNC.PositiveExtension
