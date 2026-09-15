import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Topology.Order.ProjIcc

/-! Finite-horizon existence for a bounded globally Lipschitz vector field.
The only existence result used is mathlib's Picard--Lindelof theorem.
An interior time projection gives a globally continuous representative while
preserving actual derivatives at both ends of the requested horizon.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Filter
open scoped Topology NNReal
namespace GNC.BoundedODE
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem exists_solution (f : E → E) (K L : ℝ≥0)
    (hK : LipschitzWith K f) (hL : ∀ x, ‖f x‖ ≤ L)
    (x₀ : E) {T : ℝ} (hT : 0 ≤ T) :
    ∃ x : ℝ → E, Continuous x ∧ x 0 = x₀ ∧
      ∀ t ∈ Icc 0 T, HasDerivAt x (f (x t)) t := by
  let a : ℝ≥0 := ⟨(L:ℝ)*(T+1), by positivity⟩
  let tbase : Icc (-1:ℝ) (T+1) := ⟨0, by constructor <;> linarith⟩
  have hp : IsPicardLindelof (fun _ y => f y) tbase x₀ a 0 L K := by
    refine ⟨fun _ _ => hK.lipschitzOnWith, fun _ _ => continuousOn_const,
      fun _ _ y _ => hL y, ?_⟩
    change (L:ℝ)*max (T+1-0) (0- -1) ≤ (L:ℝ)*(T+1)-0
    simp only [sub_zero, sub_neg_eq_add, zero_add]
    rw [max_eq_left (by linarith)]
  obtain ⟨y,hy₀,hy⟩ := hp.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  have hyc : ContinuousOn y (Icc (-1:ℝ) (T+1)) :=
    fun t ht => (hy t ht).continuousWithinAt
  let p : ℝ → ℝ := fun t => projIcc (-1) (T+1) (by linarith) t
  let x := y ∘ p
  have hpcont : Continuous p := continuous_subtype_val.comp continuous_projIcc
  have hxeq {t : ℝ} (ht : t ∈ Icc (-1:ℝ) (T+1)) : x t = y t := by
    simp [x, p, projIcc_of_mem _ ht]
  refine ⟨x, ?_, ?_, ?_⟩
  · exact hyc.comp_continuous hpcont (fun t => (projIcc (-1) (T+1) (by linarith) t).property)
  · rw [hxeq (by constructor <;> linarith)]
    exact hy₀
  · intro t ht
    have hmem : Icc (-1:ℝ) (T+1) ∈ 𝓝 t := Icc_mem_nhds (by linarith [ht.1]) (by linarith [ht.2])
    have he : x =ᶠ[𝓝 t] y := by
      filter_upwards [hmem] with s hs
      exact hxeq hs
    rw [he.self_of_nhds]
    exact ((hy t (by constructor <;> linarith [ht.1,ht.2])).hasDerivAt hmem).congr_of_eventuallyEq he

end GNC.BoundedODE
