import GNC.Analysis.BoundedODE

/-! Finite-horizon existence for a bounded time-dependent vector field.
An additive switched input can be absorbed into its continuous primitive;
Picard--Lindelof is applied to the resulting continuous equation.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Filter
open scoped Topology NNReal
namespace GNC.BoundedODE
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem exists_time_dependent (f : ℝ → E → E) (K L : ℝ≥0)
    (hK : ∀ t, LipschitzWith K (f t))
    (hc : Continuous (fun z : ℝ × E => f z.1 z.2))
    (hL : ∀ t x, ‖f t x‖ ≤ L) (x₀ : E) {T : ℝ} (hT : 0 ≤ T) :
    ∃ x : ℝ → E, Continuous x ∧ x 0 = x₀ ∧
      ∀ t ∈ Icc 0 T, HasDerivAt x (f t (x t)) t := by
  let a : ℝ≥0 := ⟨(L:ℝ)*(T+1), by positivity⟩
  let tbase : Icc (-1:ℝ) (T+1) := ⟨0, by constructor <;> linarith⟩
  have hp : IsPicardLindelof f tbase x₀ a 0 L K := by
    refine ⟨fun t _ => (hK t).lipschitzOnWith, ?_, fun t _ y _ => hL t y, ?_⟩
    · intro x _
      exact (hc.comp (continuous_id.prodMk continuous_const)).continuousOn
    · change (L:ℝ)*max (T+1-0) (0- -1) ≤ (L:ℝ)*(T+1)-0
      simp only [sub_zero, sub_neg_eq_add, zero_add]
      rw [max_eq_left (by linarith)]
  obtain ⟨y,hy₀,hy⟩ := hp.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  have hyc : ContinuousOn y (Icc (-1:ℝ) (T+1)) :=
    fun t ht => (hy t ht).continuousWithinAt
  let p : ℝ → ℝ := fun t => projIcc (-1) (T+1) (by linarith) t
  let x := y ∘ p
  have hpc : Continuous p := continuous_subtype_val.comp continuous_projIcc
  have hxeq {t : ℝ} (ht : t ∈ Icc (-1:ℝ) (T+1)) : x t = y t := by
    simp [x, p, projIcc_of_mem _ ht]
  refine ⟨x, hyc.comp_continuous hpc (fun t =>
    (projIcc (-1) (T+1) (by linarith) t).property), ?_, ?_⟩
  · rw [hxeq (by constructor <;> linarith)]
    exact hy₀
  · intro t ht
    have hm : Icc (-1:ℝ) (T+1) ∈ 𝓝 t :=
      Icc_mem_nhds (by linarith [ht.1]) (by linarith [ht.2])
    have he : x =ᶠ[𝓝 t] y := by
      filter_upwards [hm] with s hs
      exact hxeq hs
    rw [he.self_of_nhds]
    exact ((hy t (by constructor <;> linarith [ht.1,ht.2])).hasDerivAt hm).congr_of_eventuallyEq he

/-- The primitive need only be continuous; its derivative may jump at a
switch. The constructed curve minus the primitive solves the continuous
equation everywhere on the closed horizon. -/
theorem exists_with_primitive (f : ℝ → E → E) (K L : ℝ≥0)
    (hK : ∀ t, LipschitzWith K (f t))
    (hc : Continuous (fun z : ℝ × E => f z.1 z.2))
    (hL : ∀ t x, ‖f t x‖ ≤ L) (C : ℝ → E) (hC : Continuous C)
    (x₀ : E) {T : ℝ} (hT : 0 ≤ T) :
    ∃ x : ℝ → E, Continuous x ∧ x 0 = x₀ ∧
      ∀ t ∈ Icc 0 T, HasDerivAt (fun s => x s-C s) (f t (x t)) t := by
  let g := fun t y => f t (y+C t)
  have hgK (t : ℝ) : LipschitzWith K (g t) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_add_right] using (hK t).dist_le_mul (x+C t) (y+C t)
  have hgc : Continuous (fun z : ℝ × E => g z.1 z.2) :=
    hc.comp (continuous_fst.prodMk (continuous_snd.add (hC.comp continuous_fst)))
  obtain ⟨y,hy,hy₀,hdy⟩ := exists_time_dependent g K L hgK hgc
    (fun t y => hL t (y+C t)) (x₀-C 0) hT
  refine ⟨fun t => y t+C t, hy.add hC, by simp [hy₀], ?_⟩
  intro t ht
  simpa only [add_sub_cancel_right] using hdy t ht

end GNC.BoundedODE
