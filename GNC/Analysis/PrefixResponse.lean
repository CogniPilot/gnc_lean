import GNC.Analysis.PiecewiseResponse

/-! Exact response at every time prefix of a switched trajectory.
Clip every partition knot at the requested time. Completed arcs are
unchanged, the current arc is shortened, and all future arcs have length
zero. Open-arc dynamics suffice even at a command switch.
-/
noncomputable section
open Matrix
open scoped Matrix Matrix.Norms.Elementwise
namespace GNC.SymplecticResponse

theorem clipped_open {a b t s : ℝ} (hs : s ∈ Set.Ioo (min a t) (min b t)) :
    s ∈ Set.Ioo a b := by
  have hst : s < t := hs.2.trans_le (min_le_right b t)
  have hat : a ≤ t := by
    by_contra h
    rw [min_eq_right (le_of_not_ge h)] at hs
    exact (not_lt_of_ge hs.1.le) hst
  exact ⟨by simpa only [min_eq_left hat] using hs.1, hs.2.trans_le (min_le_left b t)⟩

theorem clipped_integrable {E : Type*} [NormedAddCommGroup E] {f : ℝ → E}
    {a b : ℝ} (hab : a ≤ b) (hf : IntervalIntegrable f MeasureTheory.volume a b) (t : ℝ) :
    IntervalIntegrable f MeasureTheory.volume (min a t) (min b t) := by
  by_cases hat : a ≤ t
  · rw [min_eq_left hat]
    apply hf.mono_set
    rw [Set.uIcc_of_le (le_min hab hat), Set.uIcc_of_le hab]
    exact Set.Icc_subset_Icc le_rfl (min_le_left b t)
  · have hta : t ≤ a := le_of_not_ge hat
    simp only [min_eq_right hta, min_eq_right (hta.trans hab)]
    simp

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Variation of constants for every real prefix, including partial burns.
The input integrals over future intervals vanish by coincident endpoints. -/
theorem piecewise_prefix (F A : ℝ → Matrix n n ℝ) (J : Matrix n n ℝ)
    (x : ℝ → n → ℝ) (u : ℕ → ℝ → n → ℝ) (times : ℕ → ℝ) (N : ℕ) {T t : ℝ}
    (ht : t ∈ Set.Icc (0:ℝ) T) (hJ : J*J = -1) (hFc : Continuous F) (hxc : Continuous x)
    (hF : ∀ s ∈ Set.Icc (0:ℝ) T, HasDerivAt F (A s*F s) s)
    (hA : ∀ s ∈ Set.Icc (0:ℝ) T, (A s)ᵀ*J+J*A s = 0)
    (hinit : F 0 = 1) (hzero : times 0 = 0) (hfinal : times N = T)
    (horder : ∀ k < N, times k ≤ times (k+1))
    (horizon : ∀ k < N, 0 ≤ times k ∧ times (k+1) ≤ T)
    (hx : ∀ k < N, ∀ s ∈ Set.Ioo (times k) (times (k+1)),
      HasDerivAt x (A s *ᵥ x s+u k s) s)
    (hint : ∀ k < N, IntervalIntegrable (fun s => pullback J (F s) *ᵥ u k s)
      MeasureTheory.volume (times k) (times (k+1))) :
    x t = F t *ᵥ (x 0+∑ k ∈ Finset.range N,
      ∫ s in min (times k) t..min (times (k+1)) t, pullback J (F s) *ᵥ u k s) := by
  apply piecewise_endpoint F A J x u (fun k => min (times k) t) N ht.1 hJ hFc hxc
    (fun s hs => hF s ⟨hs.1, hs.2.trans ht.2⟩)
    (fun s hs => hA s ⟨hs.1, hs.2.trans ht.2⟩) hinit
    (by dsimp only; rw [hzero, min_eq_left ht.1])
    (by dsimp only; rw [hfinal, min_eq_right ht.2])
    (fun k hk => min_le_min_right t (horder k hk))
    (fun k hk => ⟨le_min (horizon k hk).1 ht.1, min_le_right _ _⟩)
    (fun k hk s hs => hx k hk s (clipped_open hs))
    (fun k hk => clipped_integrable (horder k hk) (hint k hk) t)

end GNC.SymplecticResponse
