import GNC.Analysis.SymplecticResponse

/-! Variation of constants on burn/coast arcs. The trajectory is continuous
through switching times, but its derivative is required only inside each
arc. Rectangular thrust commands therefore need no fictitious derivative at
a switch. Summing the exact pullback increments telescopes the endpoints.
-/
noncomputable section
open Matrix
open scoped Matrix Matrix.Norms.Elementwise
namespace GNC.SymplecticResponse
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem arc_integral (F A : ℝ → Matrix n n ℝ) (J : Matrix n n ℝ)
    (x u : ℝ → n → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hFc : Continuous F) (hxc : Continuous x)
    (hF : ∀ t ∈ Set.Ioo a b, HasDerivAt F (A t*F t) t)
    (hA : ∀ t ∈ Set.Ioo a b, (A t)ᵀ*J+J*A t = 0)
    (hx : ∀ t ∈ Set.Ioo a b, HasDerivAt x (A t *ᵥ x t+u t) t)
    (hint : IntervalIntegrable (fun t => pullback J (F t) *ᵥ u t)
      MeasureTheory.volume a b) :
    (∫ t in a..b, pullback J (F t) *ᵥ u t) =
      pullback J (F b) *ᵥ x b-pullback J (F a) *ᵥ x a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab ?_ ?_ hint
  · exact (((continuous_const.matrix_mul hFc.matrix_transpose).matrix_mul continuous_const).matrix_mulVec
      hxc).continuousOn
  · intro t ht
    have h := mulVec_derivative (pullback_derivative (hF t ht) (hA t ht)) (hx t ht)
    simpa only [neg_mulVec, mulVec_add, mulVec_mulVec, neg_add_cancel_left] using h

theorem arc_sum (F A : ℝ → Matrix n n ℝ) (J : Matrix n n ℝ)
    (x u : ℝ → n → ℝ) (times : ℕ → ℝ) (N : ℕ)
    (hFc : Continuous F) (hxc : Continuous x)
    (horder : ∀ k < N, times k ≤ times (k+1))
    (hF : ∀ k < N, ∀ t ∈ Set.Ioo (times k) (times (k+1)), HasDerivAt F (A t*F t) t)
    (hA : ∀ k < N, ∀ t ∈ Set.Ioo (times k) (times (k+1)), (A t)ᵀ*J+J*A t = 0)
    (hx : ∀ k < N, ∀ t ∈ Set.Ioo (times k) (times (k+1)),
      HasDerivAt x (A t *ᵥ x t+u t) t)
    (hint : ∀ k < N, IntervalIntegrable (fun t => pullback J (F t) *ᵥ u t)
      MeasureTheory.volume (times k) (times (k+1))) :
    (∑ k ∈ Finset.range N, ∫ t in times k..times (k+1), pullback J (F t) *ᵥ u t) =
      pullback J (F (times N)) *ᵥ x (times N)-pullback J (F (times 0)) *ᵥ x (times 0) := by
  calc
    _ = ∑ k ∈ Finset.range N,
        (pullback J (F (times (k+1))) *ᵥ x (times (k+1))-
          pullback J (F (times k)) *ᵥ x (times k)) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hk' := Finset.mem_range.mp hk
      exact arc_integral F A J x u (horder k hk') hFc hxc
        (hF k hk') (hA k hk') (hx k hk') (hint k hk')
    _ = _ := Finset.sum_range_sub (fun k => pullback J (F (times k)) *ᵥ x (times k)) N

/-- Terminal response across a finite burn/coast partition. The reference
matrix is smooth on the horizon; the forced trajectory need only be smooth
inside each arc. No derivative of the trajectory is assumed at a switch. -/
theorem arc_endpoint (F A : ℝ → Matrix n n ℝ) (J : Matrix n n ℝ)
    (x u : ℝ → n → ℝ) (times : ℕ → ℝ) (N : ℕ) {T : ℝ}
    (hT : 0 ≤ T) (hJ : J*J = -1) (hFc : Continuous F) (hxc : Continuous x)
    (hF : ∀ t ∈ Set.Icc (0:ℝ) T, HasDerivAt F (A t*F t) t)
    (hA : ∀ t ∈ Set.Icc (0:ℝ) T, (A t)ᵀ*J+J*A t = 0)
    (hinit : F 0 = 1) (hzero : times 0 = 0) (hfinal : times N = T)
    (horder : ∀ k < N, times k ≤ times (k+1))
    (horizon : ∀ k < N, 0 ≤ times k ∧ times (k+1) ≤ T)
    (hx : ∀ k < N, ∀ t ∈ Set.Ioo (times k) (times (k+1)),
      HasDerivAt x (A t *ᵥ x t+u t) t)
    (hint : ∀ k < N, IntervalIntegrable (fun t => pullback J (F t) *ᵥ u t)
      MeasureTheory.volume (times k) (times (k+1))) :
    x T = F T *ᵥ (x 0+∑ k ∈ Finset.range N,
      ∫ t in times k..times (k+1), pullback J (F t) *ᵥ u t) := by
  have hdomain (k) (hk : k < N) (t) (ht : t ∈ Set.Ioo (times k) (times (k+1))) :
      t ∈ Set.Icc (0:ℝ) T :=
    ⟨(horizon k hk).1.trans ht.1.le, ht.2.le.trans (horizon k hk).2⟩
  have hs := arc_sum F A J x u times N hFc hxc horder
    (fun k hk t ht => hF t (hdomain k hk t ht))
    (fun k hk t ht => hA t (hdomain k hk t ht)) hx hint
  rw [hzero, hfinal] at hs
  have hp0 : pullback J (F 0) = 1 := by
    simp [pullback, hinit, hJ]
    ext i j
    simp
  have hleft : pullback J (F T)*F T = 1 := by
    have hp := SymplecticFlow.preserves_form F A J hF hA hinit T ⟨hT,le_rfl⟩
    change (-J)*(F T)ᵀ*J*F T = 1
    calc
      _ = (-J)*((F T)ᵀ*J*F T) := by noncomm_ring
      _ = 1 := by
        rw [hp, neg_mul, hJ]
        ext i j
        simp
  rw [hp0, one_mulVec] at hs
  rw [hs]
  have he : x 0+(pullback J (F T) *ᵥ x T-x 0) = pullback J (F T) *ᵥ x T := by abel
  rw [he, mulVec_mulVec, mul_eq_one_comm.mp hleft, one_mulVec]

end GNC.SymplecticResponse
