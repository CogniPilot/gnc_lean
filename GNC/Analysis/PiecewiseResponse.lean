import GNC.Analysis.SymplecticArcResponse

/-! Variation of constants with a different forcing on each open arc.
Each forcing is an extension used only on its assigned interval. This lets
smooth burn/coast inputs coexist with a continuous, piecewise differentiable
trajectory, without an artificial derivative at a command switch.
-/
noncomputable section
open Matrix
open scoped Matrix Matrix.Norms.Elementwise
namespace GNC.SymplecticResponse
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem piecewise_sum (F A : ℝ → Matrix n n ℝ) (J : Matrix n n ℝ)
    (x : ℝ → n → ℝ) (u : ℕ → ℝ → n → ℝ) (times : ℕ → ℝ) (N : ℕ)
    (hFc : Continuous F) (hxc : Continuous x)
    (horder : ∀ k < N, times k ≤ times (k+1))
    (hF : ∀ k < N, ∀ t ∈ Set.Ioo (times k) (times (k+1)), HasDerivAt F (A t*F t) t)
    (hA : ∀ k < N, ∀ t ∈ Set.Ioo (times k) (times (k+1)), (A t)ᵀ*J+J*A t = 0)
    (hx : ∀ k < N, ∀ t ∈ Set.Ioo (times k) (times (k+1)),
      HasDerivAt x (A t *ᵥ x t+u k t) t)
    (hint : ∀ k < N, IntervalIntegrable (fun t => pullback J (F t) *ᵥ u k t)
      MeasureTheory.volume (times k) (times (k+1))) :
    (∑ k ∈ Finset.range N, ∫ t in times k..times (k+1), pullback J (F t) *ᵥ u k t) =
      pullback J (F (times N)) *ᵥ x (times N)-pullback J (F (times 0)) *ᵥ x (times 0) := by
  calc
    _ = ∑ k ∈ Finset.range N,
        (pullback J (F (times (k+1))) *ᵥ x (times (k+1))-
          pullback J (F (times k)) *ᵥ x (times k)) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hk' := Finset.mem_range.mp hk
      exact arc_integral F A J x (u k) (horder k hk') hFc hxc
        (hF k hk') (hA k hk') (hx k hk') (hint k hk')
    _ = _ := Finset.sum_range_sub (fun k => pullback J (F (times k)) *ᵥ x (times k)) N

theorem piecewise_endpoint (F A : ℝ → Matrix n n ℝ) (J : Matrix n n ℝ)
    (x : ℝ → n → ℝ) (u : ℕ → ℝ → n → ℝ) (times : ℕ → ℝ) (N : ℕ) {T : ℝ}
    (hT : 0 ≤ T) (hJ : J*J = -1) (hFc : Continuous F) (hxc : Continuous x)
    (hF : ∀ t ∈ Set.Icc (0:ℝ) T, HasDerivAt F (A t*F t) t)
    (hA : ∀ t ∈ Set.Icc (0:ℝ) T, (A t)ᵀ*J+J*A t = 0)
    (hinit : F 0 = 1) (hzero : times 0 = 0) (hfinal : times N = T)
    (horder : ∀ k < N, times k ≤ times (k+1))
    (horizon : ∀ k < N, 0 ≤ times k ∧ times (k+1) ≤ T)
    (hx : ∀ k < N, ∀ t ∈ Set.Ioo (times k) (times (k+1)),
      HasDerivAt x (A t *ᵥ x t+u k t) t)
    (hint : ∀ k < N, IntervalIntegrable (fun t => pullback J (F t) *ᵥ u k t)
      MeasureTheory.volume (times k) (times (k+1))) :
    x T = F T *ᵥ (x 0+∑ k ∈ Finset.range N,
      ∫ t in times k..times (k+1), pullback J (F t) *ᵥ u k t) := by
  have hdomain (k) (hk : k < N) (t) (ht : t ∈ Set.Ioo (times k) (times (k+1))) :
      t ∈ Set.Icc (0:ℝ) T :=
    ⟨(horizon k hk).1.trans ht.1.le, ht.2.le.trans (horizon k hk).2⟩
  have hs := piecewise_sum F A J x u times N hFc hxc horder
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

omit [DecidableEq n] in
/-- Separate an arc-dependent input from a common continuous forcing, such
as reference thrust or the nonlinear gravity remainder. -/
theorem piecewise_integral_add (F : ℝ → Matrix n n ℝ) (J : Matrix n n ℝ)
    (u : ℕ → ℝ → n → ℝ) (v : ℝ → n → ℝ) (times : ℕ → ℝ) (N : ℕ)
    (hu : ∀ k < N, IntervalIntegrable (fun t => pullback J (F t) *ᵥ u k t)
      MeasureTheory.volume (times k) (times (k+1)))
    (hv : ∀ k < N, IntervalIntegrable (fun t => pullback J (F t) *ᵥ v t)
      MeasureTheory.volume (times k) (times (k+1))) :
    (∑ k ∈ Finset.range N, ∫ t in times k..times (k+1),
      pullback J (F t) *ᵥ (u k t+v t)) =
    (∑ k ∈ Finset.range N, ∫ t in times k..times (k+1), pullback J (F t) *ᵥ u k t)+
      ∫ t in times 0..times N, pullback J (F t) *ᵥ v t := by
  simp_rw [mulVec_add]
  calc
    _ = ∑ k ∈ Finset.range N,
        ((∫ t in times k..times (k+1), pullback J (F t) *ᵥ u k t)+
          ∫ t in times k..times (k+1), pullback J (F t) *ᵥ v t) := by
      apply Finset.sum_congr rfl
      intro k hk
      exact intervalIntegral.integral_add (hu k (Finset.mem_range.mp hk))
        (hv k (Finset.mem_range.mp hk))
    _ = _ := by
      rw [Finset.sum_add_distrib, intervalIntegral.sum_integral_adjacent_intervals hv]

end GNC.SymplecticResponse
