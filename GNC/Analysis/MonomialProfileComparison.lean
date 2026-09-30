import GNC.Analysis.MonomialSupersolutionComparison

/-! Pointwise comparison of time-growing and constant residual envelopes.
The constants 1/6 and 1/15 follow from integrating t² and t⁴ twice.
These are comparisons of proved supersolutions, not actual-error rankings. -/
noncomputable section
namespace GNC.MonomialSupersolution

/-- Factoring the known onset order retains its time dependence. -/
theorem factored_value {κ : ℝ} (n : ℕ) (hk : κ < pair (n+6)) (t : ℝ) :
    pair n * value κ n t = t^(n+2) *
      (1 + κ/pair (n+2)*t^2 + κ^2/(pair (n+2)*pair (n+4))*t^4 +
        κ^3/(pair (n+2)*pair (n+4)*(pair (n+6)-κ))*t^6) := by
  have hp := (pair_pos n).ne'
  have hq := (pair_pos (n+2)).ne'
  have hr := (pair_pos (n+4)).ne'
  have hk' : pair (n+6)-κ ≠ 0 := (sub_pos.mpr hk).ne'
  simp only [value, polynomial, Polynomial.eval_add, Polynomial.eval_monomial]
  dsimp only [six, four]
  simp only [pow_add]
  field_simp

/-- At every nonnegative time, the t^n-source envelope gains the factor
2 t^n / ((n+1)(n+2)) relative to the constant-source envelope. -/
theorem profile_le_constant {κ t : ℝ} (hκ : 0≤κ) (hk : κ<56)
    (ht : 0≤t) (n : ℕ) :
    value κ n t ≤ (2/pair n)*t^n*value κ 0 t := by
  have h0 : κ<pair (0+6) := by norm_num [pair]; exact hk
  have hn := hk.trans_le (closing_coefficient_lower n)
  have h2 : pair (0+2)≤pair (n+2) := pair_mono (by omega)
  have h4 : pair (0+4)≤pair (n+4) := pair_mono (by omega)
  have h6 : pair (0+6)-κ≤pair (n+6)-κ := sub_le_sub_right (pair_mono (by omega)) κ
  have hp2 := pair_pos (0+2)
  have hp4 := pair_pos (0+4)
  have hp6 : 0<pair (0+6)-κ := sub_pos.mpr h0
  have hn2 := pair_pos (n+2)
  have hn4 := pair_pos (n+4)
  have hn6 : 0<pair (n+6)-κ := sub_pos.mpr hn
  have hmain : pair n*value κ n t≤t^n*(pair 0*value κ 0 t) := by
    rw [factored_value n hn, factored_value 0 h0]
    simp only [Nat.zero_add, pow_add]
    rw [← mul_assoc]
    gcongr
  have hp := pair_pos n
  have hp0 : pair 0=2 := by norm_num [pair]
  rw [hp0] at hmain
  calc
    value κ n t ≤ (t^n*(2*value κ 0 t))/pair n := (le_div_iff₀ hp).mpr (by nlinarith [hmain])
    _ = _ := by ring

theorem constant_value_pos {κ t : ℝ} (hκ : 0≤κ) (hk : κ<56) (ht : 0<t) :
    0<value κ 0 t := by
  have hd : 0<56-κ := sub_pos.mpr hk
  norm_num [value, polynomial, pair, four, six]
  positivity

theorem value_nonneg {κ t : ℝ} (hκ : 0≤κ) (hk : κ<56) (ht : 0≤t) (n : ℕ) :
    0≤value κ n t := by
  have hp := pair_pos n
  have hf := four_pos n
  have hs := six_pos n
  have hd := sub_pos.mpr (hk.trans_le (closing_coefficient_lower n))
  simp only [value, polynomial, Polynomial.eval_add, Polynomial.eval_monomial]
  positivity

end GNC.MonomialSupersolution
