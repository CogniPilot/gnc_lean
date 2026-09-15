import GNC.Analysis.MonomialSupersolution

/-! Quantify the benefit of retaining when a forcing residual grows.
The comparison uses the same nonnegative gain and the same endpoint source
size. It compares sufficient envelopes, not actual errors of all solvers. -/
noncomputable section
namespace GNC.MonomialSupersolution

theorem pair_mono {m n : ℕ} (h : m ≤ n) : pair m ≤ pair n := by
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg _
  have hm : (0:ℝ) ≤ m := Nat.cast_nonneg _
  have hmn : (m:ℝ) ≤ n := by exact_mod_cast h
  unfold pair
  nlinarith

theorem scaled_endpoint {κ : ℝ} (n : ℕ) (hk : κ < pair (n+6)) :
    pair n * value κ n 1 =
      1 + κ/pair (n+2) + κ^2/(pair (n+2)*pair (n+4)) +
        κ^3/(pair (n+2)*pair (n+4)*(pair (n+6)-κ)) := by
  have hp := (pair_pos n).ne'
  have hq := (pair_pos (n+2)).ne'
  have hr := (pair_pos (n+4)).ne'
  have hk' : pair (n+6)-κ ≠ 0 := (sub_pos.mpr hk).ne'
  simp only [value,polynomial,Polynomial.eval_add,Polynomial.eval_monomial,one_pow,mul_one]
  dsimp only [six,four]
  field_simp

/-- A t^n source needs at most 2/((n+1)(n+2)) times the endpoint envelope
of a constant source with the same endpoint magnitude. -/
theorem endpoint_le_constant {κ : ℝ} (hκ : 0 ≤ κ) (hk : κ < 56) (n : ℕ) :
    value κ n 1 ≤ (2/pair n)*value κ 0 1 := by
  have h0 : κ < pair (0+6) := by norm_num [pair]; exact hk
  have hn := hk.trans_le (closing_coefficient_lower n)
  have h2 : pair (0+2) ≤ pair (n+2) := pair_mono (by omega)
  have h4 : pair (0+4) ≤ pair (n+4) := pair_mono (by omega)
  have h6 : pair (0+6)-κ ≤ pair (n+6)-κ := sub_le_sub_right (pair_mono (by omega)) κ
  have hp2 := pair_pos (0+2)
  have hp4 := pair_pos (0+4)
  have hp6 : 0 < pair (0+6)-κ := sub_pos.mpr h0
  have hn2 := pair_pos (n+2)
  have hn4 := pair_pos (n+4)
  have hn6 : 0 < pair (n+6)-κ := sub_pos.mpr hn
  have hmain : pair n * value κ n 1 ≤ pair 0 * value κ 0 1 := by
    rw [scaled_endpoint n hn,scaled_endpoint 0 h0]
    gcongr
  have hpair : pair 0=2 := by norm_num [pair]
  rw [hpair] at hmain
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (pair_pos n)).2
  simpa only [mul_comm] using hmain

theorem sixth_order_improvement {κ : ℝ} (hκ : 0≤κ) (hk : κ<56) :
    value κ 6 1 ≤ value κ 0 1 / 28 := by
  have h := endpoint_le_constant hκ hk 6
  norm_num [pair] at h
  linarith

end GNC.MonomialSupersolution
