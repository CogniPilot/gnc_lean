import GNC.Analysis.MonomialSupersolution

/-! Time-profile bounds kept separate from the shared supersolution definitions. -/
noncomputable section
open Polynomial Set

namespace GNC.PolynomialSupersolution

/-- The zero-initial constant-source response grows at most quadratically
times its endpoint envelope on normalized time. -/
theorem quadratic_shape {κ t : ℝ} (hκ : 0≤κ) (hk : κ<56)
    (ht : t ∈ Icc (0:ℝ) 1) : value κ t≤value κ 1*t^2 := by
  have hd : 0<56-κ := sub_pos.mpr hk
  have he : value κ t=t^2*(1/2+κ/24*t^2+κ^2/720*t^4+
      κ^3/(720*(56-κ))*t^6) := by simp [value, polynomial]; ring
  rw [he]
  calc
    _ ≤ t^2*(1/2+κ/24+κ^2/720+κ^3/(720*(56-κ))) := by
      gcongr <;> exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ ht.1 ht.2)
    _ = _ := by simp [value, polynomial]; ring

end GNC.PolynomialSupersolution

namespace GNC.MonomialSupersolution

theorem value_le_endpoint {κ t : ℝ} (n : ℕ) (hκ : 0≤κ) (hk : κ<56)
    (ht : t ∈ Icc (0:ℝ) 1) : value κ n t≤value κ n 1 := by
  have hd : 0<pair (n+6)-κ := sub_pos.mpr (hk.trans_le (closing_coefficient_lower n))
  have hp := pair_pos n
  have hf := four_pos n
  have hs := six_pos n
  simp only [value, polynomial, Polynomial.eval_add, Polynomial.eval_monomial,
    one_pow, mul_one]
  gcongr <;> exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ ht.1 ht.2)

end GNC.MonomialSupersolution
