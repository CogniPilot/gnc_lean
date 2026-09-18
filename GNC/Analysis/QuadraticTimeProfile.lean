import GNC.Analysis.PolynomialOrder

/-! Preserve double-zero initial data in a nonnegative polynomial bound. -/
namespace GNC.QuadraticTimeProfile
open Planning.PolynomialKernel Set

theorem value (p : List ℚ) (t : ℝ) :
    PolynomialOrder.value (0::0::p) t=t^2*PolynomialOrder.value p t := by
  simp only [PolynomialOrder.value,List.map_cons,map_zero,evaluate,zero_add]
  ring

theorem bound (p : List ℚ) (hp : PolynomialOrder.nonnegative p)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    PolynomialOrder.value (0::0::p) t≤PolynomialOrder.value (0::0::p) 1*t^2 := by
  rw [value,value,one_pow,one_mul,mul_comm (PolynomialOrder.value p 1)]
  exact mul_le_mul_of_nonneg_left (PolynomialOrder.value_le_endpoint p hp ht) (sq_nonneg t)

end GNC.QuadraticTimeProfile
