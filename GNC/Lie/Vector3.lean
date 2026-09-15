import GNC.Lie.SE23
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! Squared vector length and skew-flow invariance, independent of orbital dynamics. -/

noncomputable section
open Matrix
open scoped Matrix
namespace GNC

/-- Squared Euclidean length, avoiding the sup norm on the raw function type. -/
def lengthSq (v : Vec3) : ℝ := v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2

theorem lengthSq_eq_zero_iff (v : Vec3) : lengthSq v = 0 ↔ v = 0 := by
  constructor
  · intro h
    unfold lengthSq at h
    have h0 : v 0 = 0 := by nlinarith [sq_nonneg (v 1), sq_nonneg (v 2)]
    have h1 : v 1 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 2)]
    have h2 : v 2 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
    ext i; fin_cases i <;> assumption
  · rintro rfl; simp [lengthSq]

/-- The matched-control attitude equation (34c) preserves squared length. -/
theorem attitude_lengthSq_constant (ω r : ℝ → Vec3)
    (hr : ∀ t i, HasDerivAt (fun s => r s i) (-(ω t ⨯₃ r t) i) t)
    (t t₀ : ℝ) : lengthSq (r t) = lengthSq (r t₀) := by
  have hd : ∀ t, HasDerivAt (fun s => lengthSq (r s)) 0 t := by
    intro t
    convert (((hr t 0).pow 2).add ((hr t 1).pow 2)).add ((hr t 2).pow 2) using 1
    simp [cross_apply]; ring
  exact is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
    (fun s => (hd s).deriv) t t₀

/-- The zero-attitude-error set is dynamically invariant (Theorem 2). -/
theorem zero_attitude_invariant (ω r : ℝ → Vec3)
    (hr : ∀ t i, HasDerivAt (fun s => r s i) (-(ω t ⨯₃ r t) i) t)
    (t₀ : ℝ) (h₀ : r t₀ = 0) (t : ℝ) : r t = 0 := by
  apply (lengthSq_eq_zero_iff _).mp
  rw [attitude_lengthSq_constant ω r hr t t₀, h₀]
  simp [lengthSq]

end GNC
