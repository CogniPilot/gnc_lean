import GNC.Analysis.PolynomialOrder

/-! Executable zero-prefix checks turn polynomial coefficient bounds into
whole-interval time profiles. The argument may be any bounded rate times
time; irrational phase rates need not be rounded in the polynomial. -/
namespace GNC.PolynomialTimeProfile
open Planning.PolynomialKernel PolynomialBounds PolynomialOrder Set

def zeroPrefix : ℕ → List ℚ → Prop
  | 0, _ => True
  | _+1, [] => True
  | n+1, a::p => a=0 ∧ zeroPrefix n p

instance (n : ℕ) (p : List ℚ) : Decidable (zeroPrefix n p) := by
  induction n generalizing p with
  | zero => exact isTrue trivial
  | succ n ih => cases p <;> unfold zeroPrefix <;> infer_instance

theorem bound_nonneg (p : List ℚ) {h : ℚ} (hh : 0≤h) : 0≤bound p h := by
  have he := bound_sound p (x := 0) (by simpa using (show (0:ℝ)≤h by exact_mod_cast hh))
  exact_mod_cast (abs_nonneg _).trans he

/-- A zero prefix proves the power of time; no sample grid is involved. -/
theorem profile_bound (p : List ℚ) (n : ℕ) (hz : zeroPrefix n p)
    {h : ℚ} (hh : 0≤h) {s t : ℝ} (hs : |s|≤h) (ht : t∈Icc (0:ℝ) 1) :
    |value p (s*t)|≤(bound p h:ℝ)*t^n := by
  have hhR : (0:ℝ)≤h := by exact_mod_cast hh
  induction n generalizing p with
  | zero =>
    simpa only [pow_zero,mul_one] using bound_sound p (x := s*t) (by
      rw [abs_mul,abs_of_nonneg ht.1]
      exact (mul_le_mul_of_nonneg_right hs ht.1).trans (mul_le_of_le_one_right hhR ht.2))
  | succ n ih =>
    cases p with
    | nil => simp [value,evaluate,bound]
    | cons a p =>
      obtain ⟨rfl,hz⟩ := hz
      have hind := ih p hz
      rw [show value (0::p) (s*t) = 0+s*t*value p (s*t) by simp [value,evaluate]]
      rw [zero_add,abs_mul,abs_mul,abs_of_nonneg ht.1]
      have he : (bound (0::p) h:ℝ)=(h:ℝ)*(bound p h:ℝ) := by
        simp [bound,evaluate]
      rw [he,pow_succ]
      calc
        _ ≤ (h:ℝ)*t*((bound p h:ℝ)*t^n) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hs ht.1) hind (abs_nonneg _)
            (mul_nonneg hhR ht.1)
        _ = _ := by ring

end GNC.PolynomialTimeProfile
