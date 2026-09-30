import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Tactic

/-! Entire coefficient functions for cancellation-free preintegration.
The error estimate reuses mathlib's alternating-series theorem. These are
real-arithmetic identities, not a verification of generated floating-point code.
-/
noncomputable section
namespace GNC.TrigonometricRemainder

def term (θ : ℝ) (n j : ℕ) : ℝ := (θ^2)^j / (n+2*j).factorial
def remainder (θ : ℝ) (n : ℕ) : ℝ := ∑' j : ℕ, (-1)^j * term θ n j
def polynomial (θ : ℝ) (n k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range k, (-1)^j * term θ n j

theorem term_summable (θ : ℝ) (n : ℕ) : Summable (term θ n) := by
  apply Summable.of_nonneg_of_le (fun j => by unfold term; positivity)
    (fun j => ?_) (Real.summable_pow_div_factorial (θ^2))
  unfold term
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  exact_mod_cast Nat.factorial_le (show j ≤ n+2*j by omega)

theorem term_antitone {θ : ℝ} (hθ : θ^2 ≤ 4) {n : ℕ} (hn : 1 ≤ n) :
    Antitone (term θ n) := by
  apply antitone_nat_of_succ_le
  intro j
  have hm : (1 : ℝ) ≤ (n+2*j : ℕ) := by exact_mod_cast (show 1 ≤ n+2*j by omega)
  have hprod : θ^2 ≤ (((n+2*j : ℕ) : ℝ)+2)*(((n+2*j : ℕ) : ℝ)+1) := by
    nlinarith
  unfold term
  rw [show n+2*(j+1) = (n+2*j+1)+1 by omega, Nat.factorial_succ,
    Nat.factorial_succ]
  push_cast
  rw [pow_succ]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have hh := mul_le_mul_of_nonneg_left hprod
    (show 0 ≤ (θ^2)^j * ((n+2*j).factorial : ℝ) by positivity)
  push_cast at hh
  nlinarith [hh]

theorem recurrence (θ : ℝ) (n : ℕ) :
    remainder θ n = 1/(n.factorial : ℝ) - θ^2 * remainder θ (n+2) := by
  have hs := (term_summable θ n).alternating
  unfold remainder
  rw [hs.tsum_eq_zero_add]
  simp only [term, pow_zero, one_mul, Nat.mul_zero, add_zero]
  have hshift (j : ℕ) :
      (-1 : ℝ)^(j+1) * ((θ^2)^(j+1)/(n+2*(j+1)).factorial) =
        -θ^2 * ((-1)^j * ((θ^2)^j/(n+2+2*j).factorial)) := by
    rw [show n+2*(j+1)=n+2+2*j by omega, pow_succ, pow_succ]
    ring
  simp_rw [hshift]
  rw [tsum_mul_left]
  ring

theorem remainder_zero (n : ℕ) : remainder 0 n = 1/(n.factorial : ℝ) := by
  rw [recurrence]
  ring

theorem approximation_bound {θ : ℝ} (hθ : θ^2 ≤ 4) {n : ℕ} (hn : 1 ≤ n)
    (k : ℕ) :
    |remainder θ n - polynomial θ n k| ≤ (θ^2)^k / (n+2*k).factorial := by
  exact alternating_series_error_bound (term θ n)
    (term_antitone hθ hn) (term_summable θ n) k

theorem remainder_cos (θ : ℝ) : remainder θ 0 = Real.cos θ := by
  rw [Real.cos_eq_tsum]
  unfold remainder term
  apply tsum_congr
  intro j
  simp only [zero_add, pow_mul]
  ring

theorem remainder_sin (θ : ℝ) : θ * remainder θ 1 = Real.sin θ := by
  rw [Real.sin_eq_tsum]
  unfold remainder term
  rw [← tsum_mul_left]
  apply tsum_congr
  intro j
  rw [show 1+2*j=2*j+1 by omega, pow_succ θ (2*j), pow_mul]
  ring

theorem remainder_four (θ : ℝ) (hθ : θ ≠ 0) :
    remainder θ 4 = (Real.cos θ - 1 + θ^2/2) / θ^4 := by
  have hc := remainder_cos θ
  rw [recurrence θ 0, recurrence θ 2] at hc
  norm_num at hc
  apply (eq_div_iff (pow_ne_zero 4 hθ)).mpr
  nlinarith only [hc]

theorem remainder_five (θ : ℝ) (hθ : θ ≠ 0) :
    remainder θ 5 = (Real.sin θ - θ + θ^3/6) / θ^5 := by
  have hs := remainder_sin θ
  rw [recurrence θ 1, recurrence θ 3] at hs
  norm_num at hs
  apply (eq_div_iff (pow_ne_zero 5 hθ)).mpr
  nlinarith only [hs]

theorem remainder_six (θ : ℝ) (hθ : θ ≠ 0) :
    remainder θ 6 = (1 - θ^2/2 + θ^4/24 - Real.cos θ) / θ^6 := by
  have hc := remainder_cos θ
  rw [recurrence θ 0, recurrence θ 2, recurrence θ 4] at hc
  norm_num at hc
  apply (eq_div_iff (pow_ne_zero 6 hθ)).mpr
  nlinarith only [hc]

theorem remainder_seven (θ : ℝ) (hθ : θ ≠ 0) :
    remainder θ 7 = (θ - θ^3/6 + θ^5/120 - Real.sin θ) / θ^7 := by
  have hs := remainder_sin θ
  rw [recurrence θ 1, recurrence θ 3, recurrence θ 5] at hs
  norm_num at hs
  apply (eq_div_iff (pow_ne_zero 7 hθ)).mpr
  nlinarith only [hs]

/-- The apparent eighth-order pole is removable; at zero use `remainder_zero`.
The equality is proved from the convergent series, not assumed as a definition. -/
theorem remainder_eight (θ : ℝ) (hθ : θ ≠ 0) :
    remainder θ 8 =
      (Real.cos θ - 1 + θ^2/2 - θ^4/24 + θ^6/720) / θ^8 := by
  have hc := remainder_cos θ
  rw [recurrence θ 0, recurrence θ 2, recurrence θ 4, recurrence θ 6] at hc
  norm_num at hc
  apply (eq_div_iff (pow_ne_zero 8 hθ)).mpr
  nlinarith only [hc]

theorem remainder_nine (θ : ℝ) (hθ : θ ≠ 0) :
    remainder θ 9 =
      (Real.sin θ - θ + θ^3/6 - θ^5/120 + θ^7/5040) / θ^9 := by
  have hs := remainder_sin θ
  rw [recurrence θ 1, recurrence θ 3, recurrence θ 5, recurrence θ 7] at hs
  norm_num at hs
  apply (eq_div_iff (pow_ne_zero 9 hθ)).mpr
  nlinarith only [hs]

/-- A regular graph affine in two consecutive entire remainders inherits
their weighted alternating-series bounds, at any truncation length. -/
theorem affine_evaluation_bound_general {θ : ℝ} (hθ : θ^2 ≤ 4)
    {n : ℕ} (hn : 1 ≤ n) (k : ℕ) (a b c : ℝ) :
    |(a+b*remainder θ n+c*remainder θ (n+1)) -
      (a+b*polynomial θ n k+c*polynomial θ (n+1) k)| ≤
      |b| * (θ^2)^k / ((n+2*k).factorial : ℝ) +
      |c| * (θ^2)^k / ((n+1+2*k).factorial : ℝ) := by
  have h8 := approximation_bound hθ hn k
  have h9 := approximation_bound hθ (show 1 ≤ n+1 by omega) k
  calc
    _ = |b*(remainder θ n-polynomial θ n k) +
          c*(remainder θ (n+1)-polynomial θ (n+1) k)| := by congr 1; ring
    _ ≤ |b*(remainder θ n-polynomial θ n k)| +
          |c*(remainder θ (n+1)-polynomial θ (n+1) k)| := abs_add_le _ _
    _ = |b| * |remainder θ n-polynomial θ n k| +
          |c| * |remainder θ (n+1)-polynomial θ (n+1) k| := by rw [abs_mul, abs_mul]
    _ ≤ |b| * ((θ^2)^k/((n+2*k).factorial : ℝ)) +
          |c| * ((θ^2)^k/((n+1+2*k).factorial : ℝ)) :=
      add_le_add (mul_le_mul_of_nonneg_left h8 (abs_nonneg _))
        (mul_le_mul_of_nonneg_left h9 (abs_nonneg _))
    _ = _ := by ring

/-- Depth-four specialization, before floating-point rounding or projection. -/
theorem affine_evaluation_bound {θ : ℝ} (hθ : θ^2 ≤ 4) (a b c : ℝ) :
    |(a+b*remainder θ 8+c*remainder θ 9) -
      (a+b*polynomial θ 8 9+c*polynomial θ 9 9)| ≤
      |b| * (θ^2)^9 / (Nat.factorial 26 : ℝ) +
      |c| * (θ^2)^9 / (Nat.factorial 27 : ℝ) := by
  exact affine_evaluation_bound_general hθ (show 1 ≤ 8 by omega) 9 a b c

end GNC.TrigonometricRemainder
