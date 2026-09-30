import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-! Entire confluent hypergeometric functions with positive real denominator.
The functions are defined by their explicit convergent coefficient series;
no special-function ODE or convergence fact is assumed as an axiom. -/
noncomputable section
open Filter Set Metric
open scoped Topology
namespace GNC.SpecialFunctions

def kummerNumerator (a : ℂ) (b : ℝ) : ℕ → ℂ
  | 0 => 1
  | n+1 => kummerNumerator a b n * (a+n) / ((b:ℂ)+n)

def kummerMajorant (a : ℂ) (b : ℝ) : ℝ := ‖a‖/b+1

theorem kummerMajorant_pos (a : ℂ) {b : ℝ} (hb : 0 < b) :
    0 < kummerMajorant a b := by unfold kummerMajorant; positivity

theorem kummer_ratio_bound (a : ℂ) {b : ℝ} (hb : 0 < b) (n : ℕ) :
    ‖(a+n)/((b:ℂ)+n)‖ ≤ kummerMajorant a b := by
  rw [norm_div]
  have hn : ‖(n:ℂ)‖ = (n:ℝ) := by simp
  have hd : ‖(b:ℂ)+n‖ = b+n := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_add, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hd]
  apply (div_le_iff₀ (by positivity : 0 < b+(n:ℝ))).mpr
  have h := norm_add_le a (n:ℂ)
  rw [hn] at h
  unfold kummerMajorant
  have he : (‖a‖/b+1)*(b+n) = ‖a‖+n+b+‖a‖/b*n := by
    field_simp
    ring
  rw [he]
  have hp : 0 ≤ ‖a‖/b*(n:ℝ) := by positivity
  linarith

theorem kummerNumerator_bound (a : ℂ) {b : ℝ} (hb : 0 < b) (n : ℕ) :
    ‖kummerNumerator a b n‖ ≤ kummerMajorant a b ^ n := by
  induction n with
  | zero => simp [kummerNumerator]
  | succ n ih =>
    rw [kummerNumerator, mul_div_assoc, norm_mul, pow_succ]
    exact mul_le_mul ih (kummer_ratio_bound a hb n) (norm_nonneg _)
      (pow_nonneg (kummerMajorant_pos a hb).le _)

def kummerTerm (a : ℂ) (b : ℝ) (j n : ℕ) (z : ℂ) : ℂ :=
  kummerNumerator a b (n+j) / (n.factorial:ℂ) * z^n

def kummerJet (a : ℂ) (b : ℝ) (j : ℕ) (z : ℂ) : ℂ :=
  ∑' n, kummerTerm a b j n z

def kummer (a : ℂ) (b : ℝ) (z : ℂ) : ℂ := kummerJet a b 0 z

theorem kummerTerm_bound (a : ℂ) {b : ℝ} (hb : 0 < b) (j n : ℕ) (z : ℂ) :
    ‖kummerTerm a b j n z‖ ≤
      kummerMajorant a b ^ j * (kummerMajorant a b*‖z‖)^n / n.factorial := by
  unfold kummerTerm
  rw [norm_mul, norm_div, norm_pow]
  simp only [Complex.norm_natCast]
  calc
    _ ≤ (kummerMajorant a b^(n+j)/(n.factorial:ℝ))*‖z‖^n :=
      mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (kummerNumerator_bound a hb _) (by positivity))
        (by positivity)
    _ = _ := by rw [pow_add, mul_pow]; ring

theorem kummerTerm_summable (a : ℂ) {b : ℝ} (hb : 0 < b) (j : ℕ) (z : ℂ) :
    Summable (fun n => kummerTerm a b j n z) := by
  apply Summable.of_norm_bounded
    ((Real.summable_pow_div_factorial (kummerMajorant a b*‖z‖)).mul_left
      (kummerMajorant a b^j))
  intro n
  simpa only [mul_div_assoc] using kummerTerm_bound a hb j n z

def kummerTermDerivative (a : ℂ) (b : ℝ) (j : ℕ) : ℕ → ℂ → ℂ
  | 0 => fun _ => 0
  | n+1 => kummerTerm a b (j+1) n

theorem kummerTerm_hasDerivAt (a : ℂ) (b : ℝ) (j n : ℕ) (z : ℂ) :
    HasDerivAt (kummerTerm a b j n) (kummerTermDerivative a b j n z) z := by
  cases n with
  | zero =>
    convert hasDerivAt_const z (kummerNumerator a b j) using 1
    funext u
    simp [kummerTerm]
  | succ n =>
    have h := (hasDerivAt_pow (n+1) z).const_mul
      (kummerNumerator a b (n+1+j) / ((n+1).factorial:ℂ))
    convert h using 1
    simp only [kummerTermDerivative, kummerTerm, Nat.factorial_succ,
      Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel]
    rw [show n+(j+1)=n+1+j by omega]
    field_simp


def kummerDerivativeMajorant (a : ℂ) (b r : ℝ) (j : ℕ) : ℕ → ℝ
  | 0 => 0
  | n+1 => kummerMajorant a b^(j+1) *
      (kummerMajorant a b*r)^n / n.factorial

theorem kummerDerivativeMajorant_summable (a : ℂ) (b r : ℝ) (j : ℕ) :
    Summable (kummerDerivativeMajorant a b r j) := by
  rw [← summable_nat_add_iff 1]
  simpa only [kummerDerivativeMajorant, mul_div_assoc] using
    (Real.summable_pow_div_factorial (kummerMajorant a b*r)).mul_left
      (kummerMajorant a b^(j+1))

theorem kummerJet_hasDerivAt (a : ℂ) {b : ℝ} (hb : 0 < b) (j : ℕ) (z : ℂ) :
    HasDerivAt (kummerJet a b j) (kummerJet a b (j+1) z) z := by
  let r := ‖z‖+1
  have hr : 0 < r := by dsimp [r]; positivity
  have hbound : ∀ n u, u ∈ ball (0:ℂ) r →
      ‖kummerTermDerivative a b j n u‖ ≤ kummerDerivativeMajorant a b r j n := by
    intro n u hu
    have hu' : ‖u‖ ≤ r := by simpa [mem_ball, dist_zero_right] using (show dist u 0 ≤ r from (mem_ball.mp hu).le)
    cases n with
    | zero => simp [kummerTermDerivative, kummerDerivativeMajorant]
    | succ n =>
      apply (kummerTerm_bound a hb (j+1) n u).trans
      dsimp [kummerTermDerivative, kummerDerivativeMajorant]
      have hC := (kummerMajorant_pos a hb).le
      gcongr <;> positivity
  have h := hasDerivAt_tsum_of_isPreconnected
    (kummerDerivativeMajorant_summable a b r j)
    isOpen_ball (convex_ball (0:ℂ) r).isPreconnected
    (fun n u _ => kummerTerm_hasDerivAt a b j n u) hbound
    (show (0:ℂ) ∈ ball 0 r by simp [hr]) (kummerTerm_summable a hb j 0)
    (show z ∈ ball 0 r by simp [r])
  change HasDerivAt (kummerJet a b j) _ z at h
  convert h using 1
  have hs : Summable (fun n => kummerTermDerivative a b j n z) := by
    rw [← summable_nat_add_iff 1]
    exact kummerTerm_summable a hb (j+1) z
  rw [hs.tsum_eq_zero_add]
  simp only [kummerTermDerivative, zero_add, kummerJet]

theorem kummerJet_zero (a : ℂ) (b : ℝ) (j : ℕ) :
    kummerJet a b j 0 = kummerNumerator a b j := by
  rw [kummerJet, tsum_eq_single 0]
  · simp [kummerTerm]
  · intro n hn
    simp [kummerTerm, zero_pow hn]

theorem kummer_zero (a : ℂ) (b : ℝ) : kummer a b 0 = 1 := by
  simp [kummer, kummerJet_zero, kummerNumerator]


theorem kummerNumerator_step (a : ℂ) {b : ℝ} (hb : 0 < b) (n : ℕ) :
    ((b:ℂ)+n)*kummerNumerator a b (n+1) = (a+n)*kummerNumerator a b n := by
  have hd : (b:ℂ)+(n:ℂ) ≠ 0 := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_add]
    exact_mod_cast (ne_of_gt (show 0 < b+(n:ℝ) by positivity))
  rw [kummerNumerator]
  field_simp

theorem kummerTerm_weighted_succ (a : ℂ) (b : ℝ) (j n : ℕ) (z : ℂ) :
    ((n+1:ℕ):ℂ)*kummerTerm a b j (n+1) z =
      z*kummerTerm a b (j+1) n z := by
  simp only [kummerTerm, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  rw [show n+1+j=n+(j+1) by omega, pow_succ]
  field_simp

theorem kummerTerm_weighted_summable (a : ℂ) {b : ℝ} (hb : 0 < b) (j : ℕ) (z : ℂ) :
    Summable (fun n : ℕ => (n:ℂ)*kummerTerm a b j n z) := by
  rw [← summable_nat_add_iff 1]
  simpa only [kummerTerm_weighted_succ] using (kummerTerm_summable a hb (j+1) z).mul_left z

theorem kummerJet_weighted (a : ℂ) {b : ℝ} (hb : 0 < b) (j : ℕ) (z : ℂ) :
    ∑' n : ℕ, (n:ℂ)*kummerTerm a b j n z = z*kummerJet a b (j+1) z := by
  rw [(kummerTerm_weighted_summable a hb j z).tsum_eq_zero_add]
  simp only [Nat.cast_zero, zero_mul, zero_add, kummerTerm_weighted_succ, tsum_mul_left,
    kummerJet]

/-- The explicit entire series solves Kummer's differential equation. -/
theorem kummer_ode (a : ℂ) {b : ℝ} (hb : 0 < b) (z : ℂ) :
    z*kummerJet a b 2 z+((b:ℂ)-z)*kummerJet a b 1 z-a*kummerJet a b 0 z = 0 := by
  have hn (n : ℕ) :
      (b:ℂ)*kummerTerm a b 1 n z+(n:ℂ)*kummerTerm a b 1 n z-
      (a*kummerTerm a b 0 n z+(n:ℂ)*kummerTerm a b 0 n z) = 0 := by
    dsimp [kummerTerm]
    linear_combination (z^n/(n.factorial:ℂ)) * kummerNumerator_step a hb n
  have hh : (∑' n : ℕ,
      ((b:ℂ)*kummerTerm a b 1 n z+(n:ℂ)*kummerTerm a b 1 n z-
      (a*kummerTerm a b 0 n z+(n:ℂ)*kummerTerm a b 0 n z))) = 0 := by
    simp only [hn, tsum_zero]
  have hs0 := kummerTerm_summable a hb 0 z
  have hs1 := kummerTerm_summable a hb 1 z
  have hw0 := kummerTerm_weighted_summable a hb 0 z
  have hw1 := kummerTerm_weighted_summable a hb 1 z
  rw [Summable.tsum_sub ((hs1.mul_left (b:ℂ)).add hw1) ((hs0.mul_left a).add hw0),
    Summable.tsum_add (hs1.mul_left (b:ℂ)) hw1,
    Summable.tsum_add (hs0.mul_left a) hw0,
    tsum_mul_left, tsum_mul_left, kummerJet_weighted a hb 1 z,
    kummerJet_weighted a hb 0 z] at hh
  change (b:ℂ)*kummerJet a b 1 z+z*kummerJet a b 2 z-
    (a*kummerJet a b 0 z+z*kummerJet a b 1 z) = 0 at hh
  linear_combination hh

end GNC.SpecialFunctions


