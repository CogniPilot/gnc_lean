import GNC.Analysis.MixedFlow
import Mathlib.Algebra.Polynomial.Derivative

/-! Finite Magnus coefficients for a right-composed polynomial generator.
These are kernel-checked formal jets. Analytic convergence and a numerical
bound on the omitted tail are separate obligations. -/
noncomputable section
namespace GNC.Magnus
open Polynomial
variable {A : Type*} [Ring A] [Algebra ℝ A]

def comm (a b : A) : A := a*b-b*a

macro "magnus_nc" : tactic => `(tactic|
  (try simp only [comm, sub_eq_add_neg, add_mul, mul_add, mul_assoc,
    smul_mul_assoc, mul_smul_comm, smul_add, smul_neg, smul_smul,
    neg_mul, mul_neg, zero_mul, mul_zero, one_mul, mul_one,
    pow_succ, pow_zero]
   module))

/-- Coefficients of the unique formal solution of Y'=Y(a+t b+t² c), Y(0)=1. -/
def flowCoeff (a b c : A) : ℕ → A
  | 0 => 1
  | n+1 => ((n+1:ℝ)⁻¹) • (flowCoeff a b c n * a +
      (if n=0 then 0 else flowCoeff a b c (n-1)*b) +
      (if n<2 then 0 else flowCoeff a b c (n-2)*c))

/-- The complete claimed exponent through time degree five, Eq. (32). -/
def exponent5 (a b c : A) : Polynomial A :=
  monomial 1 a + monomial 2 ((1/2:ℝ) • b) +
  monomial 3 ((1/3:ℝ) • c + (1/12:ℝ) • comm a b) +
  monomial 4 ((1/12:ℝ) • comm a c) +
  monomial 5 ((1/60:ℝ) • comm b c - (1/240:ℝ) • comm b (comm a b) -
    (1/720:ℝ) • comm a (comm a (comm a b)) +
    (1/360:ℝ) • comm a (comm a c))

/-- A finite coefficient of the exponential of a zero-constant-term series.
The omitted powers have order strictly greater than n. -/
def expCoeff (p : Polynomial A) (n : ℕ) : A :=
  ∑ k ∈ Finset.range (n+1), ((Nat.factorial k:ℝ)⁻¹) • (p^k).coeff n

/-- No omitted exponential power can affect the finite jet. -/
theorem coeff_pow_vanishes (p : Polynomial A) (hp : p.coeff 0 = 0)
    (k n : ℕ) (hn : n < k) : (p^k).coeff n = 0 := by
  induction k generalizing n with
  | zero => omega
  | succ k ih =>
    rw [pow_succ, Polynomial.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    apply Finset.sum_eq_zero
    intro i hi
    have hi' := Finset.mem_range.mp hi
    by_cases hik : i < k
    · rw [ih i hik, zero_mul]
    · rw [show n-i=0 by omega, hp, mul_zero]

theorem exponent5_constant (a b c : A) : (exponent5 a b c).coeff 0 = 0 := by
  simp [exponent5, Polynomial.coeff_monomial]

theorem linear_degree_four (a b : A) : (exponent5 a b 0).coeff 4 = 0 := by
  simp [exponent5, Polynomial.coeff_monomial, comm]

theorem linear_degree_five (a b : A) : (exponent5 a b 0).coeff 5 =
    -(1/240:ℝ) • comm b (comm a b) - (1/720:ℝ) • comm a (comm a (comm a b)) := by
  simp [exponent5, Polynomial.coeff_monomial, comm, neg_smul]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 8000000 in
theorem exponent5_flow_coeff (a b c : A) (n : ℕ) (hn : n ≤ 5) :
    expCoeff (exponent5 a b c) n = flowCoeff a b c n := by
  interval_cases n <;>
    norm_num [expCoeff, exponent5, flowCoeff, pow_succ, Polynomial.coeff_mul,
      Polynomial.coeff_monomial, Polynomial.coeff_one,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ] <;>
    magnus_nc

/-- Uniqueness of the formal ODE solution from its recursively forced coefficients. -/
theorem flowCoeff_unique (a b c : A) (f : ℕ → A) (h0 : f 0 = 1)
    (hstep : ∀ n, f (n+1) = ((n+1:ℝ)⁻¹) • (f n*a +
      (if n=0 then 0 else f (n-1)*b) +
      (if n<2 then 0 else f (n-2)*c))) : f = flowCoeff a b c := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simpa [flowCoeff] using h0
    | succ n =>
      rw [hstep, flowCoeff]
      rw [ih n (by omega), ih (n-1) (by omega), ih (n-2) (by omega)]

end GNC.Magnus
