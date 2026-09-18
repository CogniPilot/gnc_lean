import GNC.Magnus.MagnusJet

/-! Finite Magnus coefficients for a left-composed polynomial generator.
The right-composed flow Y' = Y N(t) is treated in `GNC.Magnus.MagnusJet`; here the
left-composed flow Z' = N(t) Z receives the same kernel-checked jet through time
degree five, and the two jets are related by the parity map of Lemma 1:
Ξ^L(N) = -Ξ^R(-N), so brackets with an even number of generator letters change
sign between the conventions and brackets with an odd number do not. The linear
generator specialization gives the left column of Table II. -/
noncomputable section
namespace GNC.Magnus
open Polynomial
variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- Coefficients of the unique formal solution of Z'=(a+t b+t² c)Z, Z(0)=1. -/
def leftStemCoeff (a b c : A) : ℕ → A
  | 0 => 1
  | n+1 => ((n+1:ℝ)⁻¹) • (a * leftStemCoeff a b c n +
      (if n=0 then 0 else b * leftStemCoeff a b c (n-1)) +
      (if n<2 then 0 else c * leftStemCoeff a b c (n-2)))

/-- The exponent of the left-composed flow through time degree five. Relative to
Eq. (32) the even-letter brackets `[a,b]`, `[a,c]`, `[b,c]` and `[a,[a,[a,b]]]`
carry the opposite sign, while the odd-letter brackets `[b,[a,b]]` and `[a,[a,c]]`
keep theirs (Lemma 1). -/
def exponent5Left (a b c : A) : Polynomial A :=
  monomial 1 a + monomial 2 ((1/2:ℝ) • b) +
  monomial 3 ((1/3:ℝ) • c - (1/12:ℝ) • comm a b) +
  monomial 4 (-(1/12:ℝ) • comm a c) +
  monomial 5 (-(1/60:ℝ) • comm b c - (1/240:ℝ) • comm b (comm a b) +
    (1/720:ℝ) • comm a (comm a (comm a b)) +
    (1/360:ℝ) • comm a (comm a c))

theorem exponent5Left_constant (a b c : A) : (exponent5Left a b c).coeff 0 = 0 := by
  simp [exponent5Left, Polynomial.coeff_monomial]

/-- Table II, left column, grade T⁴: the linear generator has no degree-four term. -/
theorem left_linear_degree_four (a b : A) : (exponent5Left a b 0).coeff 4 = 0 := by
  simp [exponent5Left, Polynomial.coeff_monomial, comm]

/-- Table II, left column, grade T⁵: the three-letter bracket keeps the coefficient
-1/240 of the right convention and the four-letter bracket flips to +1/720. -/
theorem left_linear_degree_five (a b : A) : (exponent5Left a b 0).coeff 5 =
    -(1/240:ℝ) • comm b (comm a b) + (1/720:ℝ) • comm a (comm a (comm a b)) := by
  simp [exponent5Left, Polynomial.coeff_monomial, comm, neg_smul]

/-- Lemma 1, parity map: the left exponent is the negated right exponent of the
negated generator, Ξ^L(a,b,c) = -Ξ^R(-a,-b,-c). -/
theorem parity (a b c : A) : exponent5Left a b c = -(exponent5 (-a) (-b) (-c)) := by
  unfold exponent5Left exponent5
  simp only [neg_add, ← Polynomial.monomial_neg]
  congr 1
  · congr 1
    · congr 1
      · congr 1
        · congr 1; magnus_nc
        · congr 1; magnus_nc
      · congr 1; magnus_nc
    · congr 1; magnus_nc
  · congr 1; magnus_nc

set_option maxRecDepth 4000 in
set_option maxHeartbeats 8000000 in
/-- The exponential of `exponent5Left` reproduces the left flow through degree five. -/
theorem exponent5Left_flow_coeff (a b c : A) (n : ℕ) (hn : n ≤ 5) :
    expCoeff (exponent5Left a b c) n = leftStemCoeff a b c n := by
  interval_cases n <;>
    norm_num [expCoeff, exponent5Left, leftStemCoeff, pow_succ, Polynomial.coeff_mul,
      Polynomial.coeff_monomial, Polynomial.coeff_one,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ] <;>
    magnus_nc

/-- Uniqueness of the formal left-flow solution from its recursively forced coefficients. -/
theorem leftFlowCoeff_unique (a b c : A) (f : ℕ → A) (h0 : f 0 = 1)
    (hstep : ∀ n, f (n+1) = ((n+1:ℝ)⁻¹) • (a * f n +
      (if n=0 then 0 else b * f (n-1)) +
      (if n<2 then 0 else c * f (n-2)))) : f = leftStemCoeff a b c := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simpa [leftStemCoeff] using h0
    | succ n =>
      rw [hstep, leftStemCoeff]
      rw [ih n (by omega), ih (n-1) (by omega), ih (n-2) (by omega)]

end GNC.Magnus
