import GNC.Magnus.MagnusJet

/-! Coefficient audit for the two-node Gauss–Legendre Magnus integrator.
The equation is LEFT-composed: Y' = A(t)Y. The complete finite calculation
includes Gauss nodes, quadrature, the commutator sign, and exponential
coefficients through degree four for an arbitrary cubic generator jet.
No analytic remainder, floating-point exponential, or concrete orbital
certificate follows from these finite identities alone. -/
noncomputable section
namespace GNC.Magnus
open Polynomial
variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- Formal coefficient recurrence forced by Y' = (a+t b+t² c+t³ d)Y. -/
def leftFlowCoeff (a b c d : A) : ℕ → A
  | 0 => 1
  | n+1 => ((n+1:ℝ)⁻¹) • (a * leftFlowCoeff a b c d n +
      (if n=0 then 0 else b*leftFlowCoeff a b c d (n-1)) +
      (if n<2 then 0 else c*leftFlowCoeff a b c d (n-2)) +
      (if n<3 then 0 else d*leftFlowCoeff a b c d (n-3)))

def leftExponent4 (a b c d : A) : Polynomial A :=
  monomial 1 a + monomial 2 ((1/2:ℝ) • b) +
  monomial 3 ((1/3:ℝ) • c - (1/12:ℝ) • comm a b) +
  monomial 4 ((1/4:ℝ) • d - (1/12:ℝ) • comm a c)

set_option maxRecDepth 4000 in
set_option maxHeartbeats 8000000 in
theorem leftExponent4_flow_coeff (a b c d : A) (n : ℕ) (hn : n ≤ 4) :
    expCoeff (leftExponent4 a b c d) n = leftFlowCoeff a b c d n := by
  interval_cases n <;>
    norm_num [expCoeff, leftExponent4, leftFlowCoeff, pow_succ, Polynomial.coeff_mul,
      Polynomial.coeff_monomial, Polynomial.coeff_one,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ] <;>
    magnus_nc

/-- Taylor samples at a dimensionless node, as a polynomial in the step size. -/
def nodeSample (a b c d : A) (s : ℝ) : Polynomial A :=
  monomial 0 a + monomial 1 (s • b) + monomial 2 ((s^2) • c) +
    monomial 3 ((s^3) • d)

/-- The implemented LEFT two-node Magnus step, with r = sqrt(3)/6. -/
def gaussLeftExponent (a b c d : A) (r : ℝ) : Polynomial A :=
  monomial 1 (1:A) * ((1/2:ℝ) •
      (nodeSample a b c d (1/2-r)+nodeSample a b c d (1/2+r))) -
    monomial 2 (1:A) * ((r/2) •
      comm (nodeSample a b c d (1/2-r)) (nodeSample a b c d (1/2+r)))

set_option maxRecDepth 4000 in
set_option maxHeartbeats 8000000 in
theorem gaussLeftExponent_coeff (a b c d : A) (r : ℝ) (hr : r^2 = (1/12:ℝ))
    (n : ℕ) (hn : n ≤ 4) :
    (gaussLeftExponent a b c d r).coeff n = (leftExponent4 a b c d).coeff n := by
  interval_cases n <;>
    norm_num [gaussLeftExponent, nodeSample, leftExponent4, comm,
      Polynomial.coeff_mul, Polynomial.coeff_monomial,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ] <;>
    (try simp only [smul_add, smul_sub, smul_smul, smul_mul_assoc, mul_smul_comm,
      sub_mul, mul_sub, add_mul, mul_add]) <;>
    match_scalars <;> ring_nf <;> norm_num [hr]

omit [Algebra ℝ A] in
theorem coeff_pow_congr_below {p q : Polynomial A} {n : ℕ}
    (h : ∀ j ≤ n, p.coeff j = q.coeff j) (k j : ℕ) (hj : j ≤ n) :
    (p^k).coeff j = (q^k).coeff j := by
  induction k generalizing j with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_succ, Polynomial.coeff_mul, Polynomial.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [ih i (hi'.trans hj), h (j-i) ((Nat.sub_le _ _).trans hj)]

theorem gauss_node_square : (Real.sqrt 3/6)^2 = (1/12:ℝ) := by
  rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
  norm_num

/-- The implemented Gauss exponent produces the actual LEFT ODE's formal
coefficients through degree four. This is a finite identity, not a bound
on a floating-point matrix exponential or an analytic remainder. -/
theorem gauss_left_flow_coeff (a b c d : A) (n : ℕ) (hn : n ≤ 4) :
    expCoeff (gaussLeftExponent a b c d (Real.sqrt 3/6)) n =
      leftFlowCoeff a b c d n := by
  rw [← leftExponent4_flow_coeff a b c d n hn]
  unfold expCoeff
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  exact coeff_pow_congr_below
    (fun j hj => gaussLeftExponent_coeff a b c d _ gauss_node_square j (hj.trans hn))
    k n le_rfl

theorem gauss_left_constant (a b c d : A) :
    (gaussLeftExponent a b c d (Real.sqrt 3/6)).coeff 0 = 0 := by
  rw [gaussLeftExponent_coeff a b c d _ gauss_node_square 0 (by omega)]
  simp [leftExponent4, Polynomial.coeff_monomial]

/-- Powers omitted by `expCoeff` cannot contribute at the requested degree. -/
theorem gauss_left_high_power (a b c d : A) (k n : ℕ) (hn : n < k) :
    (gaussLeftExponent a b c d (Real.sqrt 3/6)^k).coeff n = 0 :=
  coeff_pow_vanishes _ (gauss_left_constant a b c d) k n hn

end GNC.Magnus
