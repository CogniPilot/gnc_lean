import GNC.Magnus.FohHigherCertificate

/-! Exact finite time-degree checks for the midpoint Magnus candidates.

The exponentials of the FOH6 and FOH8 candidates agree with the
unique formal right-flow coefficients through degrees six and eight. These
are finite algebraic identities, not assumptions about an infinite Magnus
series or claims about a floating-point implementation.

The proof first caches the midpoint coefficients. Leading time monomials are
pruned before convolution; commutators stay opaque until coefficient extraction
is finished. The exponential check then uses coefficient-level power recursion,
with zero-valuation pruning, while keeping the exponent polynomial opaque.
-/
noncomputable section
namespace GNC.Magnus
open Polynomial
variable {A : Type*} [Ring A] [Algebra ℝ A]
def cachedMidpoint8Coeff (a b : A) : ℕ → A
  | 0 => 0
  | 1 => a
  | 2 => (1/2:ℝ) • b
  | 3 => (1/12:ℝ) • comm a b
  | 4 => 0
  | 5 => -(1/240:ℝ) • comm b (comm a b) - (1/720:ℝ) • comm a (comm a (comm a b))
  | 6 => -(1/1440:ℝ) • (comm b (comm a (comm a b)) + comm a (comm b (comm a b)))
  | 7 => -(1/2880:ℝ) • comm b (comm b (comm a b)) +
      (1/30240:ℝ) • comm a (comm a (comm a (comm a (comm a b)))) +
      (1/10080:ℝ) • comm a (comm a (comm b (comm a b))) -
      (1/7560:ℝ) • comm (comm a b) (comm a (comm a b)) +
      (1/6720:ℝ) • comm b (comm b (comm a b))
  | 8 => (1/60480:ℝ) •
      (comm b (comm a (comm a (comm a (comm a b)))) +
       comm a (comm b (comm a (comm a (comm a b)))) +
       comm a (comm a (comm b (comm a (comm a b)))) +
       comm a (comm a (comm a (comm b (comm a b))))) +
      (1/20160:ℝ) • (comm b (comm a (comm b (comm a b))) +
        comm a (comm b (comm b (comm a b)))) -
      (1/15120:ℝ) • comm (comm a b) (comm b (comm a b))
  | _ => 0
theorem coeff_monomial_mul_all (p : Polynomial A) (n k : ℕ) (r : A) :
    (monomial n r * p).coeff k = if n ≤ k then r * p.coeff (k-n) else 0 := by
  rw [← C_mul_X_pow_eq_monomial, mul_assoc, coeff_C_mul, coeff_X_pow_mul']
  split_ifs <;> simp

theorem coeff_comm_cached (p q : Polynomial A) (n : ℕ) :
    (comm p q).coeff n = ∑ i ∈ Finset.range (n+1), comm (p.coeff i) (q.coeff (n-i)) := by
  have h : (comm p q).coeff n =
      ∑ ij ∈ Finset.antidiagonal n, comm (p.coeff ij.1) (q.coeff ij.2) := by
    simp only [comm, coeff_sub, coeff_mul, Finset.sum_sub_distrib]
    congr 1
    exact Finset.Nat.sum_antidiagonal_swap.symm
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  exact h

theorem comm_add_left_cached (a b c : A) : comm (a+b) c = comm a c + comm b c := by
  unfold comm; noncomm_ring

theorem comm_add_right_cached (a b c : A) : comm a (b+c) = comm a b + comm a c := by
  unfold comm; noncomm_ring

theorem comm_smul_left_cached (r : ℝ) (a b : A) : comm (r • a) b = r • comm a b := by
  simp [comm, smul_mul_assoc, mul_smul_comm, smul_sub]

theorem comm_smul_right_cached (r : ℝ) (a b : A) : comm a (r • b) = r • comm a b := by
  simp [comm, smul_mul_assoc, mul_smul_comm, smul_sub]

theorem comm_zero_left_cached (a : A) : comm 0 a = 0 := by simp [comm]
theorem comm_zero_right_cached (a : A) : comm a 0 = 0 := by simp [comm]
theorem comm_self_cached (a : A) : comm a a = 0 := by simp [comm]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 500000 in
theorem cachedMidpoint8_coeff_0 (a b : A) :
    (fohMidpoint8 a b).coeff 0 = cachedMidpoint8Coeff a b 0 := by
  norm_num [fohMidpoint8, fohMidpoint6, coeff_monomial_mul_all, coeff_X_pow_mul', coeff_mul_X_pow'] <;>
    norm_num [fohMidpoint, cachedMidpoint8Coeff, coeff_comm_cached,
      Polynomial.coeff_monomial, Polynomial.coeff_one, Finset.sum_range_succ] <;>
    norm_num [comm_add_left_cached, comm_add_right_cached, comm_smul_left_cached,
      comm_smul_right_cached, comm_zero_left_cached, comm_zero_right_cached,
      comm_self_cached] <;> module
set_option maxRecDepth 4000 in
set_option maxHeartbeats 500000 in
theorem cachedMidpoint8_coeff_1 (a b : A) :
    (fohMidpoint8 a b).coeff 1 = cachedMidpoint8Coeff a b 1 := by
  norm_num [fohMidpoint8, fohMidpoint6, coeff_monomial_mul_all, coeff_X_pow_mul', coeff_mul_X_pow'] <;>
    norm_num [fohMidpoint, cachedMidpoint8Coeff, coeff_comm_cached,
      Polynomial.coeff_monomial, Polynomial.coeff_one, Finset.sum_range_succ] <;>
    norm_num [comm_add_left_cached, comm_add_right_cached, comm_smul_left_cached,
      comm_smul_right_cached, comm_zero_left_cached, comm_zero_right_cached,
      comm_self_cached] <;> module
set_option maxRecDepth 4000 in
set_option maxHeartbeats 500000 in
theorem cachedMidpoint8_coeff_2 (a b : A) :
    (fohMidpoint8 a b).coeff 2 = cachedMidpoint8Coeff a b 2 := by
  norm_num [fohMidpoint8, fohMidpoint6, coeff_monomial_mul_all, coeff_X_pow_mul', coeff_mul_X_pow'] <;>
    norm_num [fohMidpoint, cachedMidpoint8Coeff, coeff_comm_cached,
      Polynomial.coeff_monomial, Polynomial.coeff_one, Finset.sum_range_succ] <;>
    norm_num [comm_add_left_cached, comm_add_right_cached, comm_smul_left_cached,
      comm_smul_right_cached, comm_zero_left_cached, comm_zero_right_cached,
      comm_self_cached] <;> module
set_option maxRecDepth 4000 in
set_option maxHeartbeats 500000 in
theorem cachedMidpoint8_coeff_3 (a b : A) :
    (fohMidpoint8 a b).coeff 3 = cachedMidpoint8Coeff a b 3 := by
  norm_num [fohMidpoint8, fohMidpoint6, coeff_monomial_mul_all, coeff_X_pow_mul', coeff_mul_X_pow'] <;>
    norm_num [fohMidpoint, cachedMidpoint8Coeff, coeff_comm_cached,
      Polynomial.coeff_monomial, Polynomial.coeff_one, Finset.sum_range_succ] <;>
    norm_num [comm_add_left_cached, comm_add_right_cached, comm_smul_left_cached,
      comm_smul_right_cached, comm_zero_left_cached, comm_zero_right_cached,
      comm_self_cached] <;> module
set_option maxRecDepth 4000 in
set_option maxHeartbeats 500000 in
theorem cachedMidpoint8_coeff_4 (a b : A) :
    (fohMidpoint8 a b).coeff 4 = cachedMidpoint8Coeff a b 4 := by
  norm_num [fohMidpoint8, fohMidpoint6, coeff_monomial_mul_all, coeff_X_pow_mul', coeff_mul_X_pow'] <;>
    norm_num [fohMidpoint, cachedMidpoint8Coeff, coeff_comm_cached,
      Polynomial.coeff_monomial, Polynomial.coeff_one, Finset.sum_range_succ] <;>
    norm_num [comm_add_left_cached, comm_add_right_cached, comm_smul_left_cached,
      comm_smul_right_cached, comm_zero_left_cached, comm_zero_right_cached,
      comm_self_cached] <;> module
set_option maxRecDepth 4000 in
set_option maxHeartbeats 500000 in
theorem cachedMidpoint8_coeff_5 (a b : A) :
    (fohMidpoint8 a b).coeff 5 = cachedMidpoint8Coeff a b 5 := by
  norm_num [fohMidpoint8, fohMidpoint6, coeff_monomial_mul_all, coeff_X_pow_mul', coeff_mul_X_pow'] <;>
    norm_num [fohMidpoint, cachedMidpoint8Coeff, coeff_comm_cached,
      Polynomial.coeff_monomial, Polynomial.coeff_one, Finset.sum_range_succ] <;>
    norm_num [comm_add_left_cached, comm_add_right_cached, comm_smul_left_cached,
      comm_smul_right_cached, comm_zero_left_cached, comm_zero_right_cached,
      comm_self_cached] <;> module
set_option maxRecDepth 4000 in
set_option maxHeartbeats 500000 in
theorem cachedMidpoint8_coeff_6 (a b : A) :
    (fohMidpoint8 a b).coeff 6 = cachedMidpoint8Coeff a b 6 := by
  norm_num [fohMidpoint8, fohMidpoint6, coeff_monomial_mul_all, coeff_X_pow_mul', coeff_mul_X_pow'] <;>
    norm_num [fohMidpoint, cachedMidpoint8Coeff, coeff_comm_cached,
      Polynomial.coeff_monomial, Polynomial.coeff_one, Finset.sum_range_succ] <;>
    norm_num [comm_add_left_cached, comm_add_right_cached, comm_smul_left_cached,
      comm_smul_right_cached, comm_zero_left_cached, comm_zero_right_cached,
      comm_self_cached] <;> module
set_option maxRecDepth 4000 in
set_option maxHeartbeats 500000 in
theorem cachedMidpoint8_coeff_7 (a b : A) :
    (fohMidpoint8 a b).coeff 7 = cachedMidpoint8Coeff a b 7 := by
  norm_num [fohMidpoint8, fohMidpoint6, coeff_monomial_mul_all, coeff_X_pow_mul', coeff_mul_X_pow'] <;>
    norm_num [fohMidpoint, cachedMidpoint8Coeff, coeff_comm_cached,
      Polynomial.coeff_monomial, Polynomial.coeff_one, Finset.sum_range_succ] <;>
    norm_num [comm_add_left_cached, comm_add_right_cached, comm_smul_left_cached,
      comm_smul_right_cached, comm_zero_left_cached, comm_zero_right_cached,
      comm_self_cached] <;> module
set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
theorem cachedMidpoint8_coeff_8 (a b : A) :
    (fohMidpoint8 a b).coeff 8 = cachedMidpoint8Coeff a b 8 := by
  norm_num [fohMidpoint8, fohMidpoint6, coeff_monomial_mul_all, coeff_X_pow_mul', coeff_mul_X_pow'] <;>
    norm_num [fohMidpoint, cachedMidpoint8Coeff, coeff_comm_cached,
      Polynomial.coeff_monomial, Polynomial.coeff_one, Finset.sum_range_succ] <;>
    norm_num [comm_add_left_cached, comm_add_right_cached, comm_smul_left_cached,
      comm_smul_right_cached, comm_zero_left_cached, comm_zero_right_cached,
      comm_self_cached] <;> module
theorem cachedMidpoint8_coeff (a b : A) (n : ℕ) (hn : n ≤ 8) :
    (fohMidpoint8 a b).coeff n = cachedMidpoint8Coeff a b n := by
  interval_cases n
  · exact cachedMidpoint8_coeff_0 a b
  · exact cachedMidpoint8_coeff_1 a b
  · exact cachedMidpoint8_coeff_2 a b
  · exact cachedMidpoint8_coeff_3 a b
  · exact cachedMidpoint8_coeff_4 a b
  · exact cachedMidpoint8_coeff_5 a b
  · exact cachedMidpoint8_coeff_6 a b
  · exact cachedMidpoint8_coeff_7 a b
  · exact cachedMidpoint8_coeff_8 a b
set_option maxRecDepth 8000 in
set_option maxHeartbeats 5000000 in
theorem fohMidpoint8_flow_coeff (a b : A) (n : ℕ) (hn : n ≤ 8) :
    expCoeff (fohMidpoint8 a b) n = flowCoeff a b 0 n := by
  generalize he : fohMidpoint8 a b = p
  have hc (k : ℕ) (hk : k ≤ 8) : p.coeff k = cachedMidpoint8Coeff a b k :=
    by rw [← he]; exact cachedMidpoint8_coeff a b k hk
  have hp0 : p.coeff 0 = 0 := by simpa [cachedMidpoint8Coeff] using hc 0 (by omega)
  have hz (j k : ℕ) (hk : k < j) : (p^j).coeff k = 0 := coeff_pow_vanishes p hp0 j k hk
  have hpow (j k : ℕ) (_hjk : j+1 ≤ k) : (p^(j+1)).coeff k =
      ∑ i ∈ Finset.range (k+1), (p^j).coeff i * p.coeff (k-i) := by
    rw [pow_succ, Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  interval_cases n <;>
    norm_num [expCoeff, hpow, hz, hc, cachedMidpoint8Coeff, flowCoeff,
      Polynomial.coeff_one, Finset.sum_range_succ] <;> magnus_nc

theorem expCoeff_congr_coeff {p q : Polynomial A} {n : ℕ}
    (h : ∀ k, k ≤ n → p.coeff k = q.coeff k) : expCoeff p n = expCoeff q n := by
  have hh (m : ℕ) : ∀ k, k ≤ n → (p^m).coeff k = (q^m).coeff k := by
    induction m with
    | zero => intro k hk; simp
    | succ m ih =>
      intro k hk
      rw [pow_succ, pow_succ, coeff_mul, coeff_mul]
      apply Finset.sum_congr rfl
      intro ij hij
      have hs := Finset.mem_antidiagonal.mp hij
      rw [ih ij.1 (by omega), h ij.2 (by omega)]
  unfold expCoeff
  apply Finset.sum_congr rfl
  intro j hj
  rw [hh j n le_rfl]

theorem fohMidpoint8_eq_six_coeff (a b : A) (n : ℕ) (hn : n ≤ 6) :
    (fohMidpoint8 a b).coeff n = (fohMidpoint6 a b).coeff n := by
  simp [fohMidpoint8, coeff_monomial_mul_all, show ¬7 ≤ n by omega]

theorem fohMidpoint6_flow_coeff (a b : A) (n : ℕ) (hn : n ≤ 6) :
    expCoeff (fohMidpoint6 a b) n = flowCoeff a b 0 n := by
  calc
    _ = expCoeff (fohMidpoint8 a b) n := expCoeff_congr_coeff
      (fun k hk => (fohMidpoint8_eq_six_coeff a b k (by omega)).symm)
    _ = _ := fohMidpoint8_flow_coeff a b n (by omega)

end GNC.Magnus
