import GNC.Magnus.FohDualDerivative
import GNC.Magnus.FohQuaternionSlope

/-!
# Finite quaternion certificate through degree fifteen

The invariant coordinates are scalar, midpoint vector, slope vector, and their
cross product. This module connects their exact multiplication and polynomial
coefficient recurrence to ordinary quaternion multiplication and differentiation.
No analytic logarithm or convergence assertion is used.
-/

noncomputable section
open Matrix Polynomial
open scoped Quaternion Matrix
namespace GNC.Magnus
namespace DegreeFifteen

abbrev Quad := Fin 4 → ℝ

def product (f g z : ℝ) (a b : Quad) : Quad := ![
  a 0*b 0-f*a 1*b 1-g*a 2*b 2-z*(a 1*b 2+a 2*b 1)-(f*g-z^2)*a 3*b 3,
  a 0*b 1+a 1*b 0+z*(a 1*b 3-a 3*b 1)+g*(a 2*b 3-a 3*b 2),
  a 0*b 2+a 2*b 0-f*(a 1*b 3-a 3*b 1)-z*(a 2*b 3-a 3*b 2),
  a 0*b 3+a 3*b 0+a 1*b 2-a 2*b 1]

def embed (m s : Vec3) : Quad →ₗ[ℝ] ℍ where
  toFun a := fohQ (a 0)
    (a 1*m 0+a 2*s 0+a 3*(m ⨯₃ s) 0)
    (a 1*m 1+a 2*s 1+a 3*(m ⨯₃ s) 1)
    (a 1*m 2+a 2*s 2+a 3*(m ⨯₃ s) 2)
  map_add' a b := by ext <;> simp [fohQ] <;> ring
  map_smul' r a := by ext <;> simp [fohQ] <;> ring

theorem embed_product (m s : Vec3) (a b : Quad) :
    embed m s (product (fohDot m m) (fohDot s s) (fohDot m s) a b) =
      embed m s a * embed m s b := by
  ext <;> simp [embed, product, fohQ, fohDot, cross_apply] <;> ring

def oneQuad : Quad := ![1, 0, 0, 0]
def firstQuad : Quad := ![0, 1, 0, 0]
def secondQuad : Quad := ![0, 0, 1, 0]

@[simp] theorem embed_one (m s : Vec3) : embed m s oneQuad = 1 := by
  ext <;> simp [embed, oneQuad, fohQ]

def poly (a : ℕ → Quad) (m s : Vec3) : Polynomial ℍ :=
  ∑ n ∈ Finset.range 16, monomial n (embed m s (a n))

theorem poly_coeff (a : ℕ → Quad) (m s : Vec3) (n : ℕ) :
    (poly a m s).coeff n = if n < 16 then embed m s (a n) else 0 := by
  classical
  simp [poly, Polynomial.coeff_monomial, Finset.sum_ite_eq']

theorem poly_coeff_of_support (a : ℕ → Quad) (m s : Vec3)
    (ha : ∀ n, 16 ≤ n → a n = 0) (n : ℕ) :
    (poly a m s).coeff n = embed m s (a n) := by
  rw [poly_coeff]
  split_ifs with h
  · rfl
  · rw [ha n (by omega), map_zero]

def convolution (f g z : ℝ) (a b : ℕ → Quad) (n : ℕ) : Quad :=
  ∑ j ∈ Finset.range (n+1), product f g z (a j) (b (n-j))

theorem poly_mul_coeff (a b : ℕ → Quad) (m s : Vec3) (n : ℕ) (hn : n < 16) :
    (poly a m s * poly b m s).coeff n =
      embed m s (convolution (fohDot m m) (fohDot s s) (fohDot m s) a b n) := by
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [convolution, map_sum, embed_product]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_range.mp hj
  rw [poly_coeff, poly_coeff, if_pos (by omega), if_pos (by omega)]

theorem power_coeff_from_certificate (m s : Vec3) (a : ℕ → Quad)
    (p : ℕ → ℕ → Quad)
    (h0 : ∀ n < 16, p 0 n = if n = 0 then oneQuad else 0)
    (hstep : ∀ k < 15, ∀ n < 16, p (k+1) n =
      convolution (fohDot m m) (fohDot s s) (fohDot m s) (p k) a n)
    (k : ℕ) (hk : k ≤ 15) (n : ℕ) (hn : n < 16) :
    ((poly a m s)^k).coeff n = embed m s (p k n) := by
  induction k generalizing n with
  | zero =>
    rw [h0 n hn]
    by_cases he : n = 0
    · simp [he]
    · simp [Polynomial.coeff_one, he]
  | succ k ih =>
    rw [pow_succ, Polynomial.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, hstep k (by omega) n hn]
    simp only [convolution, map_sum, embed_product]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_range.mp hj
    rw [ih (by omega) j (by omega), poly_coeff, if_pos (by omega)]

theorem embed_mul_nat (m s : Vec3) (a : Quad) (n : ℕ) :
    embed m s ((n:ℝ) • a) = embed m s a * (n:ℍ) := by
  ext <;> simp [embed, fohQ] <;> ring

theorem poly_derivative_from_certificate (m s : Vec3) (q a b : ℕ → Quad)
    (hq : ∀ n, 16 ≤ n → q n = 0)
    (ha : ∀ n, 16 ≤ n → a n = 0)
    (hb : ∀ n, 16 ≤ n → b n = 0)
    (hrec : ∀ j, ((j+1:ℕ):ℝ) • q (j+1) = (1/2:ℝ) •
      (product (fohDot m m) (fohDot s s) (fohDot m s) (a j) firstQuad +
       if j = 0 then 0 else
       product (fohDot m m) (fohDot s s) (fohDot m s) (b (j-1)) secondQuad)) :
    (poly q m s).derivative = (1/2:ℝ) •
      (poly a m s * C (embed m s firstQuad) +
       X * poly b m s * C (embed m s secondQuad)) := by
  apply Polynomial.ext
  intro j
  rw [coeff_derivative, poly_coeff_of_support q m s hq,
    show (j:ℍ)+1 = ((j+1:ℕ):ℍ) by simp, ← embed_mul_nat,
    hrec j]
  cases j with
  | zero => simp [map_smul, map_add, embed_product, coeff_mul_C,
      poly_coeff_of_support a m s ha]
  | succ j => simp [map_smul, map_add, embed_product, coeff_mul_C,
      coeff_X_mul, poly_coeff_of_support a m s ha, poly_coeff_of_support b m s hb]

theorem quaternion_mul_real (q : ℍ) (r : ℝ) : q*(r:ℍ) = r • q := by
  ext <;> simp <;> ring

theorem poly_eval_real (a : ℕ → Quad) (m s : Vec3) (r : ℝ) :
    (poly a m s).eval (r:ℍ) =
      embed m s (∑ j ∈ Finset.range 16, r^j • a j) := by
  simp only [poly, Polynomial.eval_finset_sum, Polynomial.eval_monomial,
    map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← Quaternion.coe_pow, quaternion_mul_real]

theorem polynomial_eq_of_derivative_eval (p q : Polynomial ℍ) (r : ℍ)
    (hd : p.derivative = q.derivative) (hv : p.eval r = q.eval r) : p = q := by
  letI : IsAddTorsionFree ℍ := IsAddTorsionFree.of_module_rat ℍ
  have hh : (p-q).derivative = 0 := by rw [map_sub, hd, sub_self]
  have hc := Polynomial.eq_C_of_derivative_eq_zero hh
  have hz : (p-q).eval r = 0 := by rw [Polynomial.eval_sub, hv, sub_self]
  rw [hc, Polynomial.eval_C] at hz
  apply sub_eq_zero.mp
  rw [hc, hz, Polynomial.C_0]

theorem centered_solution_unique (m s : Vec3) (Q P : ℕ → Polynomial ℍ)
    (h0 : Q 0 = P 0)
    (hb : ∀ n < 15, (Q (n+1)).eval (-1/2) = (P (n+1)).eval (-1/2))
    (hQ : ∀ n < 15, (Q (n+1)).derivative = (1/2:ℝ) •
      (Q n * C (embed m s firstQuad) +
       X * (if n = 0 then 0 else Q (n-1)) * C (embed m s secondQuad)))
    (hP : ∀ n < 15, (P (n+1)).derivative = (1/2:ℝ) •
      (P n * C (embed m s firstQuad) +
       X * (if n = 0 then 0 else P (n-1)) * C (embed m s secondQuad))) :
    ∀ n ≤ 15, Q n = P n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    cases n with
    | zero => exact h0
    | succ n =>
      apply polynomial_eq_of_derivative_eval _ _ (-1/2) _ (hb n (by omega))
      rw [hQ n (by omega), hP n (by omega), ih n (by omega) (by omega)]
      by_cases hn0 : n = 0
      · simp [hn0]
      · rw [if_neg hn0, if_neg hn0, ih (n-1) (by omega) (by omega)]

end DegreeFifteen
end GNC.Magnus
