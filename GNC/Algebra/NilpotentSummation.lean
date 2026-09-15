import GNC.Lie.Euclidean
import Mathlib.Data.Matrix.Block

/-! The early finite-tail factorization in MixedNilPotent (May 1, 2025).
Keeping the index bound explicit prevents subtraction on natural numbers from
silently changing the power of Ω at the end of a summation range. -/
noncomputable section
open Matrix Finset
namespace GNC.Preintegration
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

def block (Ω : Matrix m m ℝ) (A : Matrix m n ℝ) (B : Matrix n n ℝ) :
    Matrix (m ⊕ n) (m ⊕ n) ℝ := fromBlocks Ω A 0 B

/-- Powers of the mixed block matrix, before using nilpotence. -/
theorem block_power_sum (Ω : Matrix m m ℝ) (A : Matrix m n ℝ)
    (B : Matrix n n ℝ) (k : ℕ) :
    block Ω A B ^ k = fromBlocks (Ω^k)
      (∑ i ∈ range k, Ω^(k-1-i)*A*B^i) 0 (B^k) := by
  induction k with
  | zero => simp [block, fromBlocks_one]
  | succ k ih =>
    rw [pow_succ', ih]
    simp only [block, fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero,
      zero_add, ← pow_succ', sum_range_succ, Nat.add_sub_cancel, Nat.sub_self,
      pow_zero, Matrix.one_mul]
    congr 1
    rw [Matrix.mul_sum]
    congr 1
    apply sum_congr rfl
    intro i hi
    have hi' := mem_range.mp hi
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← pow_succ',
      show k-1-i+1 = k-i by omega]

/-- The summation trick on page 2: the entire finite inner sum has a common
left factor. This works for every nilpotency cutoff l. -/
theorem factor_tail (Ω : Matrix m m ℝ) (A : Matrix m n ℝ) (B : Matrix n n ℝ)
    (l j : ℕ) :
    (∑ i ∈ range (l+1), Ω^(l+2+j-i)*A*B^i) =
      Ω^(j+1) * ∑ i ∈ range (l+1), Ω^(l+1-i)*A*B^i := by
  rw [Matrix.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' := mem_range.mp hi
  rw [show l+2+j-i = (j+1)+(l+1-i) by omega, pow_add]
  simp only [Matrix.mul_assoc]

/-- Reversing the finite index in the fixed tail factor. -/
theorem reverse_tail (Ω : Matrix m m ℝ) (A : Matrix m n ℝ) (B : Matrix n n ℝ)
    (l : ℕ) :
    (∑ i ∈ range (l+1), Ω^(l+1-i)*A*B^i) =
      ∑ i ∈ range (l+1), Ω^(i+1)*A*B^(l-i) := by
  rw [← Finset.sum_range_reflect (fun i => Ω^(l+1-i)*A*B^i) (l+1)]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' := mem_range.mp hi
  rw [show l+1-(l+1-1-i) = i+1 by omega,
    show l+1-1-i = l-i by omega]

/-- Nilpotence removes terms before any infinite-series rearrangement. -/
theorem truncate_nilpotent (Ω : Matrix m m ℝ) (A : Matrix m n ℝ)
    (B : Matrix n n ℝ) (l k : ℕ) (hB : B^(l+1) = 0) (hlk : l ≤ k) :
    (∑ i ∈ range (k+1), Ω^(k-i)*A*B^i) =
      ∑ i ∈ range (l+1), Ω^(k-i)*A*B^i := by
  symm
  apply Finset.sum_subset (range_mono (by omega))
  intro i hi hni
  have hi' : l+1 ≤ i := by simpa using hni
  have hz : B^i = 0 := by
    rw [show i = (l+1)+(i-(l+1)) by omega, pow_add, hB, zero_mul]
  rw [hz, Matrix.mul_zero]

/-- The entire tail has one fixed translation factor, exactly the early
summation trick in the note. -/
theorem block_power_tail (Ω : Matrix m m ℝ) (A : Matrix m n ℝ)
    (B : Matrix n n ℝ) (l j : ℕ) (hB : B^(l+1) = 0) :
    block Ω A B ^ (l+2+j) = fromBlocks (Ω^(l+2+j))
      (Ω^j * ∑ i ∈ range (l+1), Ω^(l+1-i)*A*B^i) 0 0 := by
  rw [block_power_sum]
  have hz : B^(l+2+j) = 0 := by
    rw [show l+2+j = (l+1)+(j+1) by omega, pow_add, hB, zero_mul]
  rw [hz]
  congr 1
  rw [show l+2+j = (l+1+j)+1 by omega]
  simp only [Nat.add_sub_cancel]
  rw [truncate_nilpotent Ω A B l (l+1+j) hB (by omega)]
  cases j with
  | zero => simp
  | succ j =>
    simpa only [show l+1+(j+1) = l+2+j by omega] using factor_tail Ω A B l j

/-- Cayley–Hamilton reduces the factored tail once, for every nilpotency
order. The square-zero case used in the published theorem is l = 1. -/
theorem block_minimal_relation (Ω : Matrix m m ℝ) (A : Matrix m n ℝ)
    (B : Matrix n n ℝ) (l : ℕ) (w : ℝ)
    (hΩ : Ω^3 = -(w^2) • Ω) (hB : B^(l+1) = 0) :
    block Ω A B ^ (l+4) = -(w^2) • block Ω A B ^ (l+2) := by
  rw [show l+4 = l+2+2 by omega, block_power_tail Ω A B l 2 hB,
    show l+2 = l+2+0 by omega, block_power_tail Ω A B l 0 hB]
  simp only [Nat.add_zero, Nat.reduceAdd, pow_one, fromBlocks_smul, smul_zero]
  have hp : Ω^(l+2+2) = -(w^2) • Ω^(l+2) := by
    rw [show l+2+2 = 3+(l+1) by omega, pow_add, hΩ, Matrix.smul_mul,
      ← pow_succ', show l+1+1 = l+2 by omega]
  rw [hp]
  congr 1
  simp only [pow_zero, Matrix.one_mul]
  rw [Matrix.mul_sum, Finset.smul_sum]
  apply sum_congr rfl
  intro i hi
  have hi' := mem_range.mp hi
  rw [show l+1-i = 1+(l-i) by omega, pow_add, pow_one]
  simp only [← Matrix.mul_assoc]
  rw [show Ω^2*Ω = Ω^3 by noncomm_ring, hΩ]
  simp only [Matrix.smul_mul]

end GNC.Preintegration
