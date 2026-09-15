import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Tactic

/-! Propagate local matrix-step error certificates through ordered products.
The actual implementation may also have an additive error at each matrix
multiplication. All bounds refer to computed quantities and certified local
step errors; no norm bound for an unknown exact prefix is assumed. -/
noncomputable section
namespace GNC.StepComposition
variable {A : Type*} [NormedRing A]

/-- `S` and `P` are the computed local step and prefix; `T` and `Q` are exact. -/
theorem one_step (S T P Q R : A) :
    ‖S*P+R-T*Q‖ ≤
      (‖S‖+‖S-T‖)*‖P-Q‖+‖S-T‖*‖P‖+‖R‖ := by
  have he : S*P+R-T*Q = T*(P-Q)+(S-T)*P+R := by noncomm_ring
  rw [he]
  have hT : ‖T‖ ≤ ‖S‖+‖S-T‖ := by
    calc
      ‖T‖ = ‖S-(S-T)‖ := by congr 1; abel
      _ ≤ ‖S‖+‖S-T‖ := norm_sub_le _ _
  exact (norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add
      ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hT (norm_nonneg _)))
      (norm_mul_le _ _))) le_rfl)

def budget (b δ p ρ : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | k+1 => (b k+δ k)*budget b δ p ρ k+δ k*p k+ρ k

/-- Local certificates and multiplication-error bounds imply a full product
certificate. The supplied `p` bounds only the already computed prefixes. -/
theorem finite_product_error
    (S T P Q R : ℕ → A) (b δ p ρ : ℕ → ℝ) (n : ℕ)
    (hinit : P 0 = Q 0)
    (hP : ∀ k < n, P (k+1) = S k*P k+R k)
    (hQ : ∀ k < n, Q (k+1) = T k*Q k)
    (hS : ∀ k < n, ‖S k‖ ≤ b k)
    (hδ : ∀ k < n, ‖S k-T k‖ ≤ δ k)
    (hp : ∀ k < n, ‖P k‖ ≤ p k)
    (hρ : ∀ k < n, ‖R k‖ ≤ ρ k) :
    ‖P n-Q n‖ ≤ budget b δ p ρ n := by
  have all : ∀ k, k ≤ n → ‖P k-Q k‖ ≤ budget b δ p ρ k := by
    intro k
    induction k with
    | zero => intro _; simp [hinit,budget]
    | succ k ih =>
      intro hk
      have hkn : k < n := by omega
      have hd : 0 ≤ δ k := (norm_nonneg _).trans (hδ k hkn)
      have hb : 0 ≤ b k := (norm_nonneg _).trans (hS k hkn)
      rw [hP k hkn,hQ k hkn,budget]
      exact (one_step (S k) (T k) (P k) (Q k) (R k)).trans
        (add_le_add
          (add_le_add
            (mul_le_mul (add_le_add (hS k hkn) (hδ k hkn))
              (ih (by omega)) (norm_nonneg _) (add_nonneg hb hd))
            (mul_le_mul (hδ k hkn) (hp k hkn) (norm_nonneg _) hd))
          (hρ k hkn))
  exact all n le_rfl

end GNC.StepComposition
