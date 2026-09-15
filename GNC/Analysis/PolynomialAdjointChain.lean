import GNC.Analysis.PolynomialAdjoint

/-! Initial, interface and terminal charges for a computed adjoint.
The candidate and adjoint may both jump at an interface. These discrepancies
are bounded explicitly; physical state continuity alone does not cancel them.
-/
namespace GNC.ParametricBox
open PolynomialODE Set
variable {C : Type} {n : ℕ} (A : Model C)

def initialPairCharge (ell : Fin n → C) (I : Fin n → ℚ) (a : ℚ) : ℚ :=
  ∑ i, A.bound (A.atTime (ell i) 0) 0 a * I i

def joinPairCharge (q ell nextQ nextEll : Fin n → C)
    (E : Fin n → ℚ) (h a : ℚ) : ℚ :=
  ∑ i, (A.bound (A.add (A.atTime (nextEll i) 0)
      (A.scale (-1) (A.atTime (ell i) h))) 0 a * E i +
    A.bound (A.multiply (A.atTime (nextEll i) 0)
      (A.add (A.atTime (q i) h) (A.scale (-1) (A.atTime (nextQ i) 0)))) 0 a)

def terminalPairCharge (ell : Fin n → C) (row E : Fin n → ℚ) (h a : ℚ) : ℚ :=
  ∑ i, A.bound (A.add (A.constant (row i))
    (A.scale (-1) (A.atTime (ell i) h))) 0 a * E i

noncomputable section

def pairing (q ell : Fin n → C) (θ t : ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i, A.value (ell i) t θ * (x i-A.value (q i) t θ)

theorem polynomial_pair_bound (ell : Fin n → C) {E : Fin n → ℚ}
    {h a : ℚ} {t θ : ℝ} (ht : |t| ≤ (h : ℝ)) (hθ : |θ| ≤ (a : ℝ))
    (v : Fin n → ℝ) (hv : ∀ i, |v i| ≤ (E i : ℝ)) :
    |∑ i, A.value (ell i) t θ*v i| ≤
      ((∑ i, A.bound (ell i) h a*E i : ℚ) : ℝ) := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  push_cast
  apply Finset.sum_le_sum
  intro i _
  rw [abs_mul]
  have hb := A.bound_sound (ell i) ht hθ
  exact mul_le_mul hb (hv i) (abs_nonneg _) ((abs_nonneg _).trans hb)

theorem initial_pair_bound (q ell : Fin n → C) {I : Fin n → ℚ} {a : ℚ}
    {θ : ℝ} (hθ : |θ| ≤ (a : ℝ)) (x : Fin n → ℝ)
    (hx : ∀ i, |x i-A.value (q i) 0 θ| ≤ (I i : ℝ)) :
    |pairing A q ell θ 0 x| ≤ (initialPairCharge A ell I a : ℝ) := by
  simpa only [pairing, initialPairCharge, A.value_atTime, Rat.cast_zero] using
    polynomial_pair_bound A (fun i => A.atTime (ell i) 0)
      (t := 0) (h := 0) (by norm_num) hθ (fun i => x i-A.value (q i) 0 θ) hx

theorem join_pair_bound (q ell nextQ nextEll : Fin n → C)
    {E : Fin n → ℚ} {h a : ℚ} {θ : ℝ} (hθ : |θ| ≤ (a : ℝ))
    (x : Fin n → ℝ) (hx : ∀ i, |x i-A.value (q i) h θ| ≤ (E i : ℝ)) :
    |pairing A nextQ nextEll θ 0 x-pairing A q ell θ h x| ≤
      (joinPairCharge A q ell nextQ nextEll E h a : ℝ) := by
  have he : pairing A nextQ nextEll θ 0 x-pairing A q ell θ h x =
      ∑ i, ((A.value (nextEll i) 0 θ-A.value (ell i) h θ)*(x i-A.value (q i) h θ)+
        A.value (nextEll i) 0 θ*(A.value (q i) h θ-A.value (nextQ i) 0 θ)) := by
    simp only [pairing, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  simp only [joinPairCharge, Rat.cast_sum, Rat.cast_add, Rat.cast_mul]
  apply Finset.sum_le_sum
  intro i _
  have hb := A.bound_sound (A.add (A.atTime (nextEll i) 0)
    (A.scale (-1) (A.atTime (ell i) h))) (h := 0) (t := 0) (by norm_num) hθ
  have hc := A.bound_sound (A.multiply (A.atTime (nextEll i) 0)
    (A.add (A.atTime (q i) h) (A.scale (-1) (A.atTime (nextQ i) 0))))
    (h := 0) (t := 0) (by norm_num) hθ
  simp only [A.value_add, A.value_scale, A.value_multiply, A.value_atTime,
    Rat.cast_neg, Rat.cast_one, Rat.cast_zero, neg_one_mul, ← sub_eq_add_neg] at hb hc
  apply (abs_add_le _ _).trans (add_le_add ?_ hc)
  rw [abs_mul]
  exact mul_le_mul hb (hx i) (abs_nonneg _) ((abs_nonneg _).trans hb)

theorem terminal_pair_bound (q ell : Fin n → C) (row : Fin n → ℚ)
    {E : Fin n → ℚ} {h a : ℚ} {θ : ℝ} (hθ : |θ| ≤ (a : ℝ))
    (x : Fin n → ℝ) (hx : ∀ i, |x i-A.value (q i) h θ| ≤ (E i : ℝ)) :
    |(∑ i, (row i : ℝ)*(x i-A.value (q i) h θ))-pairing A q ell θ h x| ≤
      (terminalPairCharge A ell row E h a : ℝ) := by
  have hb := polynomial_pair_bound A
    (fun i => A.add (A.constant (row i)) (A.scale (-1) (A.atTime (ell i) h)))
    (h := 0) (t := 0) (by norm_num) hθ (fun i => x i-A.value (q i) h θ) hx
  simpa only [A.value_add, A.value_constant, A.value_scale, A.value_atTime,
    Rat.cast_neg, Rat.cast_one, neg_one_mul, ← sub_eq_add_neg, sub_mul,
    Finset.sum_sub_distrib, pairing, terminalPairCharge] using hb

/-- Scalar telescoping with explicit jumps. No exact adjoint, exact candidate
handoff, or cancellation of rounded coefficients is assumed. -/
theorem finite_pair_chain (start finish arc jump : ℕ → ℝ) (initial : ℝ)
    (N : ℕ) (h0 : |start 0| ≤ initial)
    (ha : ∀ j < N, |finish j-start j| ≤ arc j)
    (hj : ∀ j, j+1 < N → |start (j+1)-finish j| ≤ jump j) :
    ∀ j < N, |finish j| ≤ initial+∑ k ∈ Finset.range (j+1), arc k +
      ∑ k ∈ Finset.range j, jump k := by
  intro j
  induction j with
  | zero =>
    intro h
    have hb := (abs_add_le (finish 0-start 0) (start 0)).trans
      (add_le_add (ha 0 h) h0)
    simp only [sub_add_cancel] at hb
    simpa [add_comm] using hb
  | succ j ih =>
    intro h
    have he : finish (j+1) = (finish (j+1)-start (j+1))+
        (start (j+1)-finish j)+finish j := by ring
    calc
      |finish (j+1)| = |(finish (j+1)-start (j+1))+
          (start (j+1)-finish j)+finish j| := congrArg abs he
      _ ≤ (|finish (j+1)-start (j+1)|+|start (j+1)-finish j|)+|finish j| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ (arc (j+1)+jump j)+(initial+∑ k ∈ Finset.range (j+1), arc k+
          ∑ k ∈ Finset.range j, jump k) :=
        add_le_add (add_le_add (ha (j+1) h) (hj j h)) (ih (by omega))
      _ = _ := by simp only [Finset.sum_range_succ]; ring

end
end GNC.ParametricBox
