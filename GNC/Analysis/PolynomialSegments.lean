import GNC.Analysis.PolynomialBox

/-! Polynomial certificates with different vector fields on successive arcs.
Each local solution may be extended using its own field. Only its endpoint is
identified with the next arc's initial point; no two-sided derivative is
asserted at a switched-command edge.
-/
namespace GNC.PolynomialODE
variable {n : ℕ}

theorem box_segments_sound (S : ℕ → BoxStep n) (f : ℕ → Fin n → Expr n) (N : ℕ)
    (hvalid : ∀ j < N, (S j).Valid (f j))
    (hjoin : ∀ j, j+1 < N → (S j).Compatible (S (j+1)))
    (x : ℕ → ℝ → Fin n → ℝ) (hx : ∀ j < N, Continuous (x j))
    (hd : ∀ j < N, ∀ t ∈ Set.Icc (0:ℝ) (S j).duration,
      HasDerivAt (x j) (fun i => (f j i).value (x j t)) t)
    (hjx : ∀ j, j+1 < N → x (j+1) 0 = x j (S j).duration)
    (hi : ∀ i, |x 0 0 i-curve (S 0).coefficients 0 i| ≤ ((S 0).initialError i:ℝ)) :
    ∀ j < N, ∀ t ∈ Set.Icc (0:ℝ) (S j).duration, ∀ i,
      |x j t i-curve (S j).coefficients t i| < ((S j).error i:ℝ) := by
  intro j
  induction j with
  | zero =>
    intro hj
    exact box_step_sound (S 0) (f 0) (hvalid 0 hj) (x 0) (hx 0 hj) (hd 0 hj) hi
  | succ j ih =>
    intro hj
    have hj' : j < N := by omega
    have ht : (0:ℝ) ≤ (S j).duration := by exact_mod_cast (hvalid j hj').1
    have hp := ih hj' (S j).duration ⟨ht,le_rfl⟩
    have hi' := box_handoff (S j) (S (j+1)) (hjoin j hj) (x j (S j).duration)
      (fun i => (hp i).le)
    rw [← hjx j hj] at hi'
    exact box_step_sound (S (j+1)) (f (j+1)) (hvalid (j+1) hj)
      (x (j+1)) (hx (j+1) hj) (hd (j+1) hj) hi'

end GNC.PolynomialODE
