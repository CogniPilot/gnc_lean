import GNC.Control.SharedBiasRobustness

/-! Feasible witnesses for independent-burn pointing programs, including
bounded coefficient and right-hand-side errors. These are upper/feasibility
certificates, complementary to the existing comparator cost lower bounds.
-/
noncomputable section
open Matrix Finset
namespace GNC.SharedBias
open ThrustSupport
variable {ι ρ : Type*} [Fintype ι]

/-- Per-burn squared support certificates suffice for every independently
chosen direction. Nonnegative burn magnitudes preserve the inequalities. -/
theorem independent_of_certificate (n : Vec3) (κ : ℝ) (h : ρ → ι → Vec3)
    (b : ρ → ℝ) (u : ι → ℝ) (ell s : ρ → ι → ℝ)
    (hu : ∀ j, 0 ≤ u j) (hell : ∀ i j, 0 ≤ ell i j) (hs : ∀ i j, 0 ≤ s i j)
    (hlength : ∀ i j, lengthSq (h i j+ell i j • n) ≤ (s i j)^2)
    (hbudget : ∀ i, (∑ j, u j*(s i j-ell i j*κ)) ≤ b i) :
    IndependentFeasible n κ h b u := by
  intro i q hq
  apply (sum_le_sum (fun j (_ : j ∈ (univ : Finset ι)) =>
    mul_le_mul_of_nonneg_left
      (cap_support_of_squared_bound n (h i j) (q j) κ (ell i j) (s i j)
        (hq j) (hell i j) (hs i j) (hlength i j)) (hu j))).trans
  exact hbudget i

/-- Feasibility survives terminal-data errors if the supplied witness pays
their row charges. Each independently chosen direction has unit norm. -/
theorem independent_feasible_of_errors (n : Vec3) (κ : ℝ)
    (h hh : ρ → ι → Vec3) (e : ρ → ι → ℝ) (b bh db : ρ → ℝ) (u : ι → ℝ)
    (he : ∀ i j, enorm (h i j-hh i j) ≤ e i j)
    (hb : ∀ i, |b i-bh i| ≤ db i) (hu : ∀ j, 0 ≤ u j)
    (htight : IndependentFeasible n κ hh (fun i => bh i-db i-∑ j, u j*e i j) u) :
    IndependentFeasible n κ h b u := by
  intro i q hq
  have hp (j : ι) : h i j ⬝ᵥ q j ≤ hh i j ⬝ᵥ q j+e i j := by
    have h := (abs_le.mp (pairing_error _ _ (q j) (he i j) (hq j).1)).2
    linarith
  have hs := sum_le_sum (fun j (_ : j ∈ (univ : Finset ι)) =>
    mul_le_mul_of_nonneg_left (hp j) (hu j))
  simp only [mul_add, sum_add_distrib] at hs
  have ht := htight i q hq
  linarith [(abs_le.mp (hb i)).1]

end GNC.SharedBias
