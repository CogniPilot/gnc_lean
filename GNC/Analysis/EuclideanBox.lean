import GNC.Lie.Euclidean

/-! Convert certified component errors to a Euclidean vector error using an
exact squared budget. No numerical square-root evaluation is needed. -/
noncomputable section
namespace GNC

theorem component_le_enorm (v : Vec3) (i : Fin 3) : |v i| ≤ enorm v := by
  simpa only [Real.norm_eq_abs] using
    (PiLp.norm_apply_le (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin 3)) i)

theorem pi_norm_le_enorm (v : Vec3) : ‖v‖ ≤ enorm v :=
  (pi_norm_le_iff_of_nonneg (enorm_nonneg v)).mpr (component_le_enorm v)

theorem enorm_le_of_component_bounds (v e : Vec3) {ε : ℝ}
    (he : ∀ k, |v k| ≤ e k) (hε : 0 ≤ ε)
    (hs : (∑ k, (e k)^2) ≤ ε^2) : enorm v ≤ ε := by
  have hsq (k : Fin 3) : (v k)^2 ≤ (e k)^2 := by
    obtain ⟨hl,hu⟩ := abs_le.mp (he k)
    have h := mul_nonneg (show 0 ≤ e k+v k by linarith)
      (show 0 ≤ e k-v k by linarith)
    nlinarith
  have hsum := (Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin 3))) => hsq k)).trans hs
  have hlen : lengthSq v ≤ ε^2 := by
    simpa [lengthSq, Fin.sum_univ_succ, add_assoc] using hsum
  rw [← enorm_sq] at hlen
  nlinarith [enorm_nonneg v]

/-- A rational norm conversion convenient for three-dimensional box bounds. -/
theorem enorm_le_two_pi_norm (v : Vec3) : enorm v ≤ 2*‖v‖ := by
  apply enorm_le_of_component_bounds v (fun _ => ‖v‖)
  · intro i
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm v i
  · positivity
  · norm_num [Fin.sum_univ_succ]
    nlinarith [sq_nonneg ‖v‖]

end GNC
