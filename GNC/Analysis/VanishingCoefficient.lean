import GNC.Control.PolytopicResidualTube
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-! A quadratic residual has an exact state-dependent coefficient that
vanishes linearly at the origin. This is an existence construction, not
the recommended numerical realization or a global pairwise Lipschitz claim.
-/
noncomputable section
namespace GNC.VanishingCoefficient
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def coefficient (r : E → E) (x : E) : E →L[ℝ] E :=
  (‖x‖^2)⁻¹ • InnerProductSpace.rankOne ℝ (r x) x

@[simp] theorem coefficient_zero (r : E → E) : coefficient r 0 = 0 := by
  simp [coefficient]

theorem apply_self (r : E → E) (hzero : r 0 = 0) (x : E) :
    coefficient r x x = r x := by
  by_cases hx : x = 0
  · simp [hx, hzero]
  · have hn : ‖x‖^2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)
    simp [coefficient, InnerProductSpace.rankOne_apply,
      smul_smul, hn]

theorem norm_le (r : E → E) (x : E) {c : ℝ}
    (hr : ‖r x‖ ≤ c*‖x‖^2) : ‖coefficient r x‖ ≤ c*‖x‖ := by
  by_cases hx : x = 0
  · simp [hx]
  · have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
    rw [coefficient, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      InnerProductSpace.norm_rankOne]
    have h := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hr (norm_nonneg x))
      (show 0 ≤ (‖x‖^2)⁻¹ by positivity)
    calc
      (‖x‖^2)⁻¹ * (‖r x‖ * ‖x‖) ≤
          (‖x‖^2)⁻¹ * (c*‖x‖^2 * ‖x‖) := h
      _ = c*‖x‖ := by field_simp

/-- No differentiability of the residual is needed for this exact
coefficient representation and origin-relative norm bound. -/
theorem representation (A₀ : E →L[ℝ] E) (r : E → E) {c R : ℝ}
    (hR : 0 ≤ R) (hr : ∀ x, ‖x‖ ≤ R → ‖r x‖ ≤ c*‖x‖^2) :
    ∃ Δ : E → E →L[ℝ] E, Δ 0 = 0 ∧
      ∀ x, ‖x‖ ≤ R →
        (A₀ + Δ x) x = A₀ x + r x ∧ ‖Δ x‖ ≤ c*‖x‖ := by
  have hzero : r 0 = 0 := by
    have h := hr 0 (by simpa using hR)
    simpa using h
  refine ⟨coefficient r, coefficient_zero r, ?_⟩
  intro x hx
  exact ⟨by simp [apply_self r hzero x], norm_le r x (hr x hx)⟩

/-- The coefficient bound implies the quadratic residual used in the
regional polytopic theorem, in the same Euclidean norm. -/
theorem quadratic_residual (D : E →L[ℝ] E) (x : E) {c : ℝ}
    (hD : ‖D‖ ≤ c*‖x‖) : ‖D x‖ ≤ c*‖x‖^2 := by
  calc
    ‖D x‖ ≤ ‖D‖*‖x‖ := D.le_opNorm x
    _ ≤ (c*‖x‖)*‖x‖ := mul_le_mul_of_nonneg_right hD (norm_nonneg x)
    _ = c*‖x‖^2 := by ring

/-- Direct connection of the A0 + Delta A model to the storage supply
consumed by `PolytopicResidualTube.certificate`. -/
theorem storage_supply (P : E →L[ℝ] E) (D : E → E →L[ℝ] E)
    {m c R ρ : ℝ} (hm : 0 < m) (hc : 0 ≤ c) (hR : 0 ≤ R)
    (hcoerce : ∀ x, m*‖x‖^2 ≤ PolytopicTube.storage P x)
    (hregion : ρ ≤ m*R^2)
    (hD : ∀ x, ‖x‖ ≤ R → ‖D x‖ ≤ c*‖x‖) :
    ∀ x, PolytopicTube.storage P x ≤ ρ →
      2*inner ℝ x (P (D x x)) ≤
        (2*‖P‖*(c*R)/m)*PolytopicTube.storage P x := by
  exact PolytopicResidualTube.quadratic_supply P (fun x => D x x)
    hm hc hR hcoerce hregion
    (fun x hx => quadratic_residual (D x) x (hD x hx))

end GNC.VanishingCoefficient
