import GNC.Magnus.FohEndpointCertificate

/-! Repeated endpoint-error composition for a piecewise input.
The exact/approximate factors and local bounds are supplied; the proof
justifies every accumulated product of errors, not their numeric evaluation. -/
noncomputable section
namespace GNC.Magnus
variable {A : Type*} [NormedRing A]

def fohCertificateFold : List (A × A × ℝ) → A → A → ℝ → A × A × ℝ
  | [], X, P, e => (X, P, e)
  | (Y, Q, r) :: rest, X, P, e =>
    fohCertificateFold rest (X * Y) (P * Q) ((‖Q‖ + r) * e + r * ‖P‖)

/-- Every step of the implemented comparison-flow composition preserves a bound. -/
theorem fohCertificateFold_sound (steps : List (A × A × ℝ))
    (hs : ∀ s ∈ steps, 0 ≤ s.2.2 ∧ ‖s.1 - s.2.1‖ ≤ s.2.2)
    (X P : A) (e : ℝ) (he : 0 ≤ e) (hXP : ‖X - P‖ ≤ e) :
    let result := fohCertificateFold steps X P e
    0 ≤ result.2.2 ∧ ‖result.1 - result.2.1‖ ≤ result.2.2 := by
  induction steps generalizing X P e with
  | nil => exact ⟨he, hXP⟩
  | cons s rest ih =>
    rcases s with ⟨Y, Q, r⟩
    obtain ⟨hr, hYQ⟩ := hs (Y, Q, r) (by simp)
    apply ih (fun s h => hs s (by simp [h]))
    · positivity
    · calc
        ‖X * Y - P * Q‖ ≤
            (‖Q‖ + ‖Y - Q‖) * ‖X - P‖ + ‖Y - Q‖ * ‖P‖ :=
          foh_right_product_error X Y P Q
        _ ≤ (‖Q‖ + r) * e + r * ‖P‖ := by gcongr

end GNC.Magnus
