import GNC.Control.PolytopicTube
import Mathlib.Analysis.Calculus.MeanValue

/-! Mission tubes centered on a prescribed reference.

Unlike a comparison theorem that assumes the trajectory stays in a region,
the boundary theorem below prevents escape from the proposed tube. Its
certificate is needed only on the tube boundary. A separate static inclusion
then transfers the tube to operating and safety constraints. Existence of the
actual trajectory is explicit; no trajectory-validity hypothesis assumes the
desired tube conclusion.
-/
noncomputable section
open Set Real
namespace GNC.ReferenceTube
variable {E W : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def tube (P : E →L[ℝ] E) (reference : ℝ → E) (radiusSq : ℝ → ℝ)
    (t : ℝ) : Set E :=
  {x | PolytopicTube.storage P (x-reference t) ≤ radiusSq t}

/-- A strict inward derivative on a moving quadratic boundary precludes
first exit, using mathlib's continuous-time fencing theorem. -/
theorem boundary_invariance (P : E →L[ℝ] E)
    (hP : ∀ u v, inner ℝ u (P v) = inner ℝ v (P u))
    {x reference : ℝ → E} {dx dr : ℝ → E} {ρ dρ : ℝ → ℝ} {a b : ℝ}
    (hx : ∀ s ∈ Icc a b, HasDerivAt x (dx s) s)
    (hr : ∀ s ∈ Icc a b, HasDerivAt reference (dr s) s)
    (hρ : ∀ s, HasDerivAt ρ (dρ s) s)
    (hinit : x a ∈ tube P reference ρ a)
    (hinward : ∀ s ∈ Ico a b,
      PolytopicTube.storage P (x s-reference s) = ρ s →
      2*inner ℝ (x s-reference s) (P (dx s-dr s)) < dρ s) :
    ∀ t ∈ Icc a b, x t ∈ tube P reference ρ t := by
  have hder : ∀ s ∈ Icc a b,
      HasDerivAt (fun t => PolytopicTube.storage P (x t-reference t))
        (2*inner ℝ (x s-reference s) (P (dx s-dr s))) s := by
    intro s hs
    exact PolytopicTube.storage_derivative P hP ((hx s hs).sub (hr s hs))
  exact fun t ht => image_le_of_deriv_right_lt_deriv_boundary
    (fun s hs => (hder s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hder s ⟨hs.1,hs.2.le⟩).hasDerivWithinAt)
    hinit hρ hinward ht

/-- Regional differential supply gives a mission-wide tube, without
assuming the aircraft trajectory remains in the certificate region.
The static tube inclusion and a strictly positive reserve close that gap. -/
theorem certified_reference_tube (P : E →L[ℝ] E)
    (hP : ∀ u v, inner ℝ u (P v) = inner ℝ v (P u))
    (f : ℝ → E → W → E) (disturbances : ℝ → Set W)
    (region safe : ℝ → Set E)
    {x reference : ℝ → E} {w : ℝ → W} {dr : ℝ → E}
    {ρ dρ α β reserve : ℝ → ℝ} {a b : ℝ}
    (hx : ∀ s ∈ Icc a b, HasDerivAt x (f s (x s) (w s)) s)
    (hr : ∀ s ∈ Icc a b, HasDerivAt reference (dr s) s)
    (hρ : ∀ s, HasDerivAt ρ (dρ s) s)
    (hw : ∀ s ∈ Ico a b, w s ∈ disturbances s)
    (hinit : x a ∈ tube P reference ρ a)
    (hregion : ∀ s ∈ Icc a b, tube P reference ρ s ⊆ region s)
    (hsafe : ∀ s ∈ Icc a b, tube P reference ρ s ⊆ safe s)
    (hsupply : ∀ s ∈ Ico a b, ∀ y ∈ region s, ∀ d ∈ disturbances s,
      2*inner ℝ (y-reference s) (P (f s y d-dr s)) +
        α s*PolytopicTube.storage P (y-reference s) ≤ β s)
    (hreserve : ∀ s ∈ Ico a b, 0 < reserve s)
    (hradius : ∀ s ∈ Ico a b, β s+reserve s ≤ dρ s+α s*ρ s) :
    ∀ t ∈ Icc a b, x t ∈ tube P reference ρ t ∩ region t ∩ safe t := by
  have htube := boundary_invariance P hP hx hr hρ hinit (by
    intro s hs he
    have hc : x s ∈ tube P reference ρ s := he.le
    have h := hsupply s hs (x s) (hregion s ⟨hs.1,hs.2.le⟩ hc) (w s) (hw s hs)
    rw [he] at h
    have hh := hradius s hs
    have hp := hreserve s hs
    linarith)
  intro t ht
  exact ⟨⟨htube t ht,hregion t ht (htube t ht)⟩,hsafe t ht (htube t ht)⟩

/-- A reference need not solve the closed-loop equations exactly. Its
explicit differential defect adds to the disturbance supply budget. -/
theorem reference_defect_supply (P : E →L[ℝ] E) (e f nominal dr : E)
    {α β defectBudget : ℝ}
    (hf : 2*inner ℝ e (P (f-nominal))+α*PolytopicTube.storage P e ≤ β)
    (hd : 2*inner ℝ e (P (nominal-dr)) ≤ defectBudget) :
    2*inner ℝ e (P (f-dr))+α*PolytopicTube.storage P e ≤ β+defectBudget := by
  rw [show f-dr = (f-nominal)+(nominal-dr) by abel, map_add, inner_add_right]
  linarith

end GNC.ReferenceTube
