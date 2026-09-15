import GNC.Analysis.PolynomialBallMap
import GNC.Applications.OrbitalComparison.PointingCapChart

/-! An exact square parameterization of the physical forward pointing cap.
The transverse map is cubic; the axial component retains its square root.
This lets box-based validated integrators use precisely the same physical
input family, without enlarging the cap to an independent transverse box. -/
noncomputable section
namespace GNC.OrbitalComparison.PointingCapBox
open PolynomialBallMap PointingCapBurn Set

def input (σ a b : ℝ) : Fin 3 → ℝ :=
  PointingCapChart.input (σ*diskX a b) (σ*diskX b a)

theorem admissible {σ a b : ℝ} (hσ : σ^2≤1) (ha : |a|≤1) (hb : |b|≤1) :
    Admissible σ (input σ a b) :=
  PointingCapChart.admissible hσ (scaled_disk_inside σ ha hb)

theorem surjective {σ : ℝ} (hσ : 0<σ) {x : Fin 3 → ℝ} (hx : Admissible σ x) :
    ∃ a b : ℝ, |a|≤1 ∧ |b|≤1 ∧ input σ a b=x := by
  obtain ⟨a,b,ha,hb,hu,hv⟩ := scaled_disk_surjective hσ hx.2.2.2
  refine ⟨a,b,ha,hb,?_⟩
  simp only [input,hu,hv]
  exact (PointingCapChart.input_eq hx).symm

/-- Every predicate on physical pointing parameters has the same universal
domain in the algebraic cap and in this square parameterization. -/
theorem forall_iff {σ : ℝ} (hσ : 0<σ) (hs : σ^2≤1) (P : (Fin 3 → ℝ) → Prop) :
    (∀ x, Admissible σ x → P x) ↔ (∀ a b, |a|≤1 → |b|≤1 → P (input σ a b)) := by
  constructor
  · intro h a b ha hb
    exact h _ (admissible hs ha hb)
  · intro h x hx
    obtain ⟨a,b,ha,hb,he⟩ := surjective hσ hx
    exact he ▸ h a b ha hb

/-- In particular, this reparameterization preserves the exact set of all
physical motions and therefore every time-indexed reachable position set. -/
theorem physical_family {σ : ℝ} (hσ : 0<σ) (hs : σ^2≤1) (α t : ℝ) :
    {p | ∃ x, Admissible σ x ∧ ∃ X : Motion α (direction x), X.p t=p} =
    {p | ∃ a b, |a|≤1 ∧ |b|≤1 ∧
      ∃ X : Motion α (direction (input σ a b)), X.p t=p} := by
  ext p
  constructor
  · rintro ⟨x,hx,X,hp⟩
    obtain ⟨a,b,ha,hb,he⟩ := surjective hσ hx
    subst x
    exact ⟨a,b,ha,hb,X,hp⟩
  · rintro ⟨a,b,ha,hb,X,hp⟩
    exact ⟨input σ a b,admissible hs ha hb,X,hp⟩

end GNC.OrbitalComparison.PointingCapBox
