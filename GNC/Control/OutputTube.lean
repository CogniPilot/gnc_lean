import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import GNC.Control.PolytopicTube

/-! Convex outer output sets from a quadratic/ellipsoidal state tube.
The physical reconstruction may be nonlinear. Its remainder is charged
explicitly; this never asserts that an exponential image is convex. -/
noncomputable section
open Set
namespace GNC.OutputTube
variable {E V ι : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

def halfspaces (rows : ι → V →L[ℝ] ℝ) (bounds : ι → ℝ) : Set V :=
  {y | ∀ i, rows i y ≤ bounds i}

theorem halfspaces_convex (rows : ι → V →L[ℝ] ℝ) (bounds : ι → ℝ) :
    Convex ℝ (halfspaces rows bounds) := by
  intro x hx y hy a b ha hb hab i
  change rows i (a • x+b • y) ≤ bounds i
  simp only [map_add, map_smul, smul_eq_mul]
  have h₁ := mul_le_mul_of_nonneg_left (hx i) ha
  have h₂ := mul_le_mul_of_nonneg_left (hy i) hb
  have hs := congrArg (fun z : ℝ => z*bounds i) hab
  nlinarith

/-- A factor S of the positive quadratic metric gives a directional output
bound retaining its anisotropy, instead of first replacing it by a ball. -/
theorem linear_bound (S : E ≃L[ℝ] E) (C : E →L[ℝ] ℝ) (x : E) {radius : ℝ}
    (hx : ‖S x‖ ≤ radius) : C x ≤ ‖C.comp S.symm.toContinuousLinearMap‖*radius := by
  have he : C x = (C.comp S.symm.toContinuousLinearMap) (S x) := by simp
  rw [he]
  exact (le_abs_self _).trans (((C.comp S.symm.toContinuousLinearMap).le_opNorm (S x)).trans
    (mul_le_mul_of_nonneg_left hx (norm_nonneg _)))

/-- A nonlinear output map is enclosed by a convex intersection of physical
halfspaces. The uniform remainder bound must be proved on the whole state
tube, including any log-chart or physical-force domain restrictions. -/
theorem nonlinear_image_enclosure (S : E ≃L[ℝ] E) (L : E →L[ℝ] V)
    (recover : E → V) (center : V) (rows : ι → V →L[ℝ] ℝ)
    (error : ι → ℝ) (radius : ℝ)
    (herror : ∀ x, ‖S x‖ ≤ radius → ∀ i,
      |rows i (recover x-center-L x)| ≤ error i) :
    recover '' {x | ‖S x‖ ≤ radius} ⊆
      halfspaces rows (fun i => rows i center+
        ‖(rows i).comp (L.comp S.symm.toContinuousLinearMap)‖*radius+error i) := by
  rintro y ⟨x, hx, rfl⟩ i
  have hb := linear_bound S ((rows i).comp L) x hx
  have hr := (abs_le.mp (herror x hx i)).2
  simp only [map_sub] at hr
  change rows i (recover x) ≤ _
  have hc : ((rows i).comp L).comp S.symm.toContinuousLinearMap =
      (rows i).comp (L.comp S.symm.toContinuousLinearMap) := rfl
  rw [hc] at hb
  change rows i (L x) ≤ _ at hb
  linarith

end GNC.OutputTube
