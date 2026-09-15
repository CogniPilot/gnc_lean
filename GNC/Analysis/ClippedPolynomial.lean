import GNC.Analysis.BoundedODE
import GNC.Analysis.PolynomialODE

/-! A bounded Lipschitz extension of a polynomial vector field from a cube.
Coordinate clipping is used only to construct a solution; a separate regional
certificate proves agreement with the original vector field along that solution.
-/
noncomputable section
set_option autoImplicit false
open Set Metric
open scoped NNReal
namespace GNC.PolynomialODE
variable {n : ℕ}

def clip (R : ℚ) (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  max (-(R:ℝ)) (min (R:ℝ) (x i))

theorem clip_bound {R : ℚ} (hR : 0 ≤ R) (x : Fin n → ℝ) (i : Fin n) :
    |clip R x i| ≤ (R:ℝ) := by
  have hRr : (0:ℝ) ≤ R := by exact_mod_cast hR
  exact abs_le.mpr ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

theorem clip_eq {R : ℚ} {x : Fin n → ℝ} (hx : ∀ i, |x i| ≤ (R:ℝ)) : clip R x = x := by
  funext i
  simp only [clip, min_eq_right (abs_le.mp (hx i)).2, max_eq_right (abs_le.mp (hx i)).1]

theorem clip_component_difference (R : ℚ) (x y : Fin n → ℝ) (i : Fin n) :
    |clip R x i-clip R y i| ≤ ‖x-y‖ := by
  have hl : LipschitzWith 1 (fun t : ℝ => max (-(R:ℝ)) (min (R:ℝ) t)) :=
    (LipschitzWith.id.const_min (R:ℝ)).const_max (-(R:ℝ))
  have hh := hl.dist_le_mul (x i) (y i)
  simp only [Real.dist_eq, NNReal.coe_one, one_mul] at hh
  exact hh.trans (by simpa [Real.norm_eq_abs] using norm_le_pi_norm (x-y) i)

theorem clip_lipschitz (R : ℚ) : LipschitzWith 1 (clip (n := n) R) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm, NNReal.coe_one, one_mul]
  exact (pi_norm_le_iff_of_nonneg (norm_nonneg (x-y))).mpr
    (clip_component_difference R x y)

theorem clip_norm {R : ℚ} (hR : 0 ≤ R) (x : Fin n → ℝ) : ‖clip R x‖ ≤ (R:ℝ) :=
  (pi_norm_le_iff_of_nonneg (by exact_mod_cast hR)).mpr (clip_bound hR x)

def clippedField (f : Fin n → Expr n) (R : ℚ) (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  (f i).value (clip R x)

theorem clippedField_eq (f : Fin n → Expr n) {R : ℚ} {x : Fin n → ℝ}
    (hx : ∀ i, |x i| ≤ (R:ℝ)) : clippedField f R x = fun i => (f i).value x := by
  unfold clippedField
  rw [clip_eq hx]

theorem clippedField_lipschitz (f : Fin n → Expr n) {R : ℚ} (hR : 0 ≤ R)
    (K : ℝ≥0) (hK : ∀ i, ((f i).slope R:ℝ) ≤ K) :
    LipschitzWith K (clippedField f R) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, dist_eq_norm]
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg K.2 (norm_nonneg _))).mpr
  intro i
  have h := (f i).difference_bound hR (clip R x) (clip R y) (norm_nonneg (x-y))
    (clip_bound hR x) (clip_bound hR y) (clip_component_difference R x y)
  exact h.trans (mul_le_mul_of_nonneg_right (hK i) (norm_nonneg (x-y)))

theorem clippedField_bound (f : Fin n → Expr n) {R : ℚ} (hR : 0 ≤ R)
    (L : ℝ≥0) (hL : ∀ i, ((f i).majorant R:ℝ) ≤ L) (x : Fin n → ℝ) :
    ‖clippedField f R x‖ ≤ L := by
  apply (pi_norm_le_iff_of_nonneg L.2).mpr
  intro i
  exact ((f i).value_bound hR _ (clip_bound hR x)).trans (hL i)

theorem clippedField_exists (f : Fin n → Expr n) {R : ℚ} (hR : 0 ≤ R)
    (K L : ℝ≥0) (hK : ∀ i, ((f i).slope R:ℝ) ≤ K)
    (hL : ∀ i, ((f i).majorant R:ℝ) ≤ L)
    (x₀ : Fin n → ℝ) {T : ℝ} (hT : 0 ≤ T) :
    ∃ x : ℝ → Fin n → ℝ, Continuous x ∧ x 0 = x₀ ∧
      ∀ t ∈ Icc 0 T, HasDerivAt x (clippedField f R (x t)) t :=
  BoundedODE.exists_solution _ K L (clippedField_lipschitz f hR K hK)
    (clippedField_bound f hR L hL) x₀ hT

end GNC.PolynomialODE
