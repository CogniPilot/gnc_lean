import GNC.Analysis.ClippedPolynomial
import GNC.Analysis.EuclideanBox

/-! Coordinate clipping on Euclidean three-space. The rational norm
conversion is used only for bounded ODE extensions, not as a predictor's
error allowance. The map is the identity on the stated Euclidean ball. -/
noncomputable section
namespace GNC.EuclideanClip
abbrev E3 := EuclideanSpace ℝ (Fin 3)

def clip (R : ℚ) (x : E3) : E3 :=
  WithLp.toLp 2 (PolynomialODE.clip R (WithLp.ofLp x))

theorem norm_bound {R : ℚ} (hR : 0 ≤ R) (x : E3) :
    ‖clip R x‖ ≤ 2*(R:ℝ) := by
  exact (enorm_le_two_pi_norm _).trans
    (mul_le_mul_of_nonneg_left (PolynomialODE.clip_norm hR _) (by norm_num))

theorem difference (R : ℚ) (x y : E3) :
    ‖clip R x-clip R y‖ ≤ 2*‖x-y‖ := by
  have h := (PolynomialODE.clip_lipschitz (n := 3) R).dist_le_mul
    (WithLp.ofLp x) (WithLp.ofLp y)
  simp only [dist_eq_norm, NNReal.coe_one, one_mul] at h
  have hh := h.trans (pi_norm_le_enorm (WithLp.ofLp x-WithLp.ofLp y))
  exact (enorm_le_two_pi_norm _).trans
    (mul_le_mul_of_nonneg_left hh (by norm_num))

theorem lipschitz (R : ℚ) : LipschitzWith 2 (clip R) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [dist_eq_norm, NNReal.coe_ofNat] using difference R x y

theorem eq_self {R : ℚ} {x : E3} (hx : ‖x‖ ≤ (R:ℝ)) : clip R x = x := by
  have h := PolynomialODE.clip_eq (fun i => (component_le_enorm (WithLp.ofLp x) i).trans hx)
  exact congrArg (WithLp.toLp 2) h

theorem zero {R : ℚ} (hR : 0 ≤ R) : clip R (0:E3) = 0 := by
  apply eq_self
  simpa only [norm_zero] using (show (0:ℝ) ≤ R by exact_mod_cast hR)

end GNC.EuclideanClip
