import GNC.Analysis.Coefficients
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! The elementary tangent upper bound in Remark 5. -/
noncomputable section
open Real Set
namespace GNC.Coefficients

def tangentGap (x : ℝ) : ℝ := 3*sin x-(sin x)^3-3*x*cos x

theorem tangentGap_derivative (x : ℝ) :
    HasDerivAt tangentGap (3*sin x*(x-sin x*cos x)) x := by
  convert (((hasDerivAt_sin x).const_mul 3).sub ((hasDerivAt_sin x).pow 3)).sub
    (((hasDerivAt_id x).const_mul 3).mul (hasDerivAt_cos x)) using 1
  simp only [id_eq]
  ring

theorem tangentGap_pos (x : ℝ) (hx : 0 < x) (hxπ : x < π) : 0 < tangentGap x := by
  have hm : StrictMonoOn tangentGap (Icc 0 π) :=
    strictMonoOn_of_deriv_pos (convex_Icc _ _)
      (fun y _ => (tangentGap_derivative y).continuousAt.continuousWithinAt) (by
        intro y hy
        rw [interior_Icc] at hy
        rw [(tangentGap_derivative y).deriv]
        have hs := sin_lt (show 0 < 2*y by linarith [hy.1])
        rw [sin_two_mul] at hs
        exact mul_pos (mul_pos (by norm_num) (sin_pos_of_pos_of_lt_pi hy.1 hy.2)) (by linarith))
  have h := hm (show 0 ∈ Icc (0:ℝ) π from ⟨le_rfl,pi_pos.le⟩) ⟨hx.le,hxπ.le⟩ hx
  simpa [tangentGap] using h

/-- In fact the stated non-strict bound is strict throughout (0,π). -/
theorem alpha_lt_tan_third (t : ℝ) (ht : 0 < t) (htπ : t < π) :
    alpha t < (1/3:ℝ)*tan (t/2) := by
  have hs : 0 < sin (t/2) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hc : 0 < cos (t/2) := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith⟩
  have hid : (1/3:ℝ)*tan (t/2)-alpha t = tangentGap (t/2)/(6*sin (t/2)^2*cos (t/2)) := by
    unfold alpha tangentGap
    rw [tan_eq_sin_div_cos]
    field_simp
    nlinarith [sin_sq_add_cos_sq (t/2),
      congrArg (fun z : ℝ => z*sin (t/2)) (sin_sq_add_cos_sq (t/2))]
  apply sub_pos.mp
  rw [hid]
  exact div_pos (tangentGap_pos _ (by linarith) (by linarith)) (by positivity)

theorem alpha_le_tan_third (t : ℝ) (ht : 0 < t) (htπ : t < π) :
    alpha t ≤ (1/3:ℝ)*tan (t/2) := (alpha_lt_tan_third t ht htπ).le

end GNC.Coefficients
