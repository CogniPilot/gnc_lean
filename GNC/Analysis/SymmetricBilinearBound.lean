import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Tactic

/-! A diagonal quadratic bound controls a symmetric bilinear map on a real
inner-product space with the same constant. Polarization and normalization
avoid the factor lost by applying the triangle inequality to each formula
term. The output may be any real normed vector space.
-/
noncomputable section
open scoped RealInnerProductSpace
namespace GNC.SymmetricBilinearBound
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem polarization (B : E →ₗ[ℝ] E →ₗ[ℝ] F)
    (hs : ∀ u v, B u v = B v u) (u v : E) :
    (4:ℝ) • B u v = B (u+v) (u+v)-B (u-v) (u-v) := by
  simp only [map_add,map_sub,LinearMap.add_apply,LinearMap.sub_apply]
  rw [hs v u]
  module

theorem unit_bound (B : E →ₗ[ℝ] E →ₗ[ℝ] F)
    (hs : ∀ u v, B u v = B v u) {C : ℝ}
    (hb : ∀ u, ‖B u u‖ ≤ C*‖u‖^2) (u v : E)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) : ‖B u v‖ ≤ C := by
  have h := norm_sub_le (B (u+v) (u+v)) (B (u-v) (u-v))
  rw [← polarization B hs u v,norm_smul] at h
  have hp := parallelogram_law_with_norm ℝ u v
  rw [hu,hv] at hp
  norm_num only [Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ) < 4)] at h
  norm_num at hp
  have hc := congrArg (fun x : ℝ => C*x) hp
  nlinarith [hb (u+v),hb (u-v)]

theorem bound (B : E →ₗ[ℝ] E →ₗ[ℝ] F)
    (hs : ∀ u v, B u v = B v u) {C : ℝ}
    (hb : ∀ u, ‖B u u‖ ≤ C*‖u‖^2) (u v : E) :
    ‖B u v‖ ≤ C*‖u‖*‖v‖ := by
  by_cases hu : u = 0
  · simp [hu]
  by_cases hv : v = 0
  · simp [hv]
  have hnu : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hnv : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hu' : ‖(‖u‖⁻¹:ℝ) • u‖ = 1 := by simp [norm_smul,hnu.ne']
  have hv' : ‖(‖v‖⁻¹:ℝ) • v‖ = 1 := by simp [norm_smul,hnv.ne']
  have h := unit_bound B hs hb _ _ hu' hv'
  have he : B u v = (‖u‖*‖v‖) • B (‖u‖⁻¹ • u) (‖v‖⁻¹ • v) := by
    simp only [map_smul,LinearMap.smul_apply,smul_smul]
    have hprod : ‖u‖*‖v‖*(‖v‖⁻¹*‖u‖⁻¹) = (1:ℝ) := by
      field_simp
    rw [hprod,one_smul]
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos (mul_pos hnu hnv)]
  exact (mul_le_mul_of_nonneg_left h (mul_nonneg hnu.le hnv.le)).trans_eq (by ring)

end GNC.SymmetricBilinearBound
