import GNC.Lie.CayleyChart
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.Algebra.LieGroup

/-! The smooth manifold of actual special orthogonal 3×3 matrices, using
left translates of the Cayley chart. -/
noncomputable section
open Matrix Set Function
open scoped Matrix Matrix.Norms.Operator ContDiff Manifold
namespace GNC.Cayley

instance so3TopologicalGroup : IsTopologicalGroup SO3 where
  continuous_mul := ((continuous_subtype_val.comp continuous_fst).mul
    (continuous_subtype_val.comp continuous_snd)).subtype_mk _
  continuous_inv := continuous_subtype_val.matrix_transpose.subtype_mk _

def translatedChart (R : SO3) : OpenPartialHomeomorph SO3 Vec3 :=
  (Homeomorph.mulLeft R⁻¹).toOpenPartialHomeomorph.trans chart

theorem translatedChart_apply (R S : SO3) : translatedChart R S = coordinates (R⁻¹*S) := rfl

theorem translatedChart_symm_apply (R : SO3) (q : Vec3) :
    (translatedChart R).symm q = R*rotation q := by
  simp [translatedChart, chart, Homeomorph.mulLeft_symm]

theorem translatedChart_source (R : SO3) :
    (translatedChart R).source = {S | R⁻¹*S ∈ domain} := by
  ext S; simp [translatedChart, chart]

theorem translatedChart_target (R : SO3) : (translatedChart R).target = univ := by
  ext q; simp [translatedChart, chart]

instance so3ChartedSpace : ChartedSpace Vec3 SO3 where
  atlas := range translatedChart
  chartAt := translatedChart
  mem_chart_source R := by rw [translatedChart_source]; simpa using one_mem_domain
  chart_mem_atlas R := mem_range_self R

instance so3IsManifold : IsManifold 𝓘(ℝ, Vec3) ∞ SO3 := by
  apply isManifold_of_contDiffOn
  rintro _ _ ⟨R, rfl⟩ ⟨S, rfl⟩
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    range_id, inter_univ, preimage_id_eq, id_comp, comp_id]
  intro q hq
  have hdom : S⁻¹*(R*rotation q) ∈ domain := by
    simpa [OpenPartialHomeomorph.trans_source, translatedChart_target,
      translatedChart_source, translatedChart_symm_apply] using hq
  have hc : ContDiff ℝ ∞ (fun q => (S⁻¹).val*(R.val*matrix q)) :=
    contDiff_const.mul (contDiff_const.mul contDiff_matrix)
  have hr := (contDiff_unskew.contDiffAt.comp _ (contDiffAt_ratio _ hdom)).comp q hc.contDiffAt
  convert hr.contDiffWithinAt using 1

theorem extChartAt_apply (R S : SO3) :
    extChartAt 𝓘(ℝ, Vec3) R S = coordinates (R⁻¹*S) := rfl

theorem extChartAt_symm_apply (R : SO3) (q : Vec3) :
    (extChartAt 𝓘(ℝ, Vec3) R).symm q = R*rotation q := translatedChart_symm_apply R q

/-- Smoothness into SO(3) follows from smoothness of the actual matrix entries. -/
theorem contMDiff_into_so3 {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners ℝ E H) (f : M → SO3)
    (hf : ContMDiff I 𝓘(ℝ, Mat3) ∞ (fun x => (f x).val)) :
    ContMDiff I 𝓘(ℝ, Vec3) ∞ f := by
  intro x
  rw [contMDiffAt_iff_target]
  refine ⟨(hf.continuous.subtype_mk _).continuousAt, ?_⟩
  have hA : ContMDiffAt I 𝓘(ℝ, Mat3) ∞ (fun y => (f x)⁻¹.val*(f y).val) x :=
    (contDiff_const.mul contDiff_id).contMDiff.contMDiffAt.comp x (hf x)
  have hunit : IsUnit ((f x)⁻¹.val*(f x).val+1).det := by
    change (f x)⁻¹*f x ∈ domain
    simpa using one_mem_domain
  have hC := contDiff_unskew.contDiffAt.comp _ (contDiffAt_ratio _ hunit)
  convert hC.contMDiffAt.comp x hA using 1

/-- The inclusion of the rotation manifold in matrices is smooth. -/
theorem contMDiff_so3_val : ContMDiff 𝓘(ℝ, Vec3) 𝓘(ℝ, Mat3) ∞ (fun R : SO3 => R.val) := by
  rw [contMDiff_iff]
  refine ⟨continuous_subtype_val, ?_⟩
  intro R A
  have h : ContDiff ℝ ∞ (fun q => R.val*matrix q) := contDiff_const.mul contDiff_matrix
  convert h.contDiffOn using 1

instance so3LieGroup : LieGroup 𝓘(ℝ, Vec3) ∞ SO3 where
  contMDiff_mul := by
    apply contMDiff_into_so3
    exact (contDiff_fst.mul contDiff_snd).contMDiff.comp
      ((contMDiff_so3_val.comp contMDiff_fst).prodMk_space (contMDiff_so3_val.comp contMDiff_snd))
  contMDiff_inv := by
    apply contMDiff_into_so3
    let L : Mat3 →ₗ[ℝ] Mat3 := Matrix.transposeLinearEquiv (Fin 3) (Fin 3) ℝ ℝ
    exact L.toContinuousLinearMap.contMDiff.comp contMDiff_so3_val

end GNC.Cayley
