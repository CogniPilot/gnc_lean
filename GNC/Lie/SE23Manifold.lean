import GNC.Lie.SO3Manifold

/-! Smooth charts and Lie-group operations for the actual SE₂(3) group.
The topology is the product of the matrix-subspace topology on SO(3) and
the two translation spaces. -/
noncomputable section
open Matrix Set Function
open scoped Matrix Matrix.Norms.Operator ContDiff Manifold
namespace GNC.SE23

abbrev Model := Vec3 × Vec3 × Vec3

def productEquiv : SE23 ≃ SO3 × Vec3 × Vec3 where
  toFun X := (X.rot,X.vel,X.pos)
  invFun x := ⟨x.1,x.2.1,x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance topologicalSpace : TopologicalSpace SE23 := TopologicalSpace.induced productEquiv inferInstance

def productHomeomorph : SE23 ≃ₜ SO3 × Vec3 × Vec3 where
  toEquiv := productEquiv
  continuous_toFun := continuous_induced_dom
  continuous_invFun := continuous_induced_rng.mpr continuous_id

theorem continuous_rot : Continuous SE23.rot := productHomeomorph.continuous.fst
theorem continuous_vel : Continuous SE23.vel := productHomeomorph.continuous.snd.fst
theorem continuous_pos : Continuous SE23.pos := productHomeomorph.continuous.snd.snd

def chart (R : SO3) : OpenPartialHomeomorph SE23 Model :=
  productHomeomorph.toOpenPartialHomeomorph.trans
    ((Cayley.translatedChart R).prod (OpenPartialHomeomorph.refl (Vec3 × Vec3)))

theorem chart_apply (R : SO3) (X : SE23) : chart R X = (Cayley.coordinates (R⁻¹*X.rot),X.vel,X.pos) := rfl

theorem chart_symm_apply (R : SO3) (x : Model) :
    (chart R).symm x = ⟨R*Cayley.rotation x.1,x.2.1,x.2.2⟩ := by
  simp [chart, Cayley.translatedChart_symm_apply, productHomeomorph, productEquiv]

theorem chart_source (R : SO3) : (chart R).source = {X | R⁻¹*X.rot ∈ Cayley.domain} := by
  ext X; simp [chart, Cayley.translatedChart_source, productHomeomorph, productEquiv]

theorem chart_target (R : SO3) : (chart R).target = univ := by
  ext x; simp [chart, Cayley.translatedChart_target]

instance chartedSpace : ChartedSpace Model SE23 where
  atlas := range chart
  chartAt X := chart X.rot
  mem_chart_source X := by rw [chart_source]; simpa using Cayley.one_mem_domain
  chart_mem_atlas X := mem_range_self X.rot

instance isManifold : IsManifold 𝓘(ℝ, Model) ∞ SE23 := by
  apply isManifold_of_contDiffOn
  rintro _ _ ⟨R,rfl⟩ ⟨S,rfl⟩
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    range_id, inter_univ, preimage_id_eq, id_comp, comp_id]
  intro x hx
  have hdom : S⁻¹*(R*Cayley.rotation x.1) ∈ Cayley.domain := by
    simpa [OpenPartialHomeomorph.trans_source, chart_target, chart_source, chart_symm_apply] using hx
  have hc : ContDiff ℝ ∞ (fun x : Model => (S⁻¹).val*(R.val*Cayley.matrix x.1)) :=
    contDiff_const.mul (contDiff_const.mul (Cayley.contDiff_matrix.comp contDiff_fst))
  have hr := (Cayley.contDiff_unskew.contDiffAt.comp _ (Cayley.contDiffAt_ratio _ hdom)).comp x hc.contDiffAt
  convert (hr.prodMk contDiffAt_snd).contDiffWithinAt using 1

theorem extChartAt_apply (X Y : SE23) :
    extChartAt 𝓘(ℝ, Model) X Y = (Cayley.coordinates (X.rot⁻¹*Y.rot),Y.vel,Y.pos) := rfl

theorem extChartAt_symm_apply (X : SE23) (x : Model) :
    (extChartAt 𝓘(ℝ, Model) X).symm x = ⟨X.rot*Cayley.rotation x.1,x.2.1,x.2.2⟩ :=
  chart_symm_apply X.rot x

theorem contMDiff_rot : ContMDiff 𝓘(ℝ, Model) 𝓘(ℝ, Vec3) ∞ SE23.rot := by
  apply Cayley.contMDiff_into_so3
  rw [contMDiff_iff]
  refine ⟨continuous_subtype_val.comp continuous_rot, ?_⟩
  intro X A
  have h : ContDiff ℝ ∞ (fun x : Model => X.rot.val*Cayley.matrix x.1) :=
    contDiff_const.mul (Cayley.contDiff_matrix.comp contDiff_fst)
  convert h.contDiffOn using 1

theorem contMDiff_vel : ContMDiff 𝓘(ℝ, Model) 𝓘(ℝ, Vec3) ∞ SE23.vel := by
  rw [contMDiff_iff]
  refine ⟨continuous_vel, ?_⟩
  intro X v
  have h : ContDiff ℝ ∞ (fun x : Model => x.2.1) := contDiff_fst.comp contDiff_snd
  convert h.contDiffOn using 1

theorem contMDiff_pos : ContMDiff 𝓘(ℝ, Model) 𝓘(ℝ, Vec3) ∞ SE23.pos := by
  rw [contMDiff_iff]
  refine ⟨continuous_pos, ?_⟩
  intro X p
  have h : ContDiff ℝ ∞ (fun x : Model => x.2.2) := contDiff_snd.comp contDiff_snd
  convert h.contDiffOn using 1

theorem contMDiff_mk {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners ℝ E H) (R : M → SO3) (v p : M → Vec3)
    (hR : ContMDiff I 𝓘(ℝ, Vec3) ∞ R) (hv : ContMDiff I 𝓘(ℝ, Vec3) ∞ v)
    (hp : ContMDiff I 𝓘(ℝ, Vec3) ∞ p) :
    ContMDiff I 𝓘(ℝ, Model) ∞ (fun x => (⟨R x,v x,p x⟩ : SE23)) := by
  intro x
  rw [contMDiffAt_iff_target]
  refine ⟨?_, ?_⟩
  · exact (productHomeomorph.symm.continuous.comp
      (hR.continuous.prodMk (hv.continuous.prodMk hp.continuous))).continuousAt
  · have hc := (contMDiffAt_iff_target.mp (hR x)).2
    convert hc.prodMk_space ((hv x).prodMk_space (hp x)) using 1

/-- The ordinary matrix-vector action, as a continuous bilinear operation. -/
def matrixAction : Cayley.Mat3 →L[ℝ] (Vec3 →L[ℝ] Vec3) :=
  ((LinearMap.toContinuousLinearMap : (Vec3 →ₗ[ℝ] Vec3) ≃ₗ[ℝ] (Vec3 →L[ℝ] Vec3)).toLinearMap.comp
    (Matrix.mulVecBilin ℝ ℝ)).toContinuousLinearMap

theorem contMDiff_rotate {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners ℝ E H) (R : M → SO3) (v : M → Vec3)
    (hR : ContMDiff I 𝓘(ℝ, Vec3) ∞ R) (hv : ContMDiff I 𝓘(ℝ, Vec3) ∞ v) :
    ContMDiff I 𝓘(ℝ, Vec3) ∞ (fun x => rotate (R x) (v x)) :=
  (matrixAction.contMDiff.comp (Cayley.contMDiff_so3_val.comp hR)).clm_apply hv

instance lieGroup : LieGroup 𝓘(ℝ, Model) ∞ SE23 where
  contMDiff_mul := by
    apply contMDiff_mk
    · exact (contMDiff_rot.comp contMDiff_fst).mul (contMDiff_rot.comp contMDiff_snd)
    · exact (contMDiff_vel.comp contMDiff_fst).add
        (contMDiff_rotate _ _ _ (contMDiff_rot.comp contMDiff_fst) (contMDiff_vel.comp contMDiff_snd))
    · exact (contMDiff_pos.comp contMDiff_fst).add
        (contMDiff_rotate _ _ _ (contMDiff_rot.comp contMDiff_fst) (contMDiff_pos.comp contMDiff_snd))
  contMDiff_inv := by
    apply contMDiff_mk
    · exact contMDiff_rot.inv
    · exact (contMDiff_rotate _ _ _ contMDiff_rot.inv contMDiff_vel).neg
    · exact (contMDiff_rotate _ _ _ contMDiff_rot.inv contMDiff_pos).neg

instance isTopologicalGroup : IsTopologicalGroup SE23 := topologicalGroup_of_lieGroup 𝓘(ℝ, Model) ∞

end GNC.SE23
