import GNC.Lie.LocalLog
import Mathlib.Geometry.Manifold.GroupLieAlgebra

/-! Identification of the manifold tangent Lie algebra with the paper's
matrix Lie algebra. Mathlib supplies the manifold bracket and Lie algebra
instances; the work here relates the faithful representation to that bracket. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix NormedSpace Filter Set Function VectorField
open scoped Matrix Matrix.Norms.Operator ContDiff Manifold Topology
namespace GNC.TangentLieAlgebra

/-- Differentiating the two intertwining identities and cancelling the
symmetric second derivative gives the commutator in the representation. -/
theorem bracket_representation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → Mat5) (V W : E → E) (A B : Mat5) (x : E)
    (hf : ContDiff ℝ ∞ f) (hV : DifferentiableAt ℝ V x) (hW : DifferentiableAt ℝ W x)
    (hv : ∀ y, fderiv ℝ f y (V y) = f y*A)
    (hw : ∀ y, fderiv ℝ f y (W y) = f y*B) :
    fderiv ℝ f x (lieBracket ℝ V W x) = f x*(A*B-B*A) := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by decide)).differentiable one_ne_zero x
  have hfd := hf.differentiable (by simp) x
  have h₁ := congrArg (fun g : E → Mat5 => fderiv ℝ g x (V x)) (funext hw)
  have h₂ := congrArg (fun g : E → Mat5 => fderiv ℝ g x (W x)) (funext hv)
  dsimp only at h₁ h₂
  rw [fderiv_clm_apply hd hW, fderiv_mul_const' hfd] at h₁
  rw [fderiv_clm_apply hd hV, fderiv_mul_const' hfd] at h₂
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.smul_apply,
    MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op] at h₁ h₂
  have hs := (hf.contDiffAt (x := x)).isSymmSndFDerivAt
    (by rw [minSmoothness_of_isRCLikeNormedField]; decide) (V x) (W x)
  simp only [lieBracket, map_sub]
  rw [hv] at h₁
  rw [hw] at h₂
  linear_combination (norm := noncomm_ring) h₁-h₂-hs

abbrev I := 𝓘(ℝ, SE23.Model)
abbrev Algebra := GroupLieAlgebra I SE23

instance lieGroup_three : LieGroup I (minSmoothness ℝ 3) SE23 := by
  rw [minSmoothness_of_isRCLikeNormedField]
  exact LieGroup.of_le (n := ∞) (by decide)

theorem toMatrix_contMDiff : ContMDiff I 𝓘(ℝ, Mat5) ∞ SE23.toMatrix := by
  have hr := Cayley.contMDiff_so3_val.comp SE23.contMDiff_rot
  have h := (matrixAssembly.toContinuousLinearMap.contMDiff.comp
    (hr.prodMk_space (SE23.contMDiff_vel.prodMk_space SE23.contMDiff_pos))).add
    (contMDiff_const (c := affineBottom))
  convert h using 1
  funext x
  exact (matrixAssembly_toMatrix x).symm

def matrixTangent (g : SE23) : SE23.Model →L[ℝ] Mat5 :=
  mfderiv I 𝓘(ℝ, Mat5) SE23.toMatrix g

theorem invariant_image (g : SE23) (v : Algebra) :
    matrixTangent g (mulInvariantVectorField v g) = SE23.toMatrix g*matrixTangent 1 v := by
  let L := ContinuousLinearMap.mul ℝ Mat5 (SE23.toMatrix g)
  have he : SE23.toMatrix ∘ (g*·) = L ∘ SE23.toMatrix := by
    funext h; exact SE23.toMatrix_mul g h
  have ht := toMatrix_contMDiff.mdifferentiable (by simp)
  have hg : MDifferentiable I I (g*·) :=
    (contMDiff_mul_left (I := I) (n := ∞) (a := g)).mdifferentiable (by simp)
  have hd := congrArg (fun f : SE23 → Mat5 => mfderiv I 𝓘(ℝ, Mat5) f 1 v) he
  dsimp only at hd
  rw [mfderiv_comp _ (ht _) (hg _), mfderiv_comp _ L.differentiableAt.mdifferentiableAt (ht _)] at hd
  rw [mfderiv_eq_fderiv, L.fderiv] at hd
  change matrixTangent (g*1) (mulInvariantVectorField v g) =
    SE23.toMatrix g*matrixTangent 1 v at hd
  simpa only [mul_one] using hd

abbrev identityChart := extChartAt I (1 : SE23)

def chartMatrix (z : SE23.Model) : Mat5 := SE23.toMatrix (identityChart.symm z)
def chartField (v : Algebra) : SE23.Model → SE23.Model :=
  mpullback 𝓘(ℝ, SE23.Model) I identityChart.symm (mulInvariantVectorField v)

@[simp] theorem chart_identity : identityChart (1 : SE23) = 0 := by
  change (Cayley.coordinates ((1:SO3)⁻¹*1),(0:Vec3),(0:Vec3)) = 0
  have h : Cayley.coordinates (1:SO3) = 0 := by
    simpa only [Cayley.rotation_zero] using Cayley.coordinates_rotation (0:Vec3)
  simpa using h

@[simp] theorem chart_symm_zero : identityChart.symm 0 = 1 := by
  simpa only [chart_identity] using extChartAt_to_inv (I := I) (1:SE23)

theorem chart_target : identityChart.target = univ := by
  rw [extChartAt_target, I.range_eq_univ, inter_univ]
  change (fun x : SE23.Model => x) ⁻¹' (SE23.chart (1:SO3)).target = univ
  rw [SE23.chart_target, preimage_univ]

theorem chart_symm_mdifferentiable (z : SE23.Model) :
    MDifferentiableAt 𝓘(ℝ, SE23.Model) I identityChart.symm z := by
  have h := mdifferentiableWithinAt_extChartAt_symm (I := I)
    (x := (1:SE23)) (z := z) (by rw [chart_target]; trivial)
  simpa only [I.range_eq_univ, mdifferentiableWithinAt_univ] using h

theorem chart_matrix_derivative (z : SE23.Model) :
    fderiv ℝ chartMatrix z = (matrixTangent (identityChart.symm z)).comp
      (mfderiv 𝓘(ℝ, SE23.Model) I identityChart.symm z) := by
  rw [← mfderiv_eq_fderiv]
  exact mfderiv_comp z (toMatrix_contMDiff.mdifferentiable (by simp) _) (chart_symm_mdifferentiable z)

theorem chart_field_image (v : Algebra) (z : SE23.Model) :
    fderiv ℝ chartMatrix z (chartField v z) = chartMatrix z*matrixTangent 1 v := by
  have hi := isInvertible_mfderivWithin_extChartAt_symm (I := I)
    (x := (1:SE23)) (y := z) (by rw [chart_target]; trivial)
  simp only [I.range_eq_univ, mfderivWithin_univ] at hi
  obtain ⟨e,he⟩ := hi
  rw [chart_matrix_derivative]
  change matrixTangent _ ((mfderiv 𝓘(ℝ, SE23.Model) I identityChart.symm z)
    ((mfderiv 𝓘(ℝ, SE23.Model) I identityChart.symm z).inverse _)) = _
  rw [← he, ContinuousLinearMap.inverse_equiv]
  simpa only [ContinuousLinearEquiv.coe_coe, e.apply_symm_apply] using invariant_image (identityChart.symm z) v

theorem chart_symm_derivative_zero :
    mfderiv 𝓘(ℝ, SE23.Model) I identityChart.symm 0 =
      ContinuousLinearMap.id ℝ SE23.Model := by
  have h := mfderivWithin_range_extChartAt_symm (I := I) (x := (1:SE23))
  simp only [I.range_eq_univ, mfderivWithin_univ] at h
  change (mfderiv 𝓘(ℝ, SE23.Model) I identityChart.symm (identityChart 1) :
    SE23.Model →L[ℝ] SE23.Model) = ContinuousLinearMap.id ℝ SE23.Model at h
  rwa [chart_identity] at h

theorem chart_matrix_derivative_zero : fderiv ℝ chartMatrix 0 = matrixTangent 1 := by
  rw [chart_matrix_derivative, chart_symm_zero, chart_symm_derivative_zero]
  rfl

theorem chart_field_differentiable (v : Algebra) : DifferentiableAt ℝ (chartField v) 0 := by
  have h := (mdifferentiableAt_mulInvariantVectorField (I := I) (g := (1:SE23)) v).mdifferentiableWithinAt
    (s := univ) |>.differentiableWithinAt_mpullbackWithin_vectorField
  simpa only [I.range_eq_univ, mpullbackWithin_univ, preimage_univ, inter_univ,
    chart_identity, differentiableWithinAt_univ] using h

theorem bracket_in_chart (v w : Algebra) :
    ⁅v,w⁆ = lieBracket ℝ (chartField v) (chartField w) 0 := by
  rw [GroupLieAlgebra.bracket_def]
  change mlieBracketWithin I (mulInvariantVectorField v) (mulInvariantVectorField w) univ 1 = _
  rw [mlieBracketWithin_apply, mfderiv_extChartAt_self, ContinuousLinearMap.inverse_id]
  simp only [I.range_eq_univ, mpullbackWithin_univ, preimage_univ, inter_univ,
    chart_identity, lieBracketWithin_univ]
  rfl

/-- The manifold Lie bracket is the actual matrix commutator under the
derivative of the faithful group representation. -/
theorem matrixTangent_bracket (v w : Algebra) :
    matrixTangent 1 (⁅v,w⁆ : Algebra) = ⁅matrixTangent 1 v,matrixTangent 1 w⁆ := by
  have h := bracket_representation chartMatrix (chartField v) (chartField w)
    (matrixTangent 1 v) (matrixTangent 1 w) 0 (chartMatrix_contDiff 1)
    (chart_field_differentiable v) (chart_field_differentiable w)
    (chart_field_image v) (chart_field_image w)
  simpa only [chart_matrix_derivative_zero, ← bracket_in_chart, chartMatrix,
    chart_symm_zero, SE23.toMatrix_one, Matrix.one_mul, Ring.lie_def] using h

def matrixLieHom : Algebra →ₗ⁅ℝ⁆ Mat5 where
  __ := (matrixTangent 1).toLinearMap
  map_lie' := by intro v w; exact matrixTangent_bracket v w

@[simp] theorem groupExp_zero : groupExp 0 = 1 := by
  apply SE23.toMatrix_injective
  rw [groupExp_toMatrix, show hat (0:LogState) = 0 from hatLinear.map_zero, exp_zero, SE23.toMatrix_one]

def expTangent : LogState →L[ℝ] SE23.Model :=
  mfderiv 𝓘(ℝ, LogState) I groupExp 0

theorem matrix_expTangent (x : LogState) : matrixTangent 1 (expTangent x) = hat x := by
  have hc := mfderiv_comp (I := 𝓘(ℝ, LogState)) (I' := I) (I'' := 𝓘(ℝ, Mat5)) 0
    (toMatrix_contMDiff.mdifferentiable (by simp) _)
    (groupExp_contMDiff.mdifferentiable (by simp) 0)
  have he : SE23.toMatrix ∘ groupExp = fun z => exp (hat z) := funext groupExp_toMatrix
  rw [he, mfderiv_eq_fderiv] at hc
  have h := congrArg (fun L : LogState →L[ℝ] Mat5 => L x) hc
  dsimp only at h
  have hz : Jacobian.blockLeft 0 x = x := by
    ext i j; fin_cases i <;> simp [Jacobian.blockLeft, Jacobian.leftAt, Jacobian.Q_at_zero]
  rw [matrixExp_fderiv_all, hz, show hat (0:LogState) = 0 from hatLinear.map_zero, exp_zero, Matrix.mul_one] at h
  have h' : matrixTangent (groupExp 0) (expTangent x) = hat x := h.symm
  rwa [groupExp_zero] at h'

theorem expTangent_injective : Injective expTangent := by
  intro x y h
  apply hat_injective
  rw [← matrix_expTangent x, ← matrix_expTangent y, h]

def expTangentEquiv : LogState ≃L[ℝ] SE23.Model :=
  (LinearEquiv.ofInjectiveEndo
    (LocalLog.stateEquiv.toLinearMap.comp expTangent.toLinearMap)
    (LocalLog.stateEquiv.injective.comp expTangent_injective)).toContinuousLinearEquiv.trans
      LocalLog.stateEquiv.symm.toContinuousLinearEquiv

@[simp] theorem expTangentEquiv_apply (x : LogState) : expTangentEquiv x = expTangent x :=
  LocalLog.stateEquiv.symm_apply_apply _

theorem matrixTangent_injective : Injective (matrixTangent 1) := by
  intro v w h
  obtain ⟨x,rfl⟩ := expTangentEquiv.surjective v
  obtain ⟨y,rfl⟩ := expTangentEquiv.surjective w
  simp only [expTangentEquiv_apply, matrix_expTangent] at h ⊢
  rw [hat_injective h]

theorem tangent_coordinates_bracket (x y : LogState) :
    @Bracket.bracket Algebra Algebra inferInstance (expTangent x) (expTangent y) =
      expTangent (ad x y) := by
  apply matrixTangent_injective
  calc
    matrixTangent 1 (@Bracket.bracket Algebra Algebra inferInstance (expTangent x) (expTangent y)) =
        ⁅hat x,hat y⁆ := by
      simpa only [matrix_expTangent] using
        matrixTangent_bracket (expTangent x : Algebra) (expTangent y : Algebra)
    _ = matrixTangent 1 (expTangent (ad x y)) := by rw [matrix_expTangent, hat_ad]

theorem matrixTangent_mem (v : Algebra) : matrixTangent 1 v ∈ se23 := by
  obtain ⟨x,rfl⟩ := expTangentEquiv.surjective v
  exact ⟨x, (matrix_expTangent x).symm⟩

def tangentToMatrix : Algebra →ₗ⁅ℝ⁆ se23 where
  __ := (matrixTangent 1).toLinearMap.codRestrict se23.toSubmodule matrixTangent_mem
  map_lie' := by intro v w; exact Subtype.ext (matrixTangent_bracket v w)

/-- The paper's matrix Lie algebra is isomorphic to mathlib's tangent Lie
algebra of the actual smooth SE₂(3) group. -/
def tangentLieEquiv : Algebra ≃ₗ⁅ℝ⁆ se23 := LieEquiv.ofBijective tangentToMatrix ⟨
  fun _ _ h => matrixTangent_injective (congrArg Subtype.val h), by
    rintro ⟨A,x,hx⟩
    refine ⟨expTangent x, Subtype.ext ?_⟩
    exact (matrix_expTangent x).trans hx⟩

end GNC.TangentLieAlgebra
