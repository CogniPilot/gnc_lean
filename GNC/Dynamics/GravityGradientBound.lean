import GNC.Dynamics.GravityLinearization

/-! The sharp Euclidean operator bound for the inverse-square gravity
gradient. Its radial eigenvalue has twice the magnitude of each transverse
eigenvalue. The proof uses the actual gradient and inner-product geometry.
-/
noncomputable section
namespace GNC.Gravity
open scoped RealInnerProductSpace
set_option autoImplicit false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem normalized_gradient_sq (k v : E) (hk : ‖k‖ = 1) :
    ‖(3*⟪k,v⟫) • k-v‖^2 = ‖v‖^2+3*⟪k,v⟫^2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_sub_left,inner_sub_right,real_inner_smul_left,real_inner_smul_right,
    real_inner_self_eq_norm_sq,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,hk,real_inner_comm v k]
  ring

theorem normalized_gradient_bound (k v : E) (hk : ‖k‖ = 1) :
    ‖(3*⟪k,v⟫) • k-v‖ ≤ 2*‖v‖ := by
  have hc := abs_real_inner_le_norm k v
  rw [hk,one_mul] at hc
  have hs := normalized_gradient_sq k v hk
  nlinarith [sq_abs ⟪k,v⟫,abs_nonneg ⟪k,v⟫,norm_nonneg v,
    norm_nonneg ((3*⟪k,v⟫) • k-v)]

theorem gradient_bound (μ : ℝ) (hμ : 0 ≤ μ) (q v : E) :
    ‖gradient μ q v‖ ≤ (2*μ/‖q‖^3)*‖v‖ := by
  by_cases hq : q = 0
  · simp [gradient,hq]
  have hn : 0 < ‖q‖ := norm_pos_iff.mpr hq
  let k := ‖q‖⁻¹ • q
  have hk : ‖k‖ = 1 := by simp [k,norm_smul,hn.ne']
  have he : gradient μ q v = (μ/‖q‖^3) • ((3*⟪k,v⟫) • k-v) := by
    rw [gradient_radial]
    dsimp [k]
    simp only [real_inner_smul_left]
    match_scalars <;> field_simp
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  convert mul_le_mul_of_nonneg_left (normalized_gradient_bound k v hk)
    (show 0 ≤ μ/‖q‖^3 by positivity) using 1
  ring

theorem gradient3_bound (μ : ℝ) (hμ : 0 ≤ μ) (q v : Vec3) :
    GNC.enorm (gradient3 μ q v) ≤ (2*μ/GNC.enorm q^3)*GNC.enorm v :=
  gradient_bound μ hμ (WithLp.toLp 2 q : Jacobian.E3) (WithLp.toLp 2 v)

end GNC.Gravity
