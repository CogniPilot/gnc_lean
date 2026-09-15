import GNC.Lie.ControlResidual

/-! Euclidean operator norms and sharpness in Lemma 4 and Remark 5,
connected to the actual differentiated Jacobian remainder. -/
noncomputable section
open Matrix Real
open scoped Matrix
namespace GNC.Control

def mLinear (k : Vec3) (a b : ℝ) (u : Vec3) : Jacobian.E3 →ₗ[ℝ] Jacobian.E3 where
  toFun v := WithLp.toLp 2 (mAction k a b u (WithLp.ofLp v))
  map_add' v w := by
    apply (WithLp.linearEquiv 2 ℝ Vec3).injective
    change mAction k a b u (WithLp.ofLp v+WithLp.ofLp w) =
      mAction k a b u (WithLp.ofLp v)+mAction k a b u (WithLp.ofLp w)
    simp [mAction, Axis.transverse, Axis.axial, dotProduct_add, smul_add, add_smul]
    module
  map_smul' c v := by
    apply (WithLp.linearEquiv 2 ℝ Vec3).injective
    change mAction k a b u (c • WithLp.ofLp v) = c • mAction k a b u (WithLp.ofLp v)
    simp [mAction, Axis.transverse, Axis.axial, smul_sub, smul_add, smul_smul]
    module

def mCLM (k : Vec3) (t : ℝ) (u : Vec3) : Jacobian.E3 →L[ℝ] Jacobian.E3 :=
  (mLinear k (Coefficients.alpha t) (Coefficients.beta t/t) u).toContinuousLinearMap

theorem mCLM_actual (k u v : Vec3) (hk : k ⬝ᵥ k = 1) (t : ℝ) (ht : 0 < t) (htπ : t < π) :
    WithLp.ofLp (mCLM k t u (WithLp.toLp 2 v)) = Jacobian.M (t • k) u v := by
  exact (Jacobian.M_eq_geometric k u v hk t ht htπ).symm

/-- Lemma 4's induced operator norm statement, in Euclidean L². -/
theorem mCLM_bound (k u : Vec3) (hk : k ⬝ᵥ k = 1) (t : ℝ) (ht : 0 < t) (htπ : t < π) :
    ‖mCLM k t u‖ ≤ Coefficients.alpha t*enorm u := by
  have hb := Coefficients.beta_pos t ht htπ
  have ha := Coefficients.alpha_gt_two_beta_div t ht htπ
  have hp : 0 ≤ Coefficients.alpha t :=
    (lt_trans (div_pos (mul_pos (by norm_num) hb) ht) ha).le
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hp (enorm_nonneg u))
  intro v
  exact mAction_alpha_bound k u (WithLp.ofLp v) hk t ht htπ

theorem m_axial_perpendicular (k v : Vec3) (hk : k ⬝ᵥ k = 1) (hv : k ⬝ᵥ v = 0)
    (t c : ℝ) (ht : 0 < t) (htπ : t < π) :
    Jacobian.M (t • k) (c • k) v = (-Coefficients.alpha t*c) • v := by
  rw [Jacobian.M_eq_geometric k (c • k) v hk t ht htπ, mAction_axial k v hk]
  simp [Axis.transverse, Axis.axial, hv]

/-- Axial translation attains the sharp operator bound; a perpendicular
angular input attains the corresponding action bound. -/
theorem mCLM_axial_norm (k : Vec3) (hk : k ⬝ᵥ k = 1) (t c : ℝ)
    (ht : 0 < t) (htπ : t < π) :
    ‖mCLM k t (c • k)‖ = Coefficients.alpha t*enorm (c • k) := by
  have hb := Coefficients.beta_pos t ht htπ
  have ha := Coefficients.alpha_gt_two_beta_div t ht htπ
  have hp : 0 ≤ Coefficients.alpha t :=
    (lt_trans (div_pos (mul_pos (by norm_num) hb) ht) ha).le
  apply le_antisymm (mCLM_bound k (c • k) hk t ht htπ)
  obtain ⟨v,hv,hkv⟩ := Jacobian.exists_perpendicular k
  have hvp : 0 < enorm v := lt_of_le_of_ne (enorm_nonneg v)
    (Ne.symm (mt (enorm_eq_zero_iff v).mp hv))
  have h := (mCLM k t (c • k)).le_opNorm (WithLp.toLp 2 v)
  change enorm (WithLp.ofLp (mCLM k t (c • k) (WithLp.toLp 2 v))) ≤ _ at h
  rw [mCLM_actual k (c • k) v hk t ht htπ, m_axial_perpendicular k v hk hkv t c ht htπ,
    enorm_smul, abs_mul, abs_neg, abs_of_nonneg hp] at h
  rw [enorm_smul, Gravity.unit_enorm k hk, mul_one]
  exact (mul_le_mul_iff_left₀ hvp).mp (by simpa [mul_comm, mul_left_comm, mul_assoc] using h)

/-- The β action bound is attained for every perpendicular angular input. -/
theorem diagonal_perpendicular_norm (k v : Vec3) (hk : k ⬝ᵥ k = 1)
    (hv : k ⬝ᵥ v = 0) (t : ℝ) (ht : 0 < t) (htπ : t < π) :
    enorm (Jacobian.diagonalRemainder (t • k) v) = Coefficients.beta t*enorm v := by
  rw [Jacobian.diagonalRemainder_axis k v hk t ht]
  simp [Axis.transverse, Axis.axial, hv, enorm_neg, enorm_smul,
    abs_of_pos (Coefficients.beta_pos t ht htπ)]

end GNC.Control
