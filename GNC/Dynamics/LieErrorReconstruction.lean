import GNC.Dynamics.LieGravityPullback
import GNC.Analysis.OcticPointing

/-! Physical output certificates from SE2(3) error coordinates. For a fixed
attitude error the position/velocity columns of Exp are linear contractions
in their translation arguments. A translation-error ball may be mapped once
at output, without expanding it into Cartesian state-transition tensors.
The same-attitude hypothesis is essential; attitude estimation error is not
silently omitted from these results. -/
noncomputable section
namespace GNC
open Matrix Real

theorem leftAt_nonexpansive (φ v : Vec3) (hφ : enorm φ<2*π) :
    enorm (Jacobian.leftAt φ v)≤enorm v := by
  by_cases hz : enorm φ=0
  · rw [(enorm_eq_zero_iff φ).mp hz]
    simp [Jacobian.leftAt]
  · have hp : 0<enorm φ := lt_of_le_of_ne (enorm_nonneg φ) (Ne.symm hz)
    rw [Jacobian.leftAt_eq φ v hp]
    exact (Jacobian.left_bounds (Jacobian.unitAxis φ) v
      (Jacobian.unitAxis_unit φ hp) (enorm φ) hp hφ).2

/-- Same-angle reconstruction cannot enlarge a translation-error radius. -/
theorem lie_translation_error_bound (R : SO3) (φ ρ ρhat : Vec3) {ε : ℝ}
    (hφ : enorm φ<2*π) (hρ : enorm (ρ-ρhat)≤ε) :
    enorm (rotate R (Jacobian.leftAt φ ρ)-rotate R (Jacobian.leftAt φ ρhat))≤ε := by
  change enorm (R.val *ᵥ Jacobian.leftAt φ ρ-R.val *ᵥ Jacobian.leftAt φ ρhat)≤ε
  rw [←Matrix.mulVec_sub]
  change enorm (rotate R (Jacobian.leftAt φ ρ-Jacobian.leftAt φ ρhat))≤ε
  rw [rotate_enorm,←Jacobian.leftAt_sub]
  exact (leftAt_nonexpansive φ (ρ-ρhat) hφ).trans hρ

/-- A single exponential map transports the certified SE2(3) translation
columns to physical position and velocity, with no extra radius inflation. -/
theorem groupExp_translation_certificate (reference : SE23) (x xhat : LogState)
    {ep ev : ℝ} (hφ : enorm (x 2)<2*π) (hangle : x 2=xhat 2)
    (hp : enorm (x 0-xhat 0)≤ep) (hv : enorm (x 1-xhat 1)≤ev) :
    enorm ((reference*groupExp x).pos-(reference*groupExp xhat).pos)≤ep ∧
    enorm ((reference*groupExp x).vel-(reference*groupExp xhat).vel)≤ev := by
  constructor
  · simpa only [SE23.mul_pos,groupExp,←hangle,add_sub_add_left_eq_sub] using
      lie_translation_error_bound reference.rot (x 2) (x 0) (xhat 0) hφ hp
  · simpa only [SE23.mul_vel,groupExp,←hangle,add_sub_add_left_eq_sub] using
      lie_translation_error_bound reference.rot (x 2) (x 1) (xhat 1) hφ hv

/-- A factored query avoiding divisions by the uncertain angle. The Lie
translation is theta*z, as holds for a zero-error initial trajectory. -/
def factoredTranslation (k z : Vec3) (θ : ℝ) : Vec3 :=
  θ • z+(1-cos θ) • (k ⨯₃ z)+(θ-sin θ) • (k ⨯₃ (k ⨯₃ z))

theorem factoredTranslation_eq (k z : Vec3) (hk : k ⬝ᵥ k=1) (θ : ℝ) :
    factoredTranslation k z θ=Jacobian.leftAt (θ • k) (θ • z) := by
  by_cases hz : θ=0
  · subst θ; simp [factoredTranslation,Jacobian.leftAt]
  · have hn : enorm (θ • k)=|θ| := by rw [enorm_smul,Gravity.unit_enorm k hk,mul_one]
    by_cases hp : 0≤θ
    · simp only [factoredTranslation,Jacobian.leftAt,hn,abs_of_nonneg hp,
        map_smul,LinearMap.smul_apply,smul_smul]
      match_scalars <;> field_simp <;> ring
    · simp only [factoredTranslation,Jacobian.leftAt,hn,abs_of_neg (lt_of_not_ge hp),
        cos_neg,sin_neg,map_smul,LinearMap.smul_apply,smul_smul]
      match_scalars <;> field_simp <;> ring

def polynomialTranslation (k z : Vec3) (θ : ℝ) : Vec3 :=
  θ • z+OcticPointing.cosineLoss θ • (k ⨯₃ z)+
    (θ-OcticPointing.sine θ) • (k ⨯₃ (k ⨯₃ z))

/-- Trigonometric checking may be polynomial while the delivered query
retains exact reconstruction. This tail is charged, not called zero. -/
theorem factoredTranslation_polynomial_bound (k z : Vec3) (hk : k ⬝ᵥ k=1) (θ : ℝ) :
    enorm (factoredTranslation k z θ-polynomialTranslation k z θ)≤
      (|θ|^9/362880+|θ|^10/3628800)*enorm z := by
  have he : factoredTranslation k z θ-polynomialTranslation k z θ=
      (1-cos θ-OcticPointing.cosineLoss θ) • (k ⨯₃ z)+
      (OcticPointing.sine θ-sin θ) • (k ⨯₃ (k ⨯₃ z)) := by
    dsimp [factoredTranslation,polynomialTranslation]
    module
  rw [he]
  have hklen := Gravity.unit_enorm k hk
  have h1 : enorm (k ⨯₃ z)≤enorm z := by simpa [hklen] using cross_enorm_le k z
  have h21 : enorm (k ⨯₃ (k ⨯₃ z))≤enorm (k ⨯₃ z) := by
    simpa [hklen] using cross_enorm_le k (k ⨯₃ z)
  have h2 := h21.trans h1
  have hs := OcticPointing.sine_bound θ
  have hc := OcticPointing.cosine_bound θ
  rw [abs_sub_comm] at hs
  apply (enorm_add_le _ _).trans
  rw [enorm_smul,enorm_smul]
  have hb := add_le_add (mul_le_mul hc h1 (enorm_nonneg _) (by positivity))
    (mul_le_mul hs h2 (enorm_nonneg _) (by positivity))
  convert hb using 1 <;> ring

/-- Known-reference interpolation error is separate from uncertain attitude.
This bound transfers a polynomial checker using an approximate axis to the
exact-axis query. No time-dependent approximation is charged as zero. -/
theorem polynomialTranslation_axis_bound (k khat z : Vec3) (θ : ℝ)
    {δ C H : ℝ} (hk : enorm k≤1) (hδ : enorm (k-khat)≤δ)
    (hC : |OcticPointing.cosineLoss θ|≤C) (hH : |θ-OcticPointing.sine θ|≤H) :
    enorm (polynomialTranslation k z θ-polynomialTranslation khat z θ)≤
      (C*δ+H*δ*(2+δ))*enorm z := by
  have hd0 : 0≤δ := (enorm_nonneg _).trans hδ
  have hc0 : 0≤C := (abs_nonneg _).trans hC
  have hh0 : 0≤H := (abs_nonneg _).trans hH
  have hn : enorm khat≤1+δ := by
    have he : khat=k+ -(k-khat) := by module
    rw [he]
    exact (enorm_add_le _ _).trans (by simpa only [enorm_neg] using add_le_add hk hδ)
  have h1 : enorm ((k-khat) ⨯₃ z)≤δ*enorm z :=
    (cross_enorm_le _ _).trans (mul_le_mul_of_nonneg_right hδ (enorm_nonneg _))
  have h21 : enorm (k ⨯₃ ((k-khat) ⨯₃ z))≤δ*enorm z := by
    exact (cross_enorm_le _ _).trans (by nlinarith [mul_le_mul hk h1 (enorm_nonneg _) (by norm_num)])
  have h22 : enorm ((k-khat) ⨯₃ (khat ⨯₃ z))≤δ*(1+δ)*enorm z := by
    have ha := (cross_enorm_le khat z).trans (mul_le_mul_of_nonneg_right hn (enorm_nonneg _))
    exact (cross_enorm_le _ _).trans (by nlinarith [mul_le_mul hδ ha (enorm_nonneg _) hd0])
  have he : polynomialTranslation k z θ-polynomialTranslation khat z θ=
      OcticPointing.cosineLoss θ • ((k-khat) ⨯₃ z)+
      (θ-OcticPointing.sine θ) • (k ⨯₃ ((k-khat) ⨯₃ z)+(k-khat) ⨯₃ (khat ⨯₃ z)) := by
    simp only [polynomialTranslation,map_sub,LinearMap.sub_apply]
    module
  have h2 : enorm (k ⨯₃ ((k-khat) ⨯₃ z)+(k-khat) ⨯₃ (khat ⨯₃ z))≤δ*(2+δ)*enorm z := by
    exact (enorm_add_le _ _).trans (by nlinarith [h21,h22])
  rw [he]
  apply (enorm_add_le _ _).trans
  rw [enorm_smul,enorm_smul]
  have ha := add_le_add (mul_le_mul hC h1 (enorm_nonneg _) hc0)
    (mul_le_mul hH h2 (enorm_nonneg _) hh0)
  nlinarith [ha]

end GNC
