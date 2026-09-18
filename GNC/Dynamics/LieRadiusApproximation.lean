import GNC.Dynamics.LieRadiusCertificate

/-! Error budgets for the scalar-radius certificate when its known rotating
axis is represented by a polynomial. The approximate axis is not assumed
unit. These inequalities charge that defect before any numerical record is
accepted. The resulting radius expression needs only scalar projections,
without an expanded Cartesian trajectory witness.
-/
noncomputable section
namespace GNC.LieRadiusApproximation
open Matrix Real

theorem abs_dot_bound (a b : Vec3) : |a ⬝ᵥ b|≤enorm a*enorm b := by
  have h := abs_real_inner_le_norm (WithLp.toLp 2 b : EuclideanSpace ℝ (Fin 3))
    (WithLp.toLp 2 a : EuclideanSpace ℝ (Fin 3))
  change |a ⬝ᵥ star b|≤enorm b*enorm a at h
  simpa only [star_trivial,mul_comm] using h

theorem approximate_axis_norm (k khat : Vec3) {δ : ℝ}
    (hk : enorm k≤1) (hδ : enorm (k-khat)≤δ) : enorm khat≤1+δ := by
  have he : khat=k+ -(k-khat) := by module
  rw [he]
  exact (enorm_add_le _ _).trans (by simpa only [enorm_neg] using add_le_add hk hδ)

theorem cross_square_axis_error (k khat z : Vec3) {δ : ℝ}
    (hk : enorm k≤1) (hδ : enorm (k-khat)≤δ) :
    enorm (k ⨯₃ (k ⨯₃ z)-khat ⨯₃ (khat ⨯₃ z))≤δ*(2+δ)*enorm z := by
  have hd : 0≤δ := (enorm_nonneg _).trans hδ
  have hn := approximate_axis_norm k khat hk hδ
  have h1 := (cross_enorm_le (k-khat) z).trans
    (mul_le_mul_of_nonneg_right hδ (enorm_nonneg z))
  have h2 := (cross_enorm_le khat z).trans
    (mul_le_mul_of_nonneg_right hn (enorm_nonneg z))
  have hleft := (cross_enorm_le k ((k-khat) ⨯₃ z)).trans
    (mul_le_mul hk h1 (enorm_nonneg _) (by norm_num))
  have hright := (cross_enorm_le (k-khat) (khat ⨯₃ z)).trans
    (mul_le_mul hδ h2 (enorm_nonneg _) hd)
  have he : k ⨯₃ (k ⨯₃ z)-khat ⨯₃ (khat ⨯₃ z)=
      k ⨯₃ ((k-khat) ⨯₃ z)+(k-khat) ⨯₃ (khat ⨯₃ z) := by
    simp only [map_sub,LinearMap.sub_apply]
    module
  rw [he]
  exact (enorm_add_le _ _).trans ((add_le_add hleft hright).trans_eq (by ring))

/-- Axis interpolation error in the quadratic inverse is charged separately
from the already proved truncation error of that inverse. -/
theorem inverse_axis_error (k khat v : Vec3) (θ : ℝ) {δ : ℝ}
    (hk : enorm k≤1) (hδ : enorm (k-khat)≤δ) :
    enorm (jacobianInverseQuadratic (θ • k) v-jacobianInverseQuadratic (θ • khat) v)≤
      (|θ|/2+θ^2*(2+δ)/12)*δ*enorm v := by
  have he : jacobianInverseQuadratic (θ • k) v-jacobianInverseQuadratic (θ • khat) v=
      (-θ/2) • ((k-khat) ⨯₃ v)+(θ^2/12) •
        (k ⨯₃ (k ⨯₃ v)-khat ⨯₃ (khat ⨯₃ v)) := by
    simp only [jacobianInverseQuadratic,map_smul,LinearMap.smul_apply,
      smul_smul,LinearMap.sub_apply,map_sub]
    module
  have h1 := (cross_enorm_le (k-khat) v).trans
    (mul_le_mul_of_nonneg_right hδ (enorm_nonneg v))
  have h2 := cross_square_axis_error k khat v hk hδ
  rw [he]
  apply (enorm_add_le _ _).trans
  rw [enorm_smul,enorm_smul,abs_div,abs_neg,abs_of_nonneg (by positivity : 0≤θ^2/12)]
  norm_num only [abs_of_pos (by norm_num : (0:ℝ)<2)]
  convert add_le_add
    (mul_le_mul_of_nonneg_left h1 (by positivity : 0≤|θ|/2))
    (mul_le_mul_of_nonneg_left h2 (by positivity : 0≤θ^2/12)) using 1 <;> ring

/-- Retaining only the linear inverse-radius offset in the polynomial Lie
residual leaves an explicitly bounded cubic polynomial. The supplied R is
the actual residual norm; no term is silently set to zero. -/
theorem inverse_cube_residual_bound (a ρ b φ φhat w what : Vec3) (K h : ℝ)
    (hK : 0≤K) {R P W E F H : ℝ}
    (hR : enorm (a+K • ρ+(3*K*h) • ρ-φhat ⨯₃ b+(3*K*h) • what)≤R)
    (hρ : enorm ρ≤P) (hw : enorm w≤W) (hwe : enorm (w-what)≤E)
    (hforce : enorm ((φ-φhat) ⨯₃ b)≤F) (hh : |h|≤H) :
    enorm (a+(K*(1+h)^3) • ρ-φ ⨯₃ b+(K*((1+h)^3-1)) • w)≤
      R+K*(3*H^2+H^3)*(P+W)+3*K*H*E+F := by
  have hH : 0≤H := (abs_nonneg h).trans hh
  have hP : 0≤P := (enorm_nonneg _).trans hρ
  have hW : 0≤W := (enorm_nonneg _).trans hw
  have hE : 0≤E := (enorm_nonneg _).trans hwe
  have he : a+(K*(1+h)^3) • ρ-φ ⨯₃ b+(K*((1+h)^3-1)) • w=
      (a+K • ρ+(3*K*h) • ρ-φhat ⨯₃ b+(3*K*h) • what)+
      (K*(3*h^2+h^3)) • (ρ+w)+(3*K*h) • (w-what)-((φ-φhat) ⨯₃ b) := by
    simp only [map_sub,LinearMap.sub_apply]
    module
  have ht : |3*h^2+h^3|≤3*H^2+H^3 := by
    have ha := abs_add_le (3*h^2) (h^3)
    rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<3),abs_pow,abs_pow] at ha
    exact ha.trans (by gcongr)
  have hc : |K*(3*h^2+h^3)|≤K*(3*H^2+H^3) := by
    rw [abs_mul,abs_of_nonneg hK]
    exact mul_le_mul_of_nonneg_left ht hK
  have hd : |3*K*h|≤3*K*H := by
    rw [abs_mul,abs_of_nonneg (by positivity : 0≤3*K)]
    exact mul_le_mul_of_nonneg_left hh (by positivity)
  have hpw := (enorm_add_le ρ w).trans (add_le_add hρ hw)
  have htail : enorm ((K*(3*h^2+h^3)) • (ρ+w))≤K*(3*H^2+H^3)*(P+W) := by
    rw [enorm_smul]
    exact mul_le_mul hc hpw (enorm_nonneg _) (by positivity)
  have haxis : enorm ((3*K*h) • (w-what))≤3*K*H*E := by
    rw [enorm_smul]
    exact mul_le_mul hd hwe (enorm_nonneg _) (by positivity)
  rw [he,sub_eq_add_neg]
  apply (enorm_add_le _ _).trans
  rw [enorm_neg]
  apply add_le_add _ hforce
  apply (enorm_add_le _ _).trans
  exact add_le_add ((enorm_add_le _ _).trans (add_le_add hR htail)) haxis

/-- The squared axial projection is stable even for a nonunit approximate
axis. The factor 2+delta is derived, not a normalization allowance. -/
theorem axial_square_error (k khat z : Vec3) {δ : ℝ}
    (hk : enorm k≤1) (hδ : enorm (k-khat)≤δ) :
    |(k ⬝ᵥ z)^2-(khat ⬝ᵥ z)^2|≤δ*(2+δ)*enorm z^2 := by
  have hd : 0≤δ := (enorm_nonneg _).trans hδ
  have hkhat := approximate_axis_norm k khat hk hδ
  have h1 : |(k-khat) ⬝ᵥ z|≤δ*enorm z :=
    (abs_dot_bound _ _).trans (mul_le_mul_of_nonneg_right hδ (enorm_nonneg z))
  have h2 : |(k+khat) ⬝ᵥ z|≤(2+δ)*enorm z := by
    have hn : enorm (k+khat)≤2+δ :=
      (enorm_add_le _ _).trans (by linarith)
    exact (abs_dot_bound _ _).trans (mul_le_mul_of_nonneg_right hn (enorm_nonneg z))
  have he : (k ⬝ᵥ z)^2-(khat ⬝ᵥ z)^2=((k-khat) ⬝ᵥ z)*((k+khat) ⬝ᵥ z) := by
    rw [sub_dotProduct,add_dotProduct]
    ring
  rw [he,abs_mul]
  convert mul_le_mul h1 h2 (abs_nonneg _) (mul_nonneg hd (enorm_nonneg z)) using 1 <;> ring

def gram (k z : Vec3) (θ c : ℝ) : ℝ :=
  θ^2*(k ⬝ᵥ z)^2+2*c*(lengthSq z-(k ⬝ᵥ z)^2)

theorem gram_axis_error (k khat z : Vec3) (θ c : ℝ) {δ : ℝ}
    (hk : enorm k≤1) (hδ : enorm (k-khat)≤δ) :
    |gram k z θ c-gram khat z θ c|≤
      (θ^2+2*|c|)*δ*(2+δ)*enorm z^2 := by
  have he : gram k z θ c-gram khat z θ c=
      (θ^2-2*c)*((k ⬝ᵥ z)^2-(khat ⬝ᵥ z)^2) := by unfold gram; ring
  have hc : |θ^2-2*c|≤θ^2+2*|c| := by
    have hh := abs_sub (θ^2) (2*c)
    rwa [abs_of_nonneg (sq_nonneg θ),abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] at hh
  rw [he,abs_mul]
  convert mul_le_mul hc (axial_square_error k khat z hk hδ) (abs_nonneg _)
    (by positivity : 0≤θ^2+2*|c|) using 1 <;> ring

theorem gram_trigonometric_error (k z : Vec3) (hk : k ⬝ᵥ k=1) (θ c : ℝ) :
    |lengthSq (factoredTranslation k z θ)-gram k z θ c|≤
      2*|1-cos θ-c| * enorm z^2 := by
  have hlow : 0≤lengthSq z-(k ⬝ᵥ z)^2 := sub_nonneg.mpr (Axis.dot_sq_le k z hk)
  have hupp : lengthSq z-(k ⬝ᵥ z)^2≤enorm z^2 := by rw [enorm_sq]; nlinarith
  rw [factoredTranslation_lengthSq k z hk θ]
  have he : θ^2*(k ⬝ᵥ z)^2+2*(1-cos θ)*(lengthSq z-(k ⬝ᵥ z)^2)-gram k z θ c=
      2*(1-cos θ-c)*(lengthSq z-(k ⬝ᵥ z)^2) := by unfold gram; ring
  rw [he,abs_mul,abs_mul,abs_of_nonneg hlow]
  rw [abs_of_pos (by norm_num : (0:ℝ)<2)]
  exact mul_le_mul_of_nonneg_left hupp (by positivity)

/-- Scalar Gram error for the actual unit axis and the polynomial axis,
including both the cosine tail and the nonunit-axis perturbation. -/
theorem gram_error (k khat z : Vec3) (hk : k ⬝ᵥ k=1) (θ : ℝ)
    {δ C : ℝ} (hδ : enorm (k-khat)≤δ) (hC : |OcticPointing.cosineLoss θ|≤C) :
    |lengthSq (factoredTranslation k z θ)-gram khat z θ (OcticPointing.cosineLoss θ)|≤
      (2*|θ|^10/3628800+(θ^2+2*C)*δ*(2+δ))*enorm z^2 := by
  have hd : 0≤δ := (enorm_nonneg _).trans hδ
  have h0 := gram_trigonometric_error k z hk θ (OcticPointing.cosineLoss θ)
  have h1 := gram_axis_error k khat z θ (OcticPointing.cosineLoss θ)
    (le_of_eq (Gravity.unit_enorm k hk)) hδ
  have hb : |lengthSq (factoredTranslation k z θ)-gram khat z θ (OcticPointing.cosineLoss θ)|≤
      2*|1-cos θ-OcticPointing.cosineLoss θ| * enorm z^2+
      (θ^2+2*|OcticPointing.cosineLoss θ|)*δ*(2+δ)*enorm z^2 := by
    exact (abs_sub_le _ _ _).trans (add_le_add h0 h1)
  have ht := OcticPointing.cosine_bound θ
  apply hb.trans
  calc
    _ ≤ 2*(|θ|^10/3628800)*enorm z^2+(θ^2+2*C)*δ*(2+δ)*enorm z^2 := by gcongr
    _ = _ := by ring

def radiusApprox (q k z : Vec3) (θ : ℝ) : ℝ :=
  lengthSq q+2*(q ⬝ᵥ polynomialTranslation k z θ)+
    gram k z θ (OcticPointing.cosineLoss θ)

def translationBudget (σ δ C H : ℝ) : ℝ :=
  σ^9/362880+σ^10/3628800+C*δ+H*δ*(2+δ)

def gramBudget (σ δ C : ℝ) : ℝ :=
  2*σ^10/3628800+(σ^2+2*C)*δ*(2+δ)

/-- The complete squared-radius comparison. It charges a scalar reference
projection and a Gram error, without squaring a reconstructed polynomial. -/
theorem radius_error (q k khat z : Vec3) (hk : k ⬝ᵥ k=1) (θ : ℝ)
    {δ C H : ℝ} (hδ : enorm (k-khat)≤δ)
    (hC : |OcticPointing.cosineLoss θ|≤C) (hH : |θ-OcticPointing.sine θ|≤H) :
    |enorm (q+factoredTranslation k z θ)^2-radiusApprox q khat z θ|≤
      2*enorm q*translationBudget |θ| δ C H*enorm z+
      gramBudget |θ| δ C*enorm z^2 := by
  have h1 := factoredTranslation_polynomial_bound k z hk θ
  have h2 := polynomialTranslation_axis_bound k khat z θ
    (le_of_eq (Gravity.unit_enorm k hk)) hδ hC hH
  have ht : enorm (factoredTranslation k z θ-polynomialTranslation khat z θ)≤
      translationBudget |θ| δ C H*enorm z := by
    have ha := (enorm_add_le (factoredTranslation k z θ-polynomialTranslation k z θ)
      (polynomialTranslation k z θ-polynomialTranslation khat z θ)).trans (add_le_add h1 h2)
    rw [sub_add_sub_cancel] at ha
    convert ha using 1 <;> unfold translationBudget <;> ring
  have hg := gram_error k khat z hk θ hδ hC
  have he : enorm (q+factoredTranslation k z θ)^2-radiusApprox q khat z θ=
      2*(q ⬝ᵥ (factoredTranslation k z θ-polynomialTranslation khat z θ))+
      (lengthSq (factoredTranslation k z θ)-gram khat z θ (OcticPointing.cosineLoss θ)) := by
    rw [enorm_sq]
    simp only [radiusApprox,←dot_self_lengthSq,add_dotProduct,dotProduct_add,
      dotProduct_sub,dotProduct_comm (factoredTranslation k z θ) q]
    ring
  rw [he]
  have hdot := (abs_dot_bound q _).trans (mul_le_mul_of_nonneg_left ht (enorm_nonneg q))
  have hb := (abs_add_le _ _).trans (add_le_add
    (show |2*(q ⬝ᵥ (factoredTranslation k z θ-polynomialTranslation khat z θ))|≤
      2*(enorm q*(translationBudget |θ| δ C H*enorm z)) by
      rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
      exact mul_le_mul_of_nonneg_left hdot (by norm_num)) hg)
  convert hb using 1 <;> unfold gramBudget <;> rw [sq_abs] <;> ring

/-- Preserve the known quadratic translation growth in the radius budget.
The projection error grows quadratically and the Gram error quartically;
neither is replaced by a constant disturbance over the whole burn. -/
theorem radius_error_growth (q k khat z : Vec3) (hk : k ⬝ᵥ k=1) (θ t : ℝ)
    {σ δ C H Z : ℝ} (hθ : |θ|≤σ) (hδ : enorm (k-khat)≤δ)
    (hC : |OcticPointing.cosineLoss θ|≤C) (hH : |θ-OcticPointing.sine θ|≤H)
    (hz : enorm z≤Z*t^2) :
    |enorm (q+factoredTranslation k z θ)^2-radiusApprox q khat z θ|≤
      (2*enorm q*translationBudget σ δ C H*Z)*t^2+
      (gramBudget σ δ C*Z^2)*t^4 := by
  have hd : 0≤δ := (enorm_nonneg _).trans hδ
  have hc : 0≤C := (abs_nonneg _).trans hC
  have hh : 0≤H := (abs_nonneg _).trans hH
  have hs : 0≤σ := (abs_nonneg θ).trans hθ
  have hq := enorm_nonneg q
  have hz0 := enorm_nonneg z
  apply (radius_error q k khat z hk θ hδ hC hH).trans
  calc
    _ ≤ 2*enorm q*translationBudget σ δ C H*(Z*t^2)+
        gramBudget σ δ C*(Z*t^2)^2 := by
      unfold translationBudget gramBudget
      gcongr
    _ = _ := by ring

end GNC.LieRadiusApproximation
