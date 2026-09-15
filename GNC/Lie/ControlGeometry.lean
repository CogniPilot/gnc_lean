import GNC.Dynamics.GravityAttitude
import GNC.Lie.Control

/-! Geometric form and Euclidean action bound for the off-diagonal inverse
Jacobian remainder in Lemma 4 and Theorem 3. -/
noncomputable section
open Matrix Real
open scoped Matrix
namespace GNC.Control
open Axis

/-- The symmetric remainder after removing the first-order cross term. -/
def mAction (k : Vec3) (a b : ℝ) (u v : Vec3) : Vec3 :=
  (-(a*(k ⬝ᵥ u))) • transverse k v +
    b • ((k ⬝ᵥ v) • transverse k u + (transverse k u ⬝ᵥ v) • k)

theorem mAction_sq (k u v : Vec3) (hk : k ⬝ᵥ k = 1) (a b : ℝ) :
    lengthSq (mAction k a b u v) =
      a^2*(k ⬝ᵥ u)^2*(lengthSq v-(k ⬝ᵥ v)^2) +
      b^2*(k ⬝ᵥ v)^2*(lengthSq u-(k ⬝ᵥ u)^2) +
      b^2*(transverse k u ⬝ᵥ v)^2 -
      2*a*b*(k ⬝ᵥ u)*(k ⬝ᵥ v)*(transverse k u ⬝ᵥ v) := by
  simp only [← dot_self_lengthSq, mAction, transverse, axial, add_dotProduct,
    dotProduct_add, sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul,
    smul_eq_mul, hk, dotProduct_comm u k, dotProduct_comm v k, dotProduct_comm v u]
  ring

theorem transverse_cauchy (k u v : Vec3) (hk : k ⬝ᵥ k = 1) :
    (transverse k u ⬝ᵥ v)^2 ≤
      (lengthSq u-(k ⬝ᵥ u)^2)*(lengthSq v-(k ⬝ᵥ v)^2) := by
  have he : transverse k u ⬝ᵥ transverse k v = transverse k u ⬝ᵥ v := by
    simp [transverse, axial, hk, dotProduct_comm u k]
  have h := lengthSq_nonneg (transverse k u ⨯₃ transverse k v)
  rw [← dot_self_lengthSq, cross_dot_cross,
    dotProduct_comm (transverse k v) (transverse k u), he] at h
  simp only [dot_self_lengthSq, transverse_sq k u hk, transverse_sq k v hk] at h
  nlinarith

/-- The action bound follows by completing a square. This avoids assuming
the spectral reduction or any bound on M's operator norm. -/
theorem mAction_bound (k u v : Vec3) (hk : k ⬝ᵥ k = 1) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 2*b ≤ a) :
    enorm (mAction k a b u v) ≤ a*enorm u*enorm v := by
  have hu := dot_sq_le k u hk
  have hv := dot_sq_le k v hk
  have hc := transverse_cauchy k u v hk
  have he := mAction_sq k u v hk a b
  have hba : 0 ≤ a^2-b^2 := by nlinarith
  have hba2 : 0 ≤ a^2-2*b^2 := by nlinarith
  have h1 := mul_nonneg (mul_nonneg hba (sub_nonneg.mpr hu)) (sq_nonneg (k ⬝ᵥ v))
  have h2 := mul_nonneg (mul_nonneg hba2 (sub_nonneg.mpr hu)) (sub_nonneg.mpr hv)
  have h3 := mul_nonneg (show 0 ≤ 2*b^2 by positivity) (sub_nonneg.mpr hc)
  have h4 := sq_nonneg (a*(k ⬝ᵥ u)*(k ⬝ᵥ v) + b*(transverse k u ⬝ᵥ v))
  have htotal : lengthSq (mAction k a b u v) ≤ a^2*lengthSq u*lengthSq v := by
    nlinarith
  have hsq : lengthSq (mAction k a b u v) ≤ (a*enorm u)^2*lengthSq v := by
    simpa only [mul_pow, enorm_sq, mul_assoc] using htotal
  exact norm_le_of_sq_le (mul_nonneg ha (enorm_nonneg u)) hsq

/-- Lemma 4's coefficient α, with the concrete geometric M. -/
theorem mAction_alpha_bound (k u v : Vec3) (hk : k ⬝ᵥ k = 1)
    (t : ℝ) (ht : 0 < t) (htπ : t < π) :
    enorm (mAction k (Coefficients.alpha t) (Coefficients.beta t/t) u v) ≤
      Coefficients.alpha t*enorm u*enorm v := by
  have hb : 0 ≤ Coefficients.beta t/t := div_nonneg (Coefficients.beta_pos t ht htπ).le ht.le
  have ha := Coefficients.alpha_gt_two_beta_div t ht htπ
  rw [mul_div_assoc] at ha
  apply mAction_bound k u v hk _ _ (by nlinarith) hb
  simpa only [mul_div_assoc] using ha.le

/-- For an axial translation, the residual acts only in the perpendicular plane. -/
theorem mAction_axial (k v : Vec3) (hk : k ⬝ᵥ k = 1) (a b c : ℝ) :
    mAction k a b (c • k) v = (-a*c) • transverse k v := by
  simp [mAction, transverse, axial, hk]

/-- Axial Δω is annihilated, even when the operator's sharp constant is positive. -/
theorem mAction_axial_axial (k : Vec3) (hk : k ⬝ᵥ k = 1) (a b c d : ℝ) :
    mAction k a b (c • k) (d • k) = 0 := by
  rw [mAction_axial k (d • k) hk]
  simp [transverse, axial, hk]

/-- A precise correction to Remark 5: axial u alone does not ensure equality
in the action bound. The connection to DB and Q is proved separately. -/
theorem remark5_strict (k : Vec3) (hk : k ⬝ᵥ k = 1)
    (t : ℝ) (ht : 0 < t) (htπ : t < π) :
    enorm (mAction k (Coefficients.alpha t) (Coefficients.beta t/t) k k) <
      Coefficients.alpha t * enorm k * enorm k := by
  have he := mAction_axial_axial k hk (Coefficients.alpha t) (Coefficients.beta t/t) 1 1
  simp only [one_smul] at he
  rw [he, (enorm_eq_zero_iff (0:Vec3)).mpr rfl, Gravity.unit_enorm k hk]
  have hb := Coefficients.beta_pos t ht htπ
  have ha := Coefficients.alpha_gt_two_beta_div t ht htπ
  rw [mul_div_assoc] at ha
  have hp := div_pos hb ht
  nlinarith

end GNC.Control
