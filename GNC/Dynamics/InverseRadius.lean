import GNC.Dynamics.GravityField

/-! An algebraic certificate for inverse-square gravity using a proposed
inverse radius. It bounds the complete field without a Taylor remainder.
The residual ||q||²*u²-1 must be bounded and the positive branch certified.
-/
noncomputable section
namespace GNC.Gravity

def inverseRadiusFactor (a : ℝ) : ℝ := (a^2+a+1)/(a+1)

theorem inverseRadiusFactor_nonnegative {a : ℝ} (ha : 0 ≤ a) :
    0 ≤ inverseRadiusFactor a := by unfold inverseRadiusFactor; positivity

theorem inverseRadiusFactor_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    inverseRadiusFactor a ≤ inverseRadiusFactor b := by
  have hb := ha.trans hab
  unfold inverseRadiusFactor
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have h := mul_nonneg (sub_nonneg.mpr hab)
    (show 0 ≤ a*b+a+b by positivity)
  nlinarith

/-- The entire inverse-cube error factors through the squared-radius defect. -/
theorem inverse_cube_defect {r u : ℝ} (hr : 0 < r) (hu : 0 ≤ u) :
    |u^3-1/r^3| * r = inverseRadiusFactor (r*u)/r^2*|r^2*u^2-1| := by
  have ha : 0 ≤ r*u := mul_nonneg hr.le hu
  have hp : 0 < r*u+1 := by positivity
  have he : (u^3-1/r^3)*r = inverseRadiusFactor (r*u)/r^2*(r^2*u^2-1) := by
    unfold inverseRadiusFactor
    field_simp <;> ring
  have h := congrArg abs he
  simpa only [abs_mul,abs_of_pos hr,
    abs_of_nonneg (div_nonneg (inverseRadiusFactor_nonnegative ha) (sq_nonneg r))] using h

theorem inverse_cube_bound {r u m A : ℝ} (hm : 0 < m) (hr : m ≤ r)
    (hu : 0 ≤ u) (hA : r*u ≤ A) :
    |u^3-1/r^3| * r ≤ inverseRadiusFactor A/m^2*|r^2*u^2-1| := by
  have hrp := hm.trans_le hr
  have ha := mul_nonneg hrp.le hu
  rw [inverse_cube_defect hrp hu]
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have hh := mul_le_mul (inverseRadiusFactor_mono ha hA)
    (pow_le_pow_left₀ hm.le hr 2) (sq_nonneg m)
    (inverseRadiusFactor_nonnegative (ha.trans hA))
  nlinarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A bound on the algebraic inverse-radius residual certifies the full
physical gravity vector. No linearization or series truncation is assumed. -/
theorem field_inverse_radius_bound (μ : ℝ) (hμ : 0 ≤ μ) (q : E) {u m A : ℝ}
    (hm : 0 < m) (hr : m ≤ ‖q‖) (hu : 0 ≤ u) (hA : ‖q‖*u ≤ A) :
    ‖field μ q-(-μ*u^3) • q‖ ≤ μ*inverseRadiusFactor A/m^2*|‖q‖^2*u^2-1| := by
  have he : field μ q-(-μ*u^3) • q = (μ*(u^3-1/‖q‖^3)) • q := by
    unfold field
    rw [← sub_smul]
    congr 1
    ring
  rw [he,norm_smul,Real.norm_eq_abs,abs_mul,abs_of_nonneg hμ]
  have hh := mul_le_mul_of_nonneg_left (inverse_cube_bound hm hr hu hA) hμ
  convert hh using 1 <;> ring

end GNC.Gravity
