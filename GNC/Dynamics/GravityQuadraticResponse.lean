import GNC.Dynamics.GravityThirdDerivative
import GNC.Dynamics.GravityHessianBilinear

/-! The residual of a quadratic response correction evaluated along the
first linear response. Besides the cubic Taylor remainder, it includes the
change in the Hessian quadratic term between the actual and linear states.
Omitting this second contribution would not certify the response algorithm.
-/
noncomputable section
namespace GNC.Gravity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def quadraticResidual (μ : ℝ) (q p y : E) : E :=
  field μ (q+p)-field μ q-gradient μ q p-(1/2:ℝ) • hessian μ q y y

omit [CompleteSpace E] in
theorem quadratic_residual_split (μ : ℝ) (q p y : E) :
    quadraticResidual μ q p y =
      (1/2:ℝ) • (hessian μ q p p-hessian μ q y y)+
      (field μ (q+p)-field μ q-gradient μ q p-(1/2:ℝ) • hessian μ q p p) := by
  dsimp [quadraticResidual]
  module

/-- All error and region budgets are symbolic. Once the first response has
error eps, the second response has a forcing defect proportional to
eps*(P+Y)/r^4 plus P^3/(r-D)^5. The reference may vary with time. -/
theorem quadratic_residual_bound (μ : ℝ) (hμ : 0 ≤ μ) (q p y : E)
    {r D P Y eps : ℝ} (hD : D < r) (hq : r ≤ ‖q‖)
    (hp : ‖p‖ ≤ P) (hPD : P ≤ D) (hy : ‖y‖ ≤ Y) (he : ‖p-y‖ ≤ eps) :
    ‖quadraticResidual μ q p y‖ ≤
      (3*μ/r^4)*eps*(P+Y)+(4*μ/(r-D)^5)*P^3 := by
  have hP : 0 ≤ P := (norm_nonneg p).trans hp
  have hY : 0 ≤ Y := (norm_nonneg y).trans hy
  have hε : 0 ≤ eps := (norm_nonneg (p-y)).trans he
  have hr : 0 < r := lt_of_le_of_lt (hP.trans hPD) hD
  have hrD : 0 < r-D := sub_pos.mpr hD
  have hqn : q ≠ 0 := norm_pos_iff.mp (hr.trans_le hq)
  have hcoef : 6*μ/‖q‖^4 ≤ 6*μ/r^4 :=
    div_le_div_of_nonneg_left (by positivity) (by positivity)
      (pow_le_pow_left₀ hr.le hq 4)
  have hH := (hessian_difference_bound μ hμ q p y hqn).trans
    (mul_le_mul (mul_le_mul hcoef he (norm_nonneg _) (by positivity))
      (add_le_add hp hy) (by positivity) (by positivity))
  have hH' : ‖(1/2:ℝ) • (hessian μ q p p-hessian μ q y y)‖ ≤
      (3*μ/r^4)*eps*(P+Y) := by
    rw [norm_smul,Real.norm_eq_abs]
    norm_num only [abs_of_pos (by norm_num : (0:ℝ) < 1/2)]
    exact (mul_le_mul_of_nonneg_left hH (by norm_num : (0:ℝ) ≤ 1/2)).trans_eq (by ring)
  have hC := (remainder_cubic μ hμ q p hD hq (hp.trans hPD)).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hp 3) (by positivity))
  rw [quadratic_residual_split]
  exact (norm_add_le _ _).trans (add_le_add hH' hC)

end GNC.Gravity
