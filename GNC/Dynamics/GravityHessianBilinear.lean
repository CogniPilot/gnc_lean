import GNC.Dynamics.GravityField
import GNC.Analysis.SymmetricBilinearBound

/-! The sharp gravity Hessian bound in two different directions, and the
quadratic-difference bound needed to certify successive response corrections.
-/
noncomputable section
open Real
open scoped RealInnerProductSpace
namespace GNC.Gravity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def hessianBilinear (μ : ℝ) (q : E) : E →ₗ[ℝ] E →ₗ[ℝ] E :=
  LinearMap.mk₂ ℝ (hessian μ q)
    (by
      intro u v w
      simp only [hessian,inner_add_right,inner_add_left,mul_add,add_mul,
        add_div,add_smul,smul_add]
      module)
    (by
      intro c u v
      simp only [hessian,real_inner_smul_left,real_inner_smul_right]
      module)
    (by
      intro u v w
      simp only [hessian,inner_add_right,inner_add_left,mul_add,add_mul,
        add_div,add_smul,smul_add]
      module)
    (by
      intro c u v
      simp only [hessian,real_inner_smul_left,real_inner_smul_right]
      module)

theorem hessian_mixed_bound (μ : ℝ) (hμ : 0 ≤ μ) (q u v : E) (hq : q ≠ 0) :
    ‖hessian μ q u v‖ ≤ (6*μ/‖q‖^4)*‖u‖*‖v‖ :=
  SymmetricBilinearBound.bound (hessianBilinear μ q)
    (hessian_symmetric μ q) (fun w => hessian_bound μ hμ q w hq) u v

theorem hessian_diagonal_difference (μ : ℝ) (q p y : E) :
    hessian μ q p p-hessian μ q y y = hessian μ q (p-y) (p+y) := by
  change hessianBilinear μ q p p-hessianBilinear μ q y y =
    hessianBilinear μ q (p-y) (p+y)
  simp only [map_add,map_sub,LinearMap.sub_apply]
  change hessian μ q p p-hessian μ q y y =
    hessian μ q p p-hessian μ q y p+(hessian μ q p y-hessian μ q y y)
  rw [hessian_symmetric μ q y p]
  abel

theorem hessian_difference_bound (μ : ℝ) (hμ : 0 ≤ μ) (q p y : E) (hq : q ≠ 0) :
    ‖hessian μ q p p-hessian μ q y y‖ ≤
      (6*μ/‖q‖^4)*‖p-y‖*(‖p‖+‖y‖) := by
  rw [hessian_diagonal_difference]
  exact (hessian_mixed_bound μ hμ q (p-y) (p+y) hq).trans
    (mul_le_mul_of_nonneg_left (norm_add_le p y) (by positivity))

/-- Exactly three parameter monomials suffice for the quadratic forcing of
a two-column finite-angle response. No angle truncation is involved. -/
theorem hessian_combination (μ : ℝ) (q S C : E) (s c : ℝ) :
    (1/2:ℝ) • hessian μ q (s • S+c • C) (s • S+c • C) =
      s^2 • ((1/2:ℝ) • hessian μ q S S)+(s*c) • hessian μ q S C+
      c^2 • ((1/2:ℝ) • hessian μ q C C) := by
  change (1/2:ℝ) • hessianBilinear μ q (s • S+c • C) (s • S+c • C) = _
  simp only [map_add,map_smul,LinearMap.add_apply,LinearMap.smul_apply]
  change (1/2:ℝ) •
    (s • (s • hessian μ q S S+c • hessian μ q C S)+
      c • (s • hessian μ q S C+c • hessian μ q C C)) = _
  rw [hessian_symmetric μ q C S]
  module

end GNC.Gravity
