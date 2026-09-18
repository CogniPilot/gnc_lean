import GNC.Dynamics.GravityHessianBilinear

/-! Transfer polynomial unit-radius gravity operators to an exact reference.
The surrogate reference is not assumed to lie on the unit sphere. Its full
norm and phase error are charged explicitly. The constants are the actual
coefficients and multilinear degrees of the inverse-square derivatives.
-/
noncomputable section
namespace GNC.Gravity
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def unitGradient (μ : ℝ) (q y : E) : E := μ • ((3*⟪q,y⟫) • q-y)
def unitHessian (μ : ℝ) (q u v : E) : E :=
  (3*μ) • (⟪q,u⟫ • v+⟪q,v⟫ • u+⟪u,v⟫ • q)-
    (15*μ*⟪q,u⟫*⟪q,v⟫) • q

theorem gradient_eq_unit (μ : ℝ) (q y : E) (hq : ‖q‖=1) :
    gradient μ q y=unitGradient μ q y := by
  simp only [gradient,unitGradient,hq,one_pow,div_one]
  module

theorem hessian_eq_unit (μ : ℝ) (q u v : E) (hq : ‖q‖=1) :
    hessian μ q u v=unitHessian μ q u v := by
  simp only [hessian,unitHessian,hq,one_pow,div_one]

theorem inner_smul_bound (a u v : E) :
    ‖⟪a,u⟫ • v‖≤‖a‖*‖u‖*‖v‖ := by
  rw [norm_smul,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (abs_real_inner_le_norm a u) (norm_nonneg v)

theorem inner_product_smul_bound (a b u v w : E) :
    ‖(⟪a,u⟫*⟪b,v⟫) • w‖≤‖a‖*‖b‖*‖w‖*‖u‖*‖v‖ := by
  rw [norm_smul,Real.norm_eq_abs,abs_mul]
  calc
    _≤(‖a‖*‖u‖)*(‖b‖*‖v‖)*‖w‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul (abs_real_inner_le_norm a u) (abs_real_inner_le_norm b v)
          (abs_nonneg _) (by positivity)) (norm_nonneg w)
    _=_ := by ring

theorem unit_gradient_difference (μ : ℝ) (hμ : 0≤μ) (q p y : E) :
    ‖unitGradient μ q y-unitGradient μ p y‖≤
      3*μ*‖q-p‖*(‖q‖+‖p‖)*‖y‖ := by
  have he : unitGradient μ q y-unitGradient μ p y=
      (3*μ) • (⟪q-p,y⟫ • q+⟪p,y⟫ • (q-p)) := by
    simp only [unitGradient,inner_sub_left]
    module
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0≤3*μ)]
  calc
    _≤(3*μ)*(‖q-p‖*‖y‖*‖q‖+‖p‖*‖y‖*‖q-p‖) :=
      mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans
        (add_le_add (inner_smul_bound (q-p) y q) (inner_smul_bound p y (q-p)))) (by positivity)
    _=_ := by ring

theorem unit_hessian_linear_difference (q p u v : E) :
    ‖(⟪q,u⟫ • v+⟪q,v⟫ • u+⟪u,v⟫ • q)-
      (⟪p,u⟫ • v+⟪p,v⟫ • u+⟪u,v⟫ • p)‖≤3*‖q-p‖*‖u‖*‖v‖ := by
  have he : (⟪q,u⟫ • v+⟪q,v⟫ • u+⟪u,v⟫ • q)-
      (⟪p,u⟫ • v+⟪p,v⟫ • u+⟪u,v⟫ • p)=
      ⟪q-p,u⟫ • v+⟪q-p,v⟫ • u+⟪u,v⟫ • (q-p) := by
    simp only [inner_sub_left]
    module
  rw [he]
  calc
    _≤(‖q-p‖*‖u‖*‖v‖+‖q-p‖*‖v‖*‖u‖)+‖u‖*‖v‖*‖q-p‖ :=
      (norm_add_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add
          (inner_smul_bound (q-p) u v) (inner_smul_bound (q-p) v u)))
        (inner_smul_bound u v (q-p)))
    _=_ := by ring

theorem unit_hessian_cubic_difference (q p u v : E) :
    ‖(⟪q,u⟫*⟪q,v⟫) • q-(⟪p,u⟫*⟪p,v⟫) • p‖≤
      ‖q-p‖*(‖q‖^2+‖p‖*‖q‖+‖p‖^2)*‖u‖*‖v‖ := by
  have he : (⟪q,u⟫*⟪q,v⟫) • q-(⟪p,u⟫*⟪p,v⟫) • p=
      (⟪q-p,u⟫*⟪q,v⟫) • q+(⟪p,u⟫*⟪q-p,v⟫) • q+
      (⟪p,u⟫*⟪p,v⟫) • (q-p) := by
    simp only [inner_sub_left]
    module
  rw [he]
  calc
    _≤(‖q-p‖*‖q‖*‖q‖*‖u‖*‖v‖+‖p‖*‖q-p‖*‖q‖*‖u‖*‖v‖)+
        ‖p‖*‖p‖*‖q-p‖*‖u‖*‖v‖ :=
      (norm_add_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add
          (inner_product_smul_bound (q-p) q u v q)
          (inner_product_smul_bound p (q-p) u v q)))
        (inner_product_smul_bound p p u v (q-p)))
    _=_ := by ring

theorem unit_hessian_difference (μ : ℝ) (hμ : 0≤μ) (q p u v : E) :
    ‖unitHessian μ q u v-unitHessian μ p u v‖≤
      μ*‖q-p‖*(9+15*(‖q‖^2+‖p‖*‖q‖+‖p‖^2))*‖u‖*‖v‖ := by
  have he : unitHessian μ q u v-unitHessian μ p u v=
      (3*μ) • ((⟪q,u⟫ • v+⟪q,v⟫ • u+⟪u,v⟫ • q)-
        (⟪p,u⟫ • v+⟪p,v⟫ • u+⟪u,v⟫ • p))-
      (15*μ) • ((⟪q,u⟫*⟪q,v⟫) • q-(⟪p,u⟫*⟪p,v⟫) • p) := by
    simp only [unitHessian]
    module
  rw [he]
  calc
    _≤‖(3*μ) • ((⟪q,u⟫ • v+⟪q,v⟫ • u+⟪u,v⟫ • q)-
        (⟪p,u⟫ • v+⟪p,v⟫ • u+⟪u,v⟫ • p))‖+
      ‖(15*μ) • ((⟪q,u⟫*⟪q,v⟫) • q-(⟪p,u⟫*⟪p,v⟫) • p)‖ := norm_sub_le _ _
    _≤(3*μ)*(3*‖q-p‖*‖u‖*‖v‖)+
      (15*μ)*(‖q-p‖*(‖q‖^2+‖p‖*‖q‖+‖p‖^2)*‖u‖*‖v‖) := by
      rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
        abs_of_nonneg (by positivity : 0≤3*μ),abs_of_nonneg (by positivity : 0≤15*μ)]
      exact add_le_add
        (mul_le_mul_of_nonneg_left (unit_hessian_linear_difference q p u v) (by positivity))
        (mul_le_mul_of_nonneg_left (unit_hessian_cubic_difference q p u v) (by positivity))
    _=_ := by ring

omit [InnerProductSpace ℝ E] in
theorem norm_approximate_unit (q p : E) {ε : ℝ} (hq : ‖q‖=1) (he : ‖q-p‖≤ε) :
    ‖p‖≤1+ε := by
  calc
    _=‖q-(q-p)‖ := by simp
    _≤‖q‖+‖q-p‖ := norm_sub_le _ _
    _≤1+ε := by rw [hq]; exact add_le_add le_rfl he

/-- Full gradient discrepancy with the polynomial surrogate; the
surrogate is allowed to have non-unit norm. -/
theorem gradient_unit_approximation (μ : ℝ) (hμ : 0≤μ) (q p y : E)
    {ε : ℝ} (hq : ‖q‖=1) (he : ‖q-p‖≤ε) :
    ‖gradient μ q y-unitGradient μ p y‖≤3*μ*ε*(2+ε)*‖y‖ := by
  have hε := (norm_nonneg (q-p)).trans he
  have hp := norm_approximate_unit q p hq he
  rw [gradient_eq_unit μ q y hq]
  calc
    _≤3*μ*‖q-p‖*(‖q‖+‖p‖)*‖y‖ := unit_gradient_difference μ hμ q p y
    _≤3*μ*ε*(1+(1+ε))*‖y‖ := by rw [hq]; gcongr
    _=_ := by ring

/-- The half-Hessian mismatch used by a quadratic response. Every term
from the reference's linear and cubic appearances is included. -/
theorem half_hessian_unit_approximation (μ : ℝ) (hμ : 0≤μ) (q p u v : E)
    {ε : ℝ} (hq : ‖q‖=1) (he : ‖q-p‖≤ε) :
    ‖(1/2:ℝ) • (hessian μ q u v-unitHessian μ p u v)‖≤
      (μ*ε*(9+15*(1+(1+ε)+(1+ε)^2))/2)*‖u‖*‖v‖ := by
  have hε := (norm_nonneg (q-p)).trans he
  have hp := norm_approximate_unit q p hq he
  rw [hessian_eq_unit μ q u v hq,norm_smul,Real.norm_eq_abs,
    abs_of_pos (by norm_num : (0:ℝ)<1/2)]
  calc
    _≤(1/2)*(μ*‖q-p‖*(9+15*(‖q‖^2+‖p‖*‖q‖+‖p‖^2))*‖u‖*‖v‖) :=
      mul_le_mul_of_nonneg_left (unit_hessian_difference μ hμ q p u v) (by norm_num)
    _≤(1/2)*(μ*ε*(9+15*(1+(1+ε)+(1+ε)^2))*‖u‖*‖v‖) := by
      rw [hq]
      norm_num only [one_pow,mul_one]
      gcongr
    _=_ := by ring

end GNC.Gravity
