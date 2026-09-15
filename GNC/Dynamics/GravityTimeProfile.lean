import GNC.Dynamics.GravityQuadraticResponse
import GNC.Analysis.MonomialSupersolutionComparison

/-! Gravity remainder profiles for a burn starting with zero displacement.
The displacement and first-response bounds remain explicit hypotheses.
The reference point may vary with time; only its stated radius lower bound
is used. These results do not freeze the physical inverse-square field. -/
noncomputable section
namespace GNC.Gravity
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem remainder_cubic_time (μ : ℝ) (hμ : 0≤μ) (q d : E)
    {r P t : ℝ} (hP0 : 0≤P) (hP : P<r) (hq : r≤‖q‖)
    (ht : t ∈ Icc (0:ℝ) 1) (hd : ‖d‖≤P*t^2) :
    ‖field μ (q+d)-field μ q-gradient μ q d-(1/2:ℝ) • hessian μ q d d‖ ≤
      ((4*μ/(r-P)^5)*P^3)*t^6 := by
  have hPt : P*t^2≤P := mul_le_of_le_one_right hP0 (pow_le_one₀ ht.1 ht.2)
  have h := remainder_cubic μ hμ q d hP hq (hd.trans hPt)
  have hc : 0≤4*μ/(r-P)^5 :=
    div_nonneg (mul_nonneg (by norm_num) hμ) (pow_nonneg (sub_pos.mpr hP).le 5)
  calc
    _ ≤ (4*μ/(r-P)^5)*‖d‖^3 := h
    _ ≤ (4*μ/(r-P)^5)*(P*t^2)^3 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg d) hd 3) hc
    _ = _ := by ring

theorem quadratic_residual_time (μ : ℝ) (hμ : 0≤μ) (q p y : E)
    {r P Y eps t : ℝ} (hP0 : 0≤P) (hP : P<r) (hq : r≤‖q‖)
    (ht : t ∈ Icc (0:ℝ) 1) (hp : ‖p‖≤P*t^2) (hy : ‖y‖≤Y*t^2)
    (he : ‖p-y‖≤eps*t^4) :
    ‖quadraticResidual μ q p y‖ ≤
      ((3*μ/r^4)*eps*(P+Y)+(4*μ/(r-P)^5)*P^3)*t^6 := by
  have hPt : P*t^2≤P := mul_le_of_le_one_right hP0 (pow_le_one₀ ht.1 ht.2)
  have h := quadratic_residual_bound μ hμ q p y hP hq hp hPt hy he
  convert h using 1 <;> ring

/-- Once the t^6 physical source profile above is available, its monomial
envelope is at least 28 times tighter at the endpoint than the constant-source
envelope with the same coefficient and gain. Both remain sufficient bounds. -/
theorem sixth_order_envelope_saving {κ C : ℝ} (hκ : 0≤κ) (hk : κ<56) (hC : 0≤C) :
    C*MonomialSupersolution.value κ 6 1 ≤
      (C*MonomialSupersolution.value κ 0 1)/28 := by
  have h := mul_le_mul_of_nonneg_left
    (MonomialSupersolution.sixth_order_improvement hκ hk) hC
  simpa only [mul_div_assoc] using h

end GNC.Gravity
