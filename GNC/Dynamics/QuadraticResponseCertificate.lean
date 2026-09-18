import GNC.Dynamics.GravityQuadraticResponse
import GNC.Dynamics.InitialOrbitCertificate
import GNC.Analysis.QuadraticMajorant

/-! A posteriori certificates for computed first-plus-quadratic Cartesian
responses. The reference and both responses may have numerical defects.
The full inverse-square remainder includes the Hessian correction mismatch;
no exact response solve, discarded tail, or integration tolerance is assumed.
All scalar bounds may depend on time and on an externally quantified family.
-/
noncomputable section
namespace GNC.Gravity
open Set Planning.PolynomialKernel
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The three computed residuals plus the physical gravity remainder give
the exact acceleration defect of the summed predictor. -/
theorem quadratic_response_defect_identity (μ scale : ℝ)
    (q y z qa ya za u du : E) :
    scale • (field μ (q+(y+z))+(u+du))-(qa+(ya+za)) =
      (scale • (field μ q+u)-qa) +
      (scale • (gradient μ q y+du)-ya) +
      (scale • (gradient μ q z+(1/2:ℝ) • hessian μ q y y)-za) +
      scale • quadraticResidual μ q (y+z) y := by
  have hg : gradient μ q (y+z)=gradient μ q y+gradient μ q z := by
    simp only [gradient,inner_add_right,mul_add,add_div,add_smul,smul_add]
    module
  simp only [quadraticResidual,hg]
  module

/-- Radius-floor gradient bound used to certify the sizes of the computed
responses. The nominal point may change with time. -/
theorem response_gradient_bound (μ scale : ℝ) (hμ : 0≤μ) (hs : 0≤scale)
    (q y : E) {r : ℝ} (hr : 0<r) (hq : r≤‖q‖) :
    ‖scale • gradient μ q y‖≤(scale*(2*μ/r^3))*‖y‖ := by
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hs]
  have hc : 2*μ/‖q‖^3≤2*μ/r^3 :=
    div_le_div_of_nonneg_left (by positivity) (by positivity)
      (pow_le_pow_left₀ hr.le hq 3)
  calc
    _≤scale*((2*μ/‖q‖^3)*‖y‖) := mul_le_mul_of_nonneg_left (gradient_bound μ hμ q y) hs
    _≤scale*((2*μ/r^3)*‖y‖) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hc (norm_nonneg _)) hs
    _=_ := by ring

/-- The response-size calculation charges its own computed ODE defect. -/
theorem computed_linear_response_acceleration (μ scale : ℝ)
    (hμ : 0≤μ) (hs : 0≤scale) (q y ya du : E) {r U ε : ℝ}
    (hr : 0<r) (hq : r≤‖q‖) (hu : ‖scale • du‖≤U)
    (he : ‖scale • (gradient μ q y+du)-ya‖≤ε) :
    ‖ya‖≤(scale*(2*μ/r^3))*‖y‖+(U+ε) := by
  have hi : ya=scale • gradient μ q y+scale • du-
      (scale • (gradient μ q y+du)-ya) := by module
  rw [hi]
  calc
    _≤‖scale • gradient μ q y+scale • du‖+
        ‖scale • (gradient μ q y+du)-ya‖ := norm_sub_le _ _
    _≤((scale*(2*μ/r^3))*‖y‖+U)+ε :=
      add_le_add ((norm_add_le _ _).trans
        (add_le_add (response_gradient_bound μ scale hμ hs q y hr hq) hu)) he
    _=_ := by ring

/-- Quadratic-response growth is driven by the proved first-response
radius. Its computed ODE defect is charged independently. -/
theorem computed_quadratic_response_acceleration (μ scale : ℝ)
    (hμ : 0≤μ) (hs : 0≤scale) (q y z za : E) {r Y ε : ℝ}
    (hr : 0<r) (hq : r≤‖q‖) (hy : ‖y‖≤Y)
    (he : ‖scale • (gradient μ q z+(1/2:ℝ) • hessian μ q y y)-za‖≤ε) :
    ‖za‖≤(scale*(2*μ/r^3))*‖z‖+(scale*(3*μ/r^4)*Y^2+ε) := by
  have hY := (norm_nonneg y).trans hy
  have hqn : q≠0 := norm_pos_iff.mp (hr.trans_le hq)
  have hc : 6*μ/‖q‖^4≤6*μ/r^4 :=
    div_le_div_of_nonneg_left (by positivity) (by positivity)
      (pow_le_pow_left₀ hr.le hq 4)
  have hh : ‖scale • ((1/2:ℝ) • hessian μ q y y)‖≤scale*(3*μ/r^4)*Y^2 := by
    rw [norm_smul,norm_smul,Real.norm_eq_abs,abs_of_nonneg hs]
    norm_num only [Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<1/2)]
    have hbound := (hessian_bound μ hμ q y hqn).trans
      (mul_le_mul hc (pow_le_pow_left₀ (norm_nonneg y) hy 2) (by positivity) (by positivity))
    calc
      _≤scale*((1/2)*((6*μ/r^4)*Y^2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hbound (by norm_num)) hs
      _=_ := by ring
  have hi : za=scale • gradient μ q z+scale • ((1/2:ℝ) • hessian μ q y y)-
      (scale • (gradient μ q z+(1/2:ℝ) • hessian μ q y y)-za) := by module
  rw [hi]
  calc
    _≤‖scale • gradient μ q z+scale • ((1/2:ℝ) • hessian μ q y y)‖+
        ‖scale • (gradient μ q z+(1/2:ℝ) • hessian μ q y y)-za‖ := norm_sub_le _ _
    _≤((scale*(2*μ/r^3))*‖z‖+scale*(3*μ/r^4)*Y^2)+ε :=
      add_le_add ((norm_add_le _ _).trans
        (add_le_add (response_gradient_bound μ scale hμ hs q z hr hq) hh)) he
    _=_ := by ring

variable [CompleteSpace E]

/-- `Y` and `Z` bound the two computed responses, not the unknown trajectory
error. The `Z*(2*Y+Z)` term is essential even when their defining ODEs are
solved exactly. Reference and numerical response defects are separate. -/
theorem quadratic_response_defect_bound (μ scale : ℝ)
    (hμ : 0≤μ) (hs : 0≤scale) (q y z qa ya za u du : E)
    {r Y Z ε₀ ε₁ ε₂ : ℝ} (hq : r≤‖q‖) (hregion : Y+Z<r)
    (hy : ‖y‖≤Y) (hz : ‖z‖≤Z)
    (h₀ : ‖scale • (field μ q+u)-qa‖≤ε₀)
    (h₁ : ‖scale • (gradient μ q y+du)-ya‖≤ε₁)
    (h₂ : ‖scale • (gradient μ q z+(1/2:ℝ) • hessian μ q y y)-za‖≤ε₂) :
    ‖scale • (field μ (q+(y+z))+(u+du))-(qa+(ya+za))‖ ≤
      ε₀+ε₁+ε₂+scale*((3*μ/r^4)*Z*(2*Y+Z)+
        (4*μ/(r-(Y+Z))^5)*(Y+Z)^3) := by
  have hp : ‖y+z‖≤Y+Z := (norm_add_le y z).trans (add_le_add hy hz)
  have he : ‖y+z-y‖≤Z := by simpa only [add_sub_cancel_left] using hz
  have hb := quadratic_residual_bound μ hμ q (y+z) y hregion hq hp le_rfl hy he
  have hb' : ‖scale • quadraticResidual μ q (y+z) y‖≤
      scale*((3*μ/r^4)*Z*(2*Y+Z)+(4*μ/(r-(Y+Z))^5)*(Y+Z)^3) := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hs]
    convert mul_le_mul_of_nonneg_left hb hs using 1
    ring
  rw [quadratic_response_defect_identity]
  exact (norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add h₀ h₁)) h₂)) hb')

/-- Compose the full computed quadratic-response defect with a checked
polynomial envelope. Initial mismatch is explicitly allowed. This is a
bound for every solution of the full physical ODE on the interval; solution
existence remains a separate obligation, as in `initial_polynomial_prediction`.
The candidate radius floor `r` and nominal radius floor `r₀` are distinct. -/
theorem quadratic_response_polynomial_prediction (μ scale : ℝ)
    (hμ : 0≤μ) (hs : 0≤scale)
    (x xv q qv qa y yv ya z zv za u du : ℝ → E)
    (Y Z ε₀ ε₁ ε₂ : ℝ → ℝ) {κ p₀ v₀ : ℚ} (f p : List ℚ)
    (hp : InitialPolynomialForcing.Valid κ p₀ v₀ f p) (hκ : 0≤κ) (hk : κ<56)
    {r₀ r M : ℝ} (hr : 0<r) (hM : 0≤M)
    (hclose : PolynomialOrder.value p 1<M) (hlip : scale*(2*μ/r^3)≤(κ:ℝ))
    (hregion : ∀ t ∈ Icc (0:ℝ) 1, r+M≤‖q t+(y t+z t)‖)
    (hnominal : ∀ t ∈ Icc (0:ℝ) 1, r₀≤‖q t‖ ∧ Y t+Z t<r₀)
    (hy : ∀ t ∈ Icc (0:ℝ) 1, ‖y t‖≤Y t)
    (hz : ∀ t ∈ Icc (0:ℝ) 1, ‖z t‖≤Z t)
    (h₀ : ∀ t ∈ Icc (0:ℝ) 1, ‖scale • (field μ (q t)+u t)-qa t‖≤ε₀ t)
    (h₁ : ∀ t ∈ Icc (0:ℝ) 1, ‖scale • (gradient μ (q t) (y t)+du t)-ya t‖≤ε₁ t)
    (h₂ : ∀ t ∈ Icc (0:ℝ) 1,
      ‖scale • (gradient μ (q t) (z t)+(1/2:ℝ) • hessian μ (q t) (y t) (y t))-za t‖≤ε₂ t)
    (hbudget : ∀ t ∈ Icc (0:ℝ) 1,
      ε₀ t+ε₁ t+ε₂ t+scale*((3*μ/r₀^4)*Z t*(2*Y t+Z t)+
        (4*μ/(r₀-(Y t+Z t))^5)*(Y t+Z t)^3)≤PolynomialOrder.value f t)
    (hx : Continuous x) (hv : Continuous xv)
    (hcq : Continuous q) (hcqv : Continuous qv)
    (hcy : Continuous y) (hcyv : Continuous yv)
    (hcz : Continuous z) (hczv : Continuous zv)
    (hdx : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt x (xv t) t)
    (hdv : ∀ t ∈ Icc (0:ℝ) 1,
      HasDerivAt xv (scale • (field μ (x t)+(u t+du t))) t)
    (hdq : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt q (qv t) t)
    (hdqv : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt qv (qa t) t)
    (hdy : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt y (yv t) t)
    (hdyv : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt yv (ya t) t)
    (hdz : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt z (zv t) t)
    (hdzv : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt zv (za t) t)
    (hip : ‖x 0-(q 0+(y 0+z 0))‖≤(p₀:ℝ))
    (hiv : ‖xv 0-(qv 0+(yv 0+zv 0))‖≤(v₀:ℝ)) :
    ∀ t ∈ Icc (0:ℝ) 1,
      ‖x t-(q t+(y t+z t))‖≤PolynomialOrder.value p t ∧
      ‖xv t-(qv t+(yv t+zv t))‖≤PolynomialOrder.value (differentiate p) t := by
  apply initial_polynomial_prediction μ scale hμ hs x xv
    (fun t => q t+(y t+z t)) (fun t => qv t+(yv t+zv t))
    (fun t => qa t+(ya t+za t)) (fun t => u t+du t) f p hp hκ hk hr hM
    hclose hlip hregion hx hv (hcq.add (hcy.add hcz)) (hcqv.add (hcyv.add hczv))
    hdx hdv (fun t ht => (hdq t ht).add ((hdy t ht).add (hdz t ht)))
    (fun t ht => (hdqv t ht).add ((hdyv t ht).add (hdzv t ht))) hip hiv
  intro t ht
  exact (quadratic_response_defect_bound μ scale hμ hs
    (q t) (y t) (z t) (qa t) (ya t) (za t) (u t) (du t)
    (hnominal t ht).1 (hnominal t ht).2 (hy t ht) (hz t ht)
    (h₀ t ht) (h₁ t ht) (h₂ t ht)).trans (hbudget t ht)

end GNC.Gravity
