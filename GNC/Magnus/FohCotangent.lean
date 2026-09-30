import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-! Elementary scalar coefficients for first-order-hold slope resummation.
These results prove scalar calculus and integral identities. Their interpretation
as logarithms of the actual FOH flow is a separate variation/assembly theorem.
The variable `θ` is the accumulated midpoint rotation, not squared rotation.
-/
noncomputable section
namespace GNC.Magnus

def fohCotC (θ : ℝ) : ℝ :=
  (1 - θ / 2 * (Real.cos (θ / 2) / Real.sin (θ / 2))) / θ ^ 2

def fohCotD (θ : ℝ) : ℝ := (fohCotC θ - 1 / 12) / θ ^ 2

def fohCotAlpha (θ : ℝ) : ℝ := -(fohCotC θ)^2 / 2 - fohCotD θ / 2

def fohCotBeta (θ : ℝ) : ℝ := 3 * fohCotD θ

def fohCotGamma (θ : ℝ) : ℝ :=
  ((fohCotC θ)^2 - 5 * fohCotD θ) / (2 * θ ^ 2)

theorem fohCotC_eq_cot (θ : ℝ) :
    fohCotC θ = (1 - θ / 2 * Real.cot (θ / 2)) / θ ^ 2 := by
  simp [fohCotC, Real.cot_eq_cos_div_sin]

/-- Derivative in angle: c'(f)=(c²-3d)/2 for f=θ². -/
theorem fohCotC_hasDerivAt {θ : ℝ} (hθ : θ ≠ 0)
    (hs : Real.sin (θ / 2) ≠ 0) :
    HasDerivAt fohCotC
      (θ * ((fohCotC θ)^2 - 3 * fohCotD θ)) θ := by
  have hh : HasDerivAt (fun t : ℝ => t / 2) (1 / 2) θ :=
    (hasDerivAt_id θ).div_const 2
  have hc := hh.cos
  have hs' := hh.sin
  have h := ((hasDerivAt_const θ (1 : ℝ)).sub (hh.mul (hc.div hs' hs))).div
    ((hasDerivAt_id θ).pow 2) (pow_ne_zero 2 hθ)
  convert h using 1
  dsimp [fohCotC, fohCotD]
  field_simp
  nlinarith [Real.sin_sq_add_cos_sq (θ / 2)]

theorem fohCot_quadratic_commuting {θ : ℝ} (hθ : θ ≠ 0) :
    fohCotAlpha θ + fohCotBeta θ + θ ^ 2 * fohCotGamma θ = 0 := by
  unfold fohCotAlpha fohCotBeta fohCotGamma
  field_simp
  ring

/-- All quadratic coefficients reuse the linear coefficient and its derivative. -/
theorem fohCot_quadratic_derivative_forms {θ : ℝ} (hθ : θ ≠ 0)
    (hs : Real.sin (θ / 2) ≠ 0) :
    fohCotAlpha θ = -(deriv fohCotC θ / (2 * θ)) - 2 * fohCotD θ ∧
    fohCotBeta θ = 3 * fohCotD θ ∧
    fohCotGamma θ = (deriv fohCotC θ / (2 * θ) - fohCotD θ) / θ ^ 2 := by
  rw [(fohCotC_hasDerivAt hθ hs).deriv]
  unfold fohCotAlpha fohCotBeta fohCotGamma
  constructor
  · field_simp; ring
  constructor
  · rfl
  · field_simp; ring

/-- Primitive for the first slope insertion. -/
theorem fohCot_linear_primitive (θ t : ℝ) (hθ : θ ≠ 0) :
    HasDerivAt (fun x => -x * Real.cos (θ*x) / θ + Real.sin (θ*x) / θ^2)
      (t * Real.sin (θ*t)) t := by
  have hi := (hasDerivAt_id t).const_mul θ
  convert (((hasDerivAt_id t).neg.mul hi.cos).div_const θ).add
    (hi.sin.div_const (θ^2)) using 1 <;> dsimp
  field_simp
  ring

/-- Exact finite integral used by the first variation. -/
theorem fohCot_linear_integral (θ : ℝ) (hθ : θ ≠ 0) :
    (∫ t in (-1/2 : ℝ)..(1/2), t * Real.sin (θ*t)) =
      2 * Real.sin (θ/2) / θ^2 - Real.cos (θ/2) / θ := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => fohCot_linear_primitive θ t hθ)
    ((continuous_id.mul (Real.continuous_sin.comp (continuous_const.mul continuous_id))).intervalIntegrable (-1/2) (1/2))
  rw [h]
  simp only [mul_neg, neg_div, Real.cos_neg, Real.sin_neg]
  ring_nf

/-- The first-variation integral gives the cot coefficient, not a fitted series. -/
theorem fohCotC_from_integral {θ : ℝ} (hθ : θ ≠ 0)
    (hs : Real.sin (θ / 2) ≠ 0) :
    (∫ t in (-1/2 : ℝ)..(1/2), t * Real.sin (θ*t)) /
      (2 * Real.sin (θ/2)) = fohCotC θ := by
  rw [fohCot_linear_integral θ hθ]
  unfold fohCotC
  field_simp


/-- Primitive for the mixed longitudinal/transverse slope insertion. -/
theorem fohCot_mixed_primitive (θ t : ℝ) (hθ : θ ≠ 0) :
    HasDerivAt (fun x => -(x^3-x/4) * Real.cos (θ*x) / θ +
      (3*x^2-1/4)*Real.sin (θ*x)/θ^2 +
      6*x*Real.cos (θ*x)/θ^3 - 6*Real.sin (θ*x)/θ^4)
      (t*(t^2-1/4)*Real.sin (θ*t)) t := by
  have hi := (hasDerivAt_id t).const_mul θ
  have hp := ((hasDerivAt_id t).pow 3).sub ((hasDerivAt_id t).div_const 4)
  have hq := (((hasDerivAt_id t).pow 2).const_mul 3).sub (hasDerivAt_const t (1/4 : ℝ))
  convert ((((hp.neg.mul hi.cos).div_const θ).add
    ((hq.mul hi.sin).div_const (θ^2))).add
    ((((hasDerivAt_id t).const_mul 6).mul hi.cos).div_const (θ^3))).sub
    ((hi.sin.const_mul 6).div_const (θ^4)) using 1 <;> dsimp
  field_simp
  ring

theorem fohCot_mixed_integral (θ : ℝ) (hθ : θ ≠ 0) :
    (∫ t in (-1/2 : ℝ)..(1/2), t*(t^2-1/4)*Real.sin (θ*t)) =
      Real.sin (θ/2)/θ^2 + 6*Real.cos (θ/2)/θ^3 - 12*Real.sin (θ/2)/θ^4 := by
  have hc : Continuous (fun t : ℝ => t*(t^2-1/4)*Real.sin (θ*t)) := by fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => fohCot_mixed_primitive θ t hθ) (hc.intervalIntegrable _ _)]
  simp only [mul_neg, neg_div, Real.cos_neg, Real.sin_neg]
  ring_nf

/-- Primitive for the symmetrized second diagonal insertion. -/
theorem fohCot_diagonal_primitive (θ t : ℝ) (hθ : θ ≠ 0) :
    HasDerivAt (fun x => (3*x^2-1/4)*Real.sin (θ*x)/θ +
      6*x*Real.cos (θ*x)/θ^2 - 6*Real.sin (θ*x)/θ^3)
      ((3*t^2-1/4)*Real.cos (θ*t)) t := by
  have hi := (hasDerivAt_id t).const_mul θ
  have hq := (((hasDerivAt_id t).pow 2).const_mul 3).sub (hasDerivAt_const t (1/4 : ℝ))
  convert (((hq.mul hi.sin).div_const θ).add
    ((((hasDerivAt_id t).const_mul 6).mul hi.cos).div_const (θ^2))).sub
    ((hi.sin.const_mul 6).div_const (θ^3)) using 1 <;> dsimp
  field_simp
  ring

theorem fohCot_diagonal_integral (θ : ℝ) (hθ : θ ≠ 0) :
    (∫ t in (-1/2 : ℝ)..(1/2), (3*t^2-1/4)*Real.cos (θ*t)) =
      Real.sin (θ/2)/θ + 6*Real.cos (θ/2)/θ^2 - 12*Real.sin (θ/2)/θ^3 := by
  have hc : Continuous (fun t : ℝ => (3*t^2-1/4)*Real.cos (θ*t)) := by fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => fohCot_diagonal_primitive θ t hθ) (hc.intervalIntegrable _ _)]
  simp only [mul_neg, neg_div, Real.cos_neg, Real.sin_neg]
  ring_nf

/-- The exact mixed integral gives beta. -/
theorem fohCotBeta_from_integral {θ : ℝ} (hθ : θ ≠ 0)
    (hs : Real.sin (θ/2) ≠ 0) :
    -(∫ t in (-1/2 : ℝ)..(1/2), t*(t^2-1/4)*Real.sin (θ*t)) /
      (4*Real.sin (θ/2)) = fohCotBeta θ := by
  rw [fohCot_mixed_integral θ hθ]
  unfold fohCotBeta fohCotD fohCotC
  field_simp
  <;> ring

/-- The exact diagonal integral gives alpha after the quadratic log correction. -/
theorem fohCotAlpha_from_integral {θ : ℝ} (hθ : θ ≠ 0)
    (hs : Real.sin (θ/2) ≠ 0) :
    (∫ t in (-1/2 : ℝ)..(1/2), (3*t^2-1/4)*Real.cos (θ*t)) /
      (24*θ*Real.sin (θ/2)) - (fohCotC θ)^2/2 = fohCotAlpha θ := by
  rw [fohCot_diagonal_integral θ hθ]
  unfold fohCotAlpha fohCotD fohCotC
  field_simp
  <;> ring

end GNC.Magnus
