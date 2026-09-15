import GNC.Analysis.PolynomialIntegral
import Mathlib.Analysis.InnerProductSpace.Basic

/-! Integrate a transport norm using exact polynomial squared-norm data.
A positive rational Young parameter replaces numerical square-root
quadrature. Approximation error is charged before integration. The forcing
may depend on the state; only its norm bound along the trajectory is used.
-/
noncomputable section
namespace GNC.PolynomialNormIntegral
open MeasureTheory Set
open Planning.PolynomialKernel PolynomialIntegral

variable {E : Type*} [NormedAddCommGroup E]

theorem norm_young (v : E) {ν : ℝ} (hν : 0 < ν) :
    ‖v‖ ≤ (‖v‖^2+ν^2)/(2*ν) := by
  apply (le_div_iff₀ (by positivity : 0 < 2*ν)).mpr
  nlinarith [sq_nonneg (‖v‖-ν)]

theorem integral_norm_of_squared (k : ℝ → E) {a b ν S : ℝ}
    (hab : a ≤ b) (hk : ContinuousOn k (Icc a b)) (hν : 0 < ν)
    (hS : (∫ t in a..b, ‖k t‖^2) ≤ S) :
    (∫ t in a..b, ‖k t‖) ≤ (S+(b-a)*ν^2)/(2*ν) := by
  have hn := hk.norm.intervalIntegrable_of_Icc (μ := volume) hab
  have hs := (hk.norm.pow 2).intervalIntegrable_of_Icc (μ := volume) hab
  have hy := intervalIntegral.integral_mono_on (μ := volume) hab hn
    ((hs.add intervalIntegrable_const).div_const (2*ν))
    (fun t _ => norm_young (k t) hν)
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add hs intervalIntegrable_const,
    intervalIntegral.integral_const, smul_eq_mul] at hy
  exact hy.trans (div_le_div_of_nonneg_right (add_le_add hS le_rfl) (by positivity))

/-- A polynomial squared-norm envelope gives a rational upper bound on the
norm integral. The envelope is checked for every real time, not just nodes. -/
theorem rational_bound (k : ℝ → E) (cs : List ℚ) {a b ν ε : ℚ}
    (hab : a ≤ b) (hk : ContinuousOn k (Icc (a:ℝ) (b:ℝ))) (hν : 0 < ν)
    (he : ∀ t ∈ Icc (a:ℝ) (b:ℝ),
      ‖k t‖^2 ≤ evaluate (cs.map (Rat.castHom ℝ)) t+(ε:ℝ)) :
    (∫ t in (a:ℝ)..(b:ℝ), ‖k t‖) ≤
      (((integrate cs a b+(b-a)*(ν^2+ε))/(2*ν):ℚ):ℝ) := by
  have habR : (a:ℝ) ≤ (b:ℝ) := by exact_mod_cast hab
  have hi := intervalIntegral.integral_mono_on (μ := volume) habR
    ((hk.norm.pow 2).intervalIntegrable_of_Icc habR)
    (((evaluate_continuous _).add continuous_const).intervalIntegrable _ _) he
  simp only [Pi.add_apply] at hi
  rw [intervalIntegral.integral_add ((evaluate_continuous _).intervalIntegrable _ _)
    intervalIntegrable_const, rational_integral, intervalIntegral.integral_const,
    smul_eq_mul] at hi
  have h := integral_norm_of_squared k (ν := (ν:ℝ)) habR hk (by exact_mod_cast hν) hi
  simp only [Rat.cast_div, Rat.cast_add, Rat.cast_mul, Rat.cast_sub, Rat.cast_pow,
    Rat.cast_ofNat] at h ⊢
  convert h using 1 <;> ring

variable [InnerProductSpace ℝ E]

/-- A certified norm integral bounds the transported effect of every
continuous bounded forcing, including a nonlinear trajectory residual. -/
theorem forced_pairing (k r : ℝ → E) {a b R G : ℝ} (hab : a ≤ b)
    (hk : ContinuousOn k (Icc a b)) (hr : ContinuousOn r (Icc a b))
    (hR : 0 ≤ R) (hb : ∀ t ∈ Icc a b, ‖r t‖ ≤ R)
    (hG : (∫ t in a..b, ‖k t‖) ≤ G) :
    |∫ t in a..b, inner ℝ (k t) (r t)| ≤ G*R := by
  have hm := intervalIntegral.integral_mono_on (μ := volume) hab
    ((hk.inner hr).abs.intervalIntegrable_of_Icc hab)
    ((hk.norm.mul continuousOn_const).intervalIntegrable_of_Icc hab)
    (fun t ht => (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left (hb t ht) (norm_nonneg _)))
  have h := (intervalIntegral.abs_integral_le_integral_abs hab
    (f := fun t => inner ℝ (k t) (r t))).trans hm
  simp only [Pi.mul_apply] at h
  rw [intervalIntegral.integral_mul_const] at h
  exact h.trans (mul_le_mul_of_nonneg_right hG hR)

end GNC.PolynomialNormIntegral
