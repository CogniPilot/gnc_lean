import GNC.Control.Planner
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Variation of constants and uniqueness for the forced LTV equation.
An invertible fundamental solution is supplied with its defining ODE; the
forced response is derived from it rather than postulated as affine data. -/
noncomputable section
open MeasureTheory
namespace GNC.ForcedResponse
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

abbrev End := V →L[ℝ] V

theorem inverse_derivative (Φ : ℝ → (End (V := V))ˣ) (A : ℝ → End (V := V))
    (hΦ : ∀ t, HasDerivAt (fun s => (Φ s).val) (A t*(Φ t).val) t) (t : ℝ) :
    HasDerivAt (fun s => ((Φ s)⁻¹).val) (-((Φ t)⁻¹).val*A t) t := by
  have h := (hasFDerivAt_ringInverse (𝕜 := ℝ) (Φ t)).comp_hasDerivAt t (hΦ t)
  change HasDerivAt (fun s => Ring.inverse (Φ s).val) _ t at h
  simp only [Ring.inverse_unit] at h
  convert h using 1
  change _ = -((Φ t)⁻¹).val*(A t*(Φ t).val)*((Φ t)⁻¹).val
  rw [mul_assoc, mul_assoc, Units.mul_inv, mul_one]

theorem cancel (U : (End (V := V))ˣ) (v : V) : U.val ((U⁻¹).val v) = v := by
  exact congrArg (fun F : End => F v) U.val_inv

theorem cancel' (U : (End (V := V))ˣ) (v : V) : (U⁻¹).val (U.val v) = v := by
  exact congrArg (fun F : End => F v) U.inv_val

def integrand (Φ : ℝ → (End (V := V))ˣ) (u : ℝ → V) (s : ℝ) : V := ((Φ s)⁻¹).val (u s)

def response (Φ : ℝ → (End (V := V))ˣ) (u : ℝ → V) (x₀ : V) (t : ℝ) : V :=
  (Φ t).val (x₀+∫ s in (0:ℝ)..t, integrand Φ u s)

theorem integrand_continuous (Φ : ℝ → (End (V := V))ˣ) (A : ℝ → End (V := V))
    (hΦ : ∀ t, HasDerivAt (fun s => (Φ s).val) (A t*(Φ t).val) t)
    (u : ℝ → V) (hu : Continuous u) : Continuous (integrand Φ u) := by
  have hi : Continuous (fun s => ((Φ s)⁻¹).val) := continuous_iff_continuousAt.mpr
    (fun t => (inverse_derivative Φ A hΦ t).continuousAt)
  exact hi.clm_apply hu

theorem primitive_derivative (Φ : ℝ → (End (V := V))ˣ) (u : ℝ → V)
    (hc : Continuous (integrand Φ u)) (t : ℝ) :
    HasDerivAt (fun z => ∫ s in (0:ℝ)..z, integrand Φ u s) (integrand Φ u t) t :=
  intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

/-- Equations (77)–(78): the integral response solves the forced equation. -/
theorem response_derivative (Φ : ℝ → (End (V := V))ˣ) (A : ℝ → End (V := V))
    (hΦ : ∀ t, HasDerivAt (fun s => (Φ s).val) (A t*(Φ t).val) t)
    (u : ℝ → V) (hu : Continuous u) (x₀ : V) (t : ℝ) :
    HasDerivAt (response Φ u x₀) (A t (response Φ u x₀ t)+u t) t := by
  have hp := (primitive_derivative Φ u (integrand_continuous Φ A hΦ u hu) t).const_add x₀
  convert (hΦ t).clm_apply hp using 1
  simp only [response, integrand, ContinuousLinearMap.mul_apply, cancel]

theorem response_initial (Φ : ℝ → (End (V := V))ˣ) (h₀ : Φ 0 = 1) (u : ℝ → V) (x₀ : V) :
    response Φ u x₀ 0 = x₀ := by simp [response, h₀]

/-- Every differentiable solution equals the integral response. -/
theorem response_unique (Φ : ℝ → (End (V := V))ˣ) (A : ℝ → End (V := V))
    (hΦ : ∀ t, HasDerivAt (fun s => (Φ s).val) (A t*(Φ t).val) t)
    (h₀ : Φ 0 = 1) (u : ℝ → V) (hu : Continuous u) (f : ℝ → V)
    (hf : ∀ t, HasDerivAt f (A t (f t)+u t) t) :
    f = response Φ u (f 0) := by
  let H : ℝ → V := fun t => ((Φ t)⁻¹).val (f t)-∫ s in (0:ℝ)..t, integrand Φ u s
  have hd (t : ℝ) : HasDerivAt H 0 t := by
    have h1 := (inverse_derivative Φ A hΦ t).clm_apply (hf t)
    have h2 := primitive_derivative Φ u (integrand_continuous Φ A hΦ u hu) t
    convert h1.sub h2 using 1
    simp [integrand, ContinuousLinearMap.mul_apply, map_add]
  have hc (t : ℝ) : H t = f 0 := by
    have h := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
      (fun s => (hd s).deriv) t 0
    simpa [H, h₀] using h
  funext t
  have hh := congrArg (fun v : V => (Φ t).val v) (hc t)
  dsimp [H] at hh
  rw [map_sub, cancel] at hh
  simp only [response, map_add]
  exact eq_add_of_sub_eq hh

/-- The unique ODE solution is affine in its initial condition. -/
theorem response_affine (Φ : ℝ → (End (V := V))ˣ) (u : ℝ → V) (x₀ : V) (t : ℝ) :
    response Φ u x₀ t = (Φ t).val x₀+response Φ u 0 t := by simp [response, map_add]

theorem matched_forcing (Φ : ℝ → (End (V := V))ˣ) (x₀ : V) (t : ℝ) :
    response Φ (fun _ => 0) x₀ t = (Φ t).val x₀ := by simp [response, integrand]

end GNC.ForcedResponse
