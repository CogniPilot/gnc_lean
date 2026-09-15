import GNC.Analysis.ForcedResponse

/-! Two-time transition operators and the exact Duhamel formula (77)–(78)
for an arbitrary initial time, without a normalization assumption on Φ(0). -/
noncomputable section
open MeasureTheory
namespace GNC.ForcedResponse
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

def transition (Φ : ℝ → (End (V := V))ˣ) (t s : ℝ) : (End (V := V))ˣ := Φ t*(Φ s)⁻¹

@[simp] theorem transition_self (Φ : ℝ → (End (V := V))ˣ) (t : ℝ) : transition Φ t t = 1 := by
  simp [transition]

theorem transition_comp (Φ : ℝ → (End (V := V))ˣ) (t s r : ℝ) :
    transition Φ t s*transition Φ s r = transition Φ t r := by
  simp [transition, mul_assoc]

def responseFrom (Φ : ℝ → (End (V := V))ˣ) (u : ℝ → V) (t₀ : ℝ) (x₀ : V) (t : ℝ) : V :=
  (Φ t).val (((Φ t₀)⁻¹).val x₀+∫ s in t₀..t, integrand Φ u s)

def forcingFrom (Φ : ℝ → (End (V := V))ˣ) (u : ℝ → V) (t₀ t : ℝ) : V :=
  ∫ s in t₀..t, (transition Φ t s).val (u s)

theorem primitiveFrom_derivative (Φ : ℝ → (End (V := V))ˣ) (u : ℝ → V)
    (hc : Continuous (integrand Φ u)) (t₀ t : ℝ) :
    HasDerivAt (fun z => ∫ s in t₀..z, integrand Φ u s) (integrand Φ u t) t :=
  intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable t₀ t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

theorem responseFrom_derivative (Φ : ℝ → (End (V := V))ˣ) (A : ℝ → End (V := V))
    (hΦ : ∀ t, HasDerivAt (fun s => (Φ s).val) (A t*(Φ t).val) t)
    (u : ℝ → V) (hu : Continuous u) (t₀ : ℝ) (x₀ : V) (t : ℝ) :
    HasDerivAt (responseFrom Φ u t₀ x₀) (A t (responseFrom Φ u t₀ x₀ t)+u t) t := by
  have hp := (primitiveFrom_derivative Φ u (integrand_continuous Φ A hΦ u hu) t₀ t).const_add
    (((Φ t₀)⁻¹).val x₀)
  convert (hΦ t).clm_apply hp using 1
  simp only [responseFrom, integrand, ContinuousLinearMap.mul_apply, cancel]

@[simp] theorem responseFrom_initial (Φ : ℝ → (End (V := V))ˣ) (u : ℝ → V) (t₀ : ℝ) (x₀ : V) :
    responseFrom Φ u t₀ x₀ t₀ = x₀ := by simp [responseFrom, cancel]

/-- Equation (78), with the transition operator inside the actual integral. -/
theorem responseFrom_formula (Φ : ℝ → (End (V := V))ˣ) (A : ℝ → End (V := V))
    (hΦ : ∀ t, HasDerivAt (fun s => (Φ s).val) (A t*(Φ t).val) t)
    (u : ℝ → V) (hu : Continuous u) (t₀ : ℝ) (x₀ : V) (t : ℝ) :
    responseFrom Φ u t₀ x₀ t = (transition Φ t t₀).val x₀+forcingFrom Φ u t₀ t := by
  have hc : IntervalIntegrable (integrand Φ u) volume t₀ t :=
    (integrand_continuous Φ A hΦ u hu).intervalIntegrable t₀ t
  have h := (Φ t).val.intervalIntegral_comp_comm hc
  simp only [responseFrom, map_add]
  rw [← h]
  rfl

theorem responseFrom_unique (Φ : ℝ → (End (V := V))ˣ) (A : ℝ → End (V := V))
    (hΦ : ∀ t, HasDerivAt (fun s => (Φ s).val) (A t*(Φ t).val) t)
    (u : ℝ → V) (hu : Continuous u) (f : ℝ → V)
    (hf : ∀ t, HasDerivAt f (A t (f t)+u t) t) (t₀ : ℝ) :
    f = responseFrom Φ u t₀ (f t₀) := by
  let H : ℝ → V := fun t => ((Φ t)⁻¹).val (f t)-∫ s in t₀..t, integrand Φ u s
  have hd (t : ℝ) : HasDerivAt H 0 t := by
    have h1 := (inverse_derivative Φ A hΦ t).clm_apply (hf t)
    have h2 := primitiveFrom_derivative Φ u (integrand_continuous Φ A hΦ u hu) t₀ t
    convert h1.sub h2 using 1
    simp [integrand, ContinuousLinearMap.mul_apply, map_add]
  have hc (t : ℝ) : H t = ((Φ t₀)⁻¹).val (f t₀) := by
    have h := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
      (fun s => (hd s).deriv) t t₀
    simpa [H] using h
  funext t
  have hh := congrArg (fun v : V => (Φ t).val v) (hc t)
  dsimp [H] at hh
  rw [map_sub, cancel] at hh
  simp only [responseFrom, map_add]
  exact eq_add_of_sub_eq hh

@[simp] theorem matched_forcingFrom (Φ : ℝ → (End (V := V))ˣ) (t₀ t : ℝ) :
    forcingFrom Φ (fun _ => 0) t₀ t = 0 := by simp [forcingFrom]

end GNC.ForcedResponse
