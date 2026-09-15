import GNC.Analysis.DefectBound
import Mathlib.Analysis.ODE.Gronwall

/-! Coordinate-consistent comparison and differential-defect bounds for STMs.
These statements apply to any continuous linear evolution, including orbital
variational equations. A coordinate change by itself does not change the flow.
Numerical defect envelopes are hypotheses, not conclusions of sampled data. -/
noncomputable section
open Set MeasureTheory
namespace GNC.STMComparison
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
abbrev End := E →L[ℝ] E

omit [CompleteSpace E] in
/-- The time-dependent coordinate change includes its derivative. -/
theorem change_derivative (P C C' A B : ℝ → End (E := E)) (Q : End (E := E))
    (hP : ∀ t, HasDerivAt P (A t * P t) t)
    (hC : ∀ t, HasDerivAt C (C' t) t)
    (hAB : ∀ t, C' t + C t * A t = B t * C t) (t : ℝ) :
    HasDerivAt (fun s => C s * P s * Q) (B t * (C t * P t * Q)) t := by
  convert ((hC t).mul (hP t)).mul_const Q using 1
  have h := congrArg (fun F : End => F * P t * Q) (hAB t)
  simpa only [add_mul, mul_assoc] using h.symm

/-- Equal linear dynamics and initial matrices give equal transitions.
Together with `change_derivative`, this rules out a coordinate-only STM gain. -/
theorem equal_of_same_equation (Φ : ℝ → (End (E := E))ˣ) (A P : ℝ → End (E := E))
    (hΦ : ∀ t, HasDerivAt (fun s => (Φ s).val) (A t * (Φ t).val) t)
    (hP : ∀ t, HasDerivAt P (A t * P t) t) {a : ℝ} (hinit : P a = (Φ a).val) :
    P = fun t => (Φ t).val := by
  funext t
  ext v
  have hp (s : ℝ) : HasDerivAt (fun z => P z v) (A s (P s v) + 0) s := by
    simpa using (hP s).clm_apply (hasDerivAt_const s v)
  have hq (s : ℝ) : HasDerivAt (fun z => (Φ z).val v)
      (A s ((Φ s).val v) + 0) s := by
    simpa using (hΦ s).clm_apply (hasDerivAt_const s v)
  have p := ForcedResponse.responseFrom_unique Φ A hΦ (fun _ => 0) continuous_const _ hp a
  have q := ForcedResponse.responseFrom_unique Φ A hΦ (fun _ => 0) continuous_const _ hq a
  rw [hinit] at p
  exact congrFun (p.trans q.symm) t

/-- An operator-norm STM bound from the actual matrix differential defect.
The bound holds uniformly for every initial perturbation, not only a test orbit. -/
theorem defect_bound (Φ : ℝ → (End (E := E))ˣ) (A P D : ℝ → End (E := E))
    (hΦ : ∀ t, HasDerivAt (fun s => (Φ s).val) (A t * (Φ t).val) t)
    {a b δ gain : ℝ} (hab : a ≤ b) (hδ : 0 ≤ δ) (hg : 0 ≤ gain)
    (hD : Continuous D)
    (hP : ∀ t ∈ Icc a b, HasDerivAt P (A t * P t + D t) t)
    (hinit : P a = (Φ a).val)
    (hbound : ∀ t ∈ Icc a b, ‖D t‖ ≤ δ)
    (hgain : (∫ s in a..b, ‖DefectBound.kernel Φ b s‖) ≤ gain) :
    ‖P b - (Φ b).val‖ ≤ gain * δ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hg hδ)
  intro v
  have hx (t : ℝ) (_ : t ∈ Icc a b) : HasDerivAt (fun s => (Φ s).val v)
      (A t ((Φ t).val v) + 0) t := by
    simpa using (hΦ t).clm_apply (hasDerivAt_const t v)
  have hz (t : ℝ) (ht : t ∈ Icc a b) : HasDerivAt (fun s => P s v)
      (A t (P t v) + 0 + D t v) t := by
    simpa using (hP t ht).clm_apply (hasDerivAt_const t v)
  have hb (t : ℝ) (ht : t ∈ Icc a b) : ‖D t v‖ ≤ δ * ‖v‖ :=
    ((D t).le_opNorm v).trans (mul_le_mul_of_nonneg_right (hbound t ht) (norm_nonneg v))
  have h := DefectBound.error_bound Φ A hΦ (fun t => (Φ t).val v) (fun t => P t v)
    (fun _ => 0) (fun t => D t v) hab (hD.clm_apply continuous_const) hx hz
    (mul_nonneg hδ (norm_nonneg v)) hb hgain
  simpa [hinit, mul_assoc] using h

omit [CompleteSpace E] in
/-- A propagator for a different generator has this additional model defect. -/
theorem model_defect (P A B D : End (E := E)) :
    B * P + D - A * P = (B - A) * P + D := by
  noncomm_ring

omit [CompleteSpace E] in
/-- An explicit bound using only the generator and the candidate's defect.
It requires no estimate supplied for the unknown exact transition. -/
theorem defect_bound_of_generator_norm (A P Q D : ℝ → End (E := E))
    {a b L δ : ℝ}
    (hP : ∀ t ∈ Icc a b, HasDerivAt P (A t*P t+D t) t)
    (hQ : ∀ t ∈ Icc a b, HasDerivAt Q (A t*Q t) t)
    (hinit : P a = Q a)
    (hA : ∀ t ∈ Icc a b, ‖A t‖ ≤ L)
    (hD : ∀ t ∈ Icc a b, ‖D t‖ ≤ δ) :
    ∀ t ∈ Icc a b, ‖P t-Q t‖ ≤ gronwallBound 0 L δ (t-a) := by
  have hd (t : ℝ) (ht : t ∈ Icc a b) :
      HasDerivAt (fun s => P s-Q s) (A t*(P t-Q t)+D t) t := by
    convert (hP t ht).sub (hQ t ht) using 1
    noncomm_ring
  apply norm_le_gronwallBound_of_norm_deriv_right_le
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hd t ⟨ht.1,ht.2.le⟩).hasDerivWithinAt)
    (by simp [hinit])
  intro t ht
  have ht' : t ∈ Icc a b := ⟨ht.1,ht.2.le⟩
  exact (norm_add_le _ _).trans (add_le_add
    ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (hA t ht') (norm_nonneg _)))
    (hD t ht'))

theorem defect_gain_formula (L δ h : ℝ) :
    gronwallBound 0 L δ h =
      δ * (if L = 0 then h else (Real.exp (L*h)-1)/L) := by
  by_cases hL : L = 0
  · simp [hL, gronwallBound_K0]
  · rw [gronwallBound_of_K_ne_0 hL, if_neg hL]
    ring

end GNC.STMComparison
