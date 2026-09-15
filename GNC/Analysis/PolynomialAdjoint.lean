import GNC.Analysis.PolynomialDifferential
import GNC.Analysis.ParametricBox
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Directional endpoint certificates with a computed, inexact adjoint.

Both a conventional time/parameter polynomial and a retained-rotation
polynomial can use this checker. It recomputes the primal and adjoint defects
against the full field and bounds the nonlinear remainder on an independently
certified tube. An approximate STM/adjoint is never assumed exact.
-/
namespace GNC.ParametricBox
open PolynomialODE Matrix Set MeasureTheory
variable {C : Type} {n : ℕ} (A : Model C)

def sumVector : {m : ℕ} → (Fin m → C) → C
  | 0, _ => A.constant 0
  | m+1, p => A.add (p 0) (sumVector (fun i : Fin m => p i.succ))

theorem value_sumVector {m : ℕ} (p : Fin m → C) (t θ : ℝ) :
    A.value (sumVector A p) t θ = ∑ i, A.value (p i) t θ := by
  induction m with
  | zero => simp [sumVector, A.value_constant]
  | succ m ih => simp [sumVector, A.value_add, ih, Fin.sum_univ_succ]

def adjointResidual (f : Fin n → Expr n) (q ell : Fin n → C) (i : Fin n) : C :=
  A.add (A.derivative (ell i))
    (sumVector A (fun j => A.multiply (ell j) (substitute A ((f j).partialDerivative i) q)))

def pairedResidual (f : Fin n → Expr n) (q ell : Fin n → C) : C :=
  sumVector A (fun i => A.multiply (ell i) (residual A f q i))

/-- Three computed charges: adjoint defect times the tube, the paired primal
defect, and the full nonlinear quadratic remainder. -/
def adjointCharge (f : Fin n → Expr n) (q ell : Fin n → C)
    (M E : Fin n → ℚ) (h a : ℚ) : ℚ :=
  (∑ i, A.bound (adjointResidual A f q ell i) h a * E i) +
    A.bound (pairedResidual A f q ell) h a +
    ∑ i, A.bound (ell i) h a * (f i).remainderMajorant M E

noncomputable section

theorem adjointResidual_value (f : Fin n → Expr n) (q ell : Fin n → C)
    (i : Fin n) (t θ : ℝ) :
    A.value (adjointResidual A f q ell i) t θ =
      A.value (A.derivative (ell i)) t θ +
        ∑ j, A.value (ell j) t θ * ((f j).partialDerivative i).value (curve A q θ t) := by
  simp only [adjointResidual, A.value_add, value_sumVector, A.value_multiply, substitute_value]

theorem pairedResidual_value (f : Fin n → Expr n) (q ell : Fin n → C) (t θ : ℝ) :
    A.value (pairedResidual A f q ell) t θ =
      ∑ i, A.value (ell i) t θ *
        ((f i).value (curve A q θ t)-A.value (A.derivative (q i)) t θ) := by
  simp only [pairedResidual, value_sumVector, A.value_multiply, residual_value]

/-- Exact algebra before any enclosure: all retained linearized dynamics
cancel into the computed adjoint defect. No commutation hypothesis is used. -/
theorem adjoint_algebra (f : Fin n → Expr n) (x q v ell dell w : Fin n → ℝ) :
    (∑ i, (dell i*(x i-q i)+ell i*((f i).value x+w i-v i))) =
      (∑ i, ell i*w i) +
      (∑ i, (dell i+∑ j, ell j*((f j).partialDerivative i).value q)*(x i-q i)) +
      (∑ i, ell i*((f i).value q-v i)) + ∑ i, ell i*(f i).remainder x q := by
  have hl : (∑ j, ell j*(f j).linearization q (x-q)) =
      ∑ i, (∑ j, ell j*((f j).partialDerivative i).value q)*(x i-q i) := by
    simp only [Expr.linearization_eq_sum, Finset.mul_sum, Finset.sum_mul,
      Pi.sub_apply, ← mul_assoc]
    exact Finset.sum_comm
  calc
    _ = (∑ i, ell i*w i) + (∑ i, dell i*(x i-q i)) +
        (∑ i, ell i*(f i).linearization q (x-q)) +
        (∑ i, ell i*((f i).value q-v i)) + ∑ i, ell i*(f i).remainder x q := by
      simp only [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      simp only [Expr.remainder]
      ring
    _ = _ := by rw [hl]; simp only [add_mul, Finset.sum_add_distrib]; ring

/-- The actual scalar derivative includes the input pairing and all three
defects. The candidate and adjoint can be independently generated. -/
theorem computed_adjoint_derivative (f : Fin n → Expr n) (q ell : Fin n → C)
    (θ : ℝ) {x : ℝ → Fin n → ℝ} {w : Fin n → ℝ} {t : ℝ}
    (hx : HasDerivAt x (fun i => (f i).value (x t)+w i) t) :
    HasDerivAt (fun s => ∑ i, A.value (ell i) s θ*(x s i-A.value (q i) s θ))
      ((∑ i, A.value (ell i) t θ*w i) +
       (∑ i, A.value (adjointResidual A f q ell i) t θ*(x t i-A.value (q i) t θ)) +
       A.value (pairedResidual A f q ell) t θ +
       ∑ i, A.value (ell i) t θ*(f i).remainder (x t) (curve A q θ t)) t := by
  have hd := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    (A.value_derivative (ell i) t θ).mul
      ((hasDerivAt_pi.mp hx i).sub (A.value_derivative (q i) t θ)))
  convert hd using 1
  simp only [adjointResidual_value, pairedResidual_value]
  exact (adjoint_algebra f (x t) (curve A q θ t)
    (curve A (fun i => A.derivative (q i)) θ t) (curve A ell θ t)
    (curve A (fun i => A.derivative (ell i)) θ t) w).symm

/-- A computable residual budget on a certified regional tube. It bounds
the numerical-response defect separately from the physical input support. -/
theorem adjointCharge_bound (f : Fin n → Expr n) (q ell : Fin n → C)
    {M E : Fin n → ℚ} {h a : ℚ} {t θ : ℝ}
    (hM : ∀ i, 0 ≤ M i) (hE : ∀ i, 0 ≤ E i)
    (ht : |t| ≤ (h : ℝ)) (hθ : |θ| ≤ (a : ℝ)) (x : Fin n → ℝ)
    (hx : ∀ i, |x i| ≤ (M i : ℝ))
    (hq : ∀ i, |A.value (q i) t θ| ≤ (M i : ℝ))
    (he : ∀ i, |x i-A.value (q i) t θ| ≤ (E i : ℝ)) :
    |(∑ i, A.value (adjointResidual A f q ell i) t θ*(x i-A.value (q i) t θ)) +
      A.value (pairedResidual A f q ell) t θ +
      ∑ i, A.value (ell i) t θ*(f i).remainder x (curve A q θ t)| ≤
        (adjointCharge A f q ell M E h a : ℝ) := by
  have hb₁ : |∑ i, A.value (adjointResidual A f q ell i) t θ*(x i-A.value (q i) t θ)| ≤
      ((∑ i, A.bound (adjointResidual A f q ell i) h a * E i : ℚ) : ℝ) := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    push_cast
    apply Finset.sum_le_sum
    intro i _
    rw [abs_mul]
    have hb := A.bound_sound (adjointResidual A f q ell i) ht hθ
    exact mul_le_mul hb (he i) (abs_nonneg _) ((abs_nonneg _).trans hb)
  have hb₂ := A.bound_sound (pairedResidual A f q ell) ht hθ
  have hb₃ : |∑ i, A.value (ell i) t θ*(f i).remainder x (curve A q θ t)| ≤
      ((∑ i, A.bound (ell i) h a*(f i).remainderMajorant M E : ℚ) : ℝ) := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    push_cast
    apply Finset.sum_le_sum
    intro i _
    rw [abs_mul]
    have hb := A.bound_sound (ell i) ht hθ
    exact mul_le_mul hb ((f i).remainder_bound hM hE x (curve A q θ t) hx hq he)
      (abs_nonneg _) ((abs_nonneg _).trans hb)
  exact ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans
    (by simpa only [adjointCharge, Rat.cast_add] using add_le_add (add_le_add hb₁ hb₂) hb₃)

/-- A scalar upper certificate for every admissible input history. The
polynomial potential integrates a directional support bound. It may vary
within the arc; the numerical adjoint error is charged explicitly. Applying
the theorem to an opposite terminal row supplies the lower endpoint bound. -/
theorem computed_endpoint_bound (f : Fin n → Expr n) (q ell : Fin n → C)
    (potential : C) {M E : Fin n → ℚ} {h a : ℚ} {θ : ℝ}
    (hh : 0 ≤ h) (hM : ∀ i, 0 ≤ M i) (hE : ∀ i, 0 ≤ E i)
    (hθ : |θ| ≤ (a : ℝ)) (x w : ℝ → Fin n → ℝ) (hxc : Continuous x)
    (hx : ∀ t ∈ Icc (0 : ℝ) h, HasDerivAt x (fun i => (f i).value (x t)+w t i) t)
    (hregion : ∀ t ∈ Icc (0 : ℝ) h, ∀ i, |x t i| ≤ (M i : ℝ))
    (hq : ∀ t ∈ Icc (0 : ℝ) h, ∀ i, |A.value (q i) t θ| ≤ (M i : ℝ))
    (he : ∀ t ∈ Icc (0 : ℝ) h, ∀ i, |x t i-A.value (q i) t θ| ≤ (E i : ℝ))
    (hsupply : ∀ t ∈ Icc (0 : ℝ) h,
      (∑ i, A.value (ell i) t θ*w t i) ≤ A.value (A.derivative potential) t θ) :
    (∑ i, A.value (ell i) h θ*(x h i-A.value (q i) h θ)) ≤
      (∑ i, A.value (ell i) 0 θ*(x 0 i-A.value (q i) 0 θ)) +
      (A.value potential h θ-A.value potential 0 θ) +
      (h : ℝ)*adjointCharge A f q ell M E h a := by
  let F := fun t => ∑ i, A.value (ell i) t θ*(x t i-A.value (q i) t θ)
  let charge : ℝ := adjointCharge A f q ell M E h a
  let B := fun t => F 0+(A.value potential t θ-A.value potential 0 θ)+t*charge
  have hc (p : C) : Continuous (fun t => A.value p t θ) :=
    continuous_iff_continuousAt.mpr (fun t => (A.value_derivative p t θ).continuousAt)
  have hFc : Continuous F := continuous_finset_sum _ (fun i _ =>
    (hc (ell i)).mul (((continuous_apply i).comp hxc).sub (hc (q i))))
  have hBc : Continuous B :=
    (continuous_const.add ((hc potential).sub continuous_const)).add (continuous_id.mul_const charge)
  apply image_le_of_deriv_right_le_deriv_boundary hFc.continuousOn
    (fun t ht => (computed_adjoint_derivative A f q ell θ (hx t (Ico_subset_Icc_self ht))).hasDerivWithinAt)
    (B := B) (B' := fun t => A.value (A.derivative potential) t θ+charge)
    (by simp [B]) hBc.continuousOn
    (fun t _ => by
      convert ((hasDerivAt_const t (F 0)).add
        ((A.value_derivative potential t θ).sub_const _)).add
        ((hasDerivAt_id t).mul_const charge) |>.hasDerivWithinAt using 1 <;> simp [B])
    (fun t ht => by
      have ht' := Ico_subset_Icc_self ht
      have hr := adjointCharge_bound A f q ell hM hE
        (show |t| ≤ (h : ℝ) by rw [abs_of_nonneg ht.1]; exact ht.2.le) hθ
        (x t) (hregion t ht') (hq t ht') (he t ht')
      have hb := (le_abs_self _).trans hr
      have hs := hsupply t ht'
      dsimp [charge] at *
      linarith)
    (right_mem_Icc.mpr (by exact_mod_cast hh))

/-- Symmetric version with a scalar directional input bound on one arc.
Subdivision may be used to keep that bound sharp. The state tube is an
independent prerequisite, never inferred from this output-only estimate. -/
theorem computed_endpoint_abs_bound (f : Fin n → Expr n) (q ell : Fin n → C)
    {M E : Fin n → ℚ} {h a : ℚ} {θ input : ℝ}
    (hh : 0 ≤ h) (hM : ∀ i, 0 ≤ M i) (hE : ∀ i, 0 ≤ E i)
    (hθ : |θ| ≤ (a : ℝ)) (x w : ℝ → Fin n → ℝ)
    (hx : ∀ t ∈ Icc (0 : ℝ) h, HasDerivAt x (fun i => (f i).value (x t)+w t i) t)
    (hregion : ∀ t ∈ Icc (0 : ℝ) h, ∀ i, |x t i| ≤ (M i : ℝ))
    (hq : ∀ t ∈ Icc (0 : ℝ) h, ∀ i, |A.value (q i) t θ| ≤ (M i : ℝ))
    (he : ∀ t ∈ Icc (0 : ℝ) h, ∀ i, |x t i-A.value (q i) t θ| ≤ (E i : ℝ))
    (hsupply : ∀ t ∈ Icc (0 : ℝ) h, |∑ i, A.value (ell i) t θ*w t i| ≤ input) :
    |(∑ i, A.value (ell i) h θ*(x h i-A.value (q i) h θ)) -
      ∑ i, A.value (ell i) 0 θ*(x 0 i-A.value (q i) 0 θ)| ≤
      (h : ℝ)*(input+adjointCharge A f q ell M E h a) := by
  have hd := fun t ht => computed_adjoint_derivative A f q ell θ (hx t ht)
  have hb := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun t ht => (hd t ht).hasDerivWithinAt)
    (C := input+adjointCharge A f q ell M E h a)
    (fun t ht => by
      have ht' := Ico_subset_Icc_self ht
      have hr := adjointCharge_bound A f q ell hM hE
        (show |t| ≤ (h : ℝ) by rw [abs_of_nonneg ht.1]; exact ht.2.le) hθ
        (x t) (hregion t ht') (hq t ht') (he t ht')
      rw [Real.norm_eq_abs]
      simpa only [add_assoc] using
        (abs_add_le _ _).trans (add_le_add (hsupply t ht') hr))
    (h : ℝ) (right_mem_Icc.mpr (by exact_mod_cast hh))
  simpa only [sub_zero, Real.norm_eq_abs, mul_comm] using hb

end
end GNC.ParametricBox
