import GNC.Analysis.ForcedResponse
import GNC.Control.QuadraticTube

/-! A non-iterative nonlinear tube about an actual LTV fundamental solution.
The nonlinear ODE, rather than a supplied response identity, is the input.
All bounds are over continuous time. The regional quadratic remainder is
used only inside radius `2*a`; the theorem proves that region is invariant
over the stated interval. Existence of the trajectory and fundamental
solution is explicit, not a numerical integration claim.
-/
noncomputable section
open Set MeasureTheory
namespace GNC.NearLinearTube
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
abbrev End := E →L[ℝ] E

def kernel (Φ : ℝ → (End (E := E))ˣ) (t s : ℝ) : End (E := E) :=
  (Φ t).val * ((Φ s)⁻¹).val

theorem kernel_continuous (Φ : ℝ → (End (E := E))ˣ) (A : ℝ → End (E := E))
    (hΦ : ∀ t, HasDerivAt (fun s => (Φ s).val) (A t*(Φ t).val) t) (t : ℝ) :
    Continuous (kernel Φ t) := by
  have hi : Continuous (fun s => ((Φ s)⁻¹).val) :=
    continuous_iff_continuousAt.mpr fun s =>
      (ForcedResponse.inverse_derivative Φ A hΦ s).continuousAt
  exact continuous_const.mul hi

theorem variation_of_constants (Φ : ℝ → (End (E := E))ˣ) (A : ℝ → End (E := E))
    (hΦ : ∀ t, HasDerivAt (fun s => (Φ s).val) (A t*(Φ t).val) t)
    (hΦ₀ : Φ 0 = 1) (x r : ℝ → E) (hr : Continuous r) {t : ℝ} (ht : 0 ≤ t)
    (hx : ∀ s ∈ Icc 0 t, HasDerivAt x (A s (x s)+r s) s) :
    x t = (Φ t).val (x 0)+∫ s in 0..t, kernel Φ t s (r s) := by
  have hc := ForcedResponse.integrand_continuous Φ A hΦ r hr
  have hd (s : ℝ) (hs : s ∈ Icc 0 t) :
      HasDerivAt (fun u => ((Φ u)⁻¹).val (x u))
        (ForcedResponse.integrand Φ r s) s := by
    convert (ForcedResponse.inverse_derivative Φ A hΦ s).clm_apply (hx s hs) using 1
    simp [ForcedResponse.integrand, ContinuousLinearMap.mul_apply, map_add]
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => hd s (by simpa [uIcc_of_le ht] using hs))
    (hc.intervalIntegrable (μ := volume) 0 t)
  have he := congrArg (fun z => (Φ t).val z) hi
  simp only [map_sub, ForcedResponse.cancel, hΦ₀] at he
  have hm := (Φ t).val.intervalIntegral_comp_comm (hc.intervalIntegrable (μ := volume) 0 t)
  change (∫ s in 0..t, kernel Φ t s (r s)) = _ at hm
  rw [← hm] at he
  simpa [add_comm] using (sub_eq_iff_eq_add.mp he.symm)

/-- A checked quadratic closure gives both the total radius and the
prediction error. The reference transport is never replaced by exp(Kt). -/
theorem certificate (Φ : ℝ → (End (E := E))ˣ) (A : ℝ → End (E := E))
    (hΦ : ∀ t, HasDerivAt (fun s => (Φ s).val) (A t*(Φ t).val) t)
    (hΦ₀ : Φ 0 = 1) (x r : ℝ → E) (c : ℝ → ℝ) {T a b : ℝ}
    (hT : 0 ≤ T) (ha : 0 < a) (hb : 0 ≤ b) (hsmall : 4*a*b < 1)
    (hx : Continuous x) (hr : Continuous r) (hc : Continuous c)
    (hode : ∀ t ∈ Icc 0 T, HasDerivAt x (A t (x t)+r t) t)
    (hc0 : ∀ t ∈ Icc 0 T, 0 ≤ c t)
    (hi : ‖x 0‖ ≤ a) (hlin : ∀ t ∈ Icc 0 T, ‖(Φ t).val (x 0)‖ ≤ a)
    (hrem : ∀ t ∈ Icc 0 T, ‖x t‖ ≤ 2*a → ‖r t‖ ≤ c t*‖x t‖^2)
    (hgain : ∀ t ∈ Icc 0 T, (∫ s in 0..t, ‖kernel Φ t s‖*c s) ≤ b) :
    ∀ t ∈ Icc 0 T, ‖x t‖ ≤ QuadraticTube.radius a b ∧
      ‖x t-(Φ t).val (x 0)‖ ≤ b*(QuadraticTube.radius a b)^2 := by
  have hid (t : ℝ) (ht : t ∈ Icc 0 T) := variation_of_constants Φ A hΦ hΦ₀
    x r hr ht.1 (fun s hs => hode s ⟨hs.1, hs.2.trans ht.2⟩)
  have hk := kernel_continuous Φ A hΦ
  have hbnd := QuadraticTube.from_response x (fun t => (Φ t).val (x 0)) r
    (kernel Φ) c hT ha hb hsmall hx hr hc (fun t _ => hk t) hc0 hi hlin hid hrem hgain
  have hrad := QuadraticTube.radius_properties ha hb hsmall
  intro t ht
  refine ⟨hbnd t ht, ?_⟩
  have hw := QuadraticTube.weighted_response (kernel Φ t) r c ht.1 (hk t) hr hc
    (fun s hs => hc0 s ⟨hs.1, hs.2.trans ht.2⟩) (fun s hs => by
      have hsT : s ∈ Icc 0 T := ⟨hs.1, hs.2.trans ht.2⟩
      exact (hrem s hsT ((hbnd s hsT).trans hrad.2.1.le)).trans
        (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _) (hbnd s hsT) 2) (hc0 s hsT))) (hgain t ht)
  rw [hid t ht, add_sub_cancel_left]
  exact hw

end GNC.NearLinearTube
