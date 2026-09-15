import GNC.Analysis.SecondOrderCertificate
import GNC.Dynamics.GravityLipschitz

/-! A candidate-centered certificate for the complete inverse-square field.
The gain, forcing profile and scalar supersolutions are parameters, not
benchmark constants. Time is normalized to `[0,1]`; `scale` is the square
of the physical duration. Velocity in the conclusion is differentiated
with respect to normalized time. -/
noncomputable section
namespace GNC.Gravity
open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E]

/-- A complete physical residual, a radius check and a scalar comparison
certificate bound any supplied orbital solution. The first-exit proof
establishes the region; no a priori actual-orbit tube is assumed. -/
theorem prediction_certificate (μ scale : ℝ) (hμ : 0 ≤ μ) (hscale : 0 ≤ scale)
    (x velocity q qv qa thrust : ℝ → E) (f P V W b bv bw : ℝ → ℝ)
    {κ B BV F r M : ℝ} (hκ : 0 ≤ κ) (hB : 0 ≤ B) (hBV : 0 ≤ BV)
    (hF : 0 ≤ F) (hr : 0 < r) (hclose : B*F < M)
    (hlip : scale*(2*μ/r^3) ≤ κ)
    (hq : ∀ t ∈ Icc (0:ℝ) 1, r+M ≤ ‖q t‖)
    (hx : Continuous x) (hv : Continuous velocity)
    (hcq : Continuous q) (hcqv : Continuous qv)
    (hdx : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt x (velocity t) t)
    (hdv : ∀ t ∈ Icc (0:ℝ) 1,
      HasDerivAt velocity (scale • (field μ (x t)+thrust t)) t)
    (hdq : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt q (qv t) t)
    (hdqv : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt qv (qa t) t)
    (hP : ∀ t, HasDerivAt P (V t) t) (hV : ∀ t, HasDerivAt V (W t) t)
    (hb : ∀ t, HasDerivAt b (bv t) t) (hbv : ∀ t, HasDerivAt bv (bw t) t)
    (hip : x 0 = q 0) (hiv : velocity 0 = qv 0)
    (hiP : P 0 = 0) (hiV : V 0 = 0) (hib : b 0 = 0) (hibv : bv 0 = 0)
    (hshape : ∀ t ∈ Icc (0:ℝ) 1, κ*b t+1 ≤ bw t)
    (hbounds : ∀ t ∈ Icc (0:ℝ) 1, b t ≤ B ∧ bv t ≤ BV)
    (hforcing : ∀ t ∈ Icc (0:ℝ) 1, f t ≤ F)
    (hsuper : ∀ t ∈ Icc (0:ℝ) 1, κ*P t+f t ≤ W t)
    (hdefect : ∀ t ∈ Icc (0:ℝ) 1,
      ‖scale • (field μ (q t)+thrust t)-qa t‖ ≤ f t) :
    ∀ t ∈ Icc (0:ℝ) 1, ‖x t-q t‖ ≤ P t ∧ ‖velocity t-qv t‖ ≤ V t := by
  have hMn : 0 ≤ M := ((mul_nonneg hB hF).trans_lt hclose).le
  apply SecondOrderCertificate.regional_response
    (fun t => x t-q t) (fun t => velocity t-qv t)
    (fun t => scale • (field μ (x t)+thrust t)-qa t)
    f P V W b bv bw hκ hB hBV hF hclose
    (hx.sub hcq) (hv.sub hcqv)
    (fun t ht => (hdx t ht).sub (hdq t ht))
    (fun t ht => (hdv t ht).sub (hdqv t ht)) hP hV hb hbv
    (by simp [hip]) (by simp [hiv]) hiP hiV hib hibv hshape hbounds hforcing hsuper
  intro t ht hreg
  have hg := field_difference_ball μ hμ (q t) (x t-q t) 0 hr (hq t ht)
    hreg (by simpa using hMn)
  simp only [add_sub_cancel,add_zero,sub_zero] at hg
  have hs : ‖scale • (field μ (x t)-field μ (q t))‖ ≤ κ*‖x t-q t‖ := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hscale]
    exact (mul_le_mul_of_nonneg_left hg hscale).trans (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hlip (norm_nonneg _))
  have he : scale • (field μ (x t)+thrust t)-qa t =
      scale • (field μ (x t)-field μ (q t))+
      (scale • (field μ (q t)+thrust t)-qa t) := by module
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add hs (hdefect t ht))

end GNC.Gravity
