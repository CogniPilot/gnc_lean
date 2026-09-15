import GNC.Dynamics.GravityPairedError
import GNC.Applications.OrbitalComparison.RegionalPrediction

/-! Certifying relative orbit prediction without adding two absolute error
radii. The differential defect is formed after subtracting the nominal.
Shared nominal prediction error is charged through the gravity Hessian times
relative displacement. A first-exit argument closes the region without
iteration, just as for the absolute candidate certificate.
-/
noncomputable section
open Set
namespace GNC.OrbitalComparison
open Planning.PolynomialKernel PolynomialOrder
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `q` predicts the nominal, while `d` predicts the relative displacement.
The nominal prediction needs only its independently established radius `N`.
The forcing envelope contains the *relative* defect and the mixed nominal
error term; it does not add the nominal's absolute endpoint error twice. -/
theorem paired_orbital_prediction (μ scale : ℝ) (hμ : 0 ≤ μ) (hscale : 0 ≤ scale)
    (x vx x₀ vx₀ q d dv da thrust thrust₀ : ℝ → E) (f envelope : List ℚ)
    (henv : PolynomialEnvelope.Valid f envelope) (hf : nonnegative f)
    {r D N M : ℝ} (hr : 0 < r)
    (hclose : shape 1*((evaluate f 1:ℚ):ℝ) < M)
    (hlip : scale*(2*μ/r^3) ≤ 17/20)
    (hq : ∀ t ∈ Icc (0:ℝ) 1, r+D+N+M ≤ ‖q t‖)
    (hd : ∀ t ∈ Icc (0:ℝ) 1, ‖d t‖ ≤ D)
    (hn : ∀ t ∈ Icc (0:ℝ) 1, ‖x₀ t-q t‖ ≤ N)
    (hx : Continuous x) (hvx : Continuous vx)
    (hx₀ : Continuous x₀) (hvx₀ : Continuous vx₀)
    (hcd : Continuous d) (hcdv : Continuous dv)
    (hdx : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt x (vx t) t)
    (hdvx : ∀ t ∈ Icc (0:ℝ) 1,
      HasDerivAt vx (scale • (Gravity.field μ (x t)+thrust t)) t)
    (hdx₀ : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt x₀ (vx₀ t) t)
    (hdvx₀ : ∀ t ∈ Icc (0:ℝ) 1,
      HasDerivAt vx₀ (scale • (Gravity.field μ (x₀ t)+thrust₀ t)) t)
    (hdd : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt d (dv t) t)
    (hddv : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt dv (da t) t)
    (hip : x 0-x₀ 0 = d 0) (hiv : vx 0-vx₀ 0 = dv 0)
    (hforcing : ∀ t ∈ Icc (0:ℝ) 1,
      ‖scale • (Gravity.field μ (q t+d t)-Gravity.field μ (q t)+thrust t-thrust₀ t)-da t‖+
        scale*(6*μ/r^4)*‖d t‖*‖x₀ t-q t‖ ≤ value f t) :
    ∀ t ∈ Icc (0:ℝ) 1,
      ‖(x t-x₀ t)-d t‖ ≤ ((evaluate envelope 1:ℚ):ℝ) ∧
      ‖(vx t-vx₀ t)-dv t‖ ≤ ((evaluate (differentiate envelope) 1:ℚ):ℝ) := by
  apply regional_weighted_response (fun t => (x t-x₀ t)-d t)
    (fun t => (vx t-vx₀ t)-dv t)
    (fun t => (scale • (Gravity.field μ (x t)+thrust t)-
      scale • (Gravity.field μ (x₀ t)+thrust₀ t))-da t)
    f envelope henv hf hclose ((hx.sub hx₀).sub hcd) ((hvx.sub hvx₀).sub hcdv)
    (fun t ht => ((hdx t ht).sub (hdx₀ t ht)).sub (hdd t ht))
    (fun t ht => ((hdvx t ht).sub (hdvx₀ t ht)).sub (hddv t ht))
    (by simp [hip]) (by simp [hiv])
  intro t ht hregion
  have hg := Gravity.paired_field_error μ hμ (q t) (d t) (x₀ t-q t)
    ((x t-x₀ t)-d t) hr (hq t ht) (hd t ht) (hn t ht) hregion
  have heq : q t+d t+(x₀ t-q t)+((x t-x₀ t)-d t) = x t := by abel
  rw [heq,add_sub_cancel] at hg
  have hs := mul_le_mul_of_nonneg_left hg hscale
  have hlin := mul_le_mul_of_nonneg_right hlip (norm_nonneg ((x t-x₀ t)-d t))
  have hscaled : ‖scale • ((Gravity.field μ (x t)-Gravity.field μ (x₀ t))-
      (Gravity.field μ (q t+d t)-Gravity.field μ (q t)))‖ ≤
      (17/20)*‖(x t-x₀ t)-d t‖+scale*(6*μ/r^4)*‖d t‖*‖x₀ t-q t‖ := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hscale]
    calc
      _ ≤ _ := hs
      _ = (scale*(2*μ/r^3))*‖(x t-x₀ t)-d t‖+
          scale*(6*μ/r^4)*‖d t‖*‖x₀ t-q t‖ := by ring
      _ ≤ _ := add_le_add hlin le_rfl
  have hid : (scale • (Gravity.field μ (x t)+thrust t)-
      scale • (Gravity.field μ (x₀ t)+thrust₀ t))-da t =
      scale • ((Gravity.field μ (x t)-Gravity.field μ (x₀ t))-
        (Gravity.field μ (q t+d t)-Gravity.field μ (q t)))+
      (scale • (Gravity.field μ (q t+d t)-Gravity.field μ (q t)+thrust t-thrust₀ t)-da t) := by
    module
  rw [hid]
  have hb := (norm_add_le _ (scale • (Gravity.field μ (q t+d t)-
    Gravity.field μ (q t)+thrust t-thrust₀ t)-da t)).trans (add_le_add hscaled le_rfl)
  linarith [hforcing t ht]

end GNC.OrbitalComparison
