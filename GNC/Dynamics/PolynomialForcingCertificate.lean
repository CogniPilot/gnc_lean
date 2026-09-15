import GNC.Dynamics.PolynomialOrbitCertificate
import GNC.Analysis.PolynomialForcing

/-! Complete inverse-square physical certificates retaining a polynomial
forcing profile. Region closure uses a coarse supersolution; the reported
error uses the checked time-dependent envelope. No physical tube is assumed. -/
noncomputable section
namespace GNC.Gravity
open Set Planning.PolynomialKernel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem polynomial_prediction_curve (μ scale : ℝ) (hμ : 0≤μ) (hscale : 0≤scale)
    (x xv q qv qa thrust : ℝ → E) {κ : ℚ} (f p : List ℚ)
    (hp : PolynomialForcing.Valid κ f p) (hκ : 0≤κ) (hk : κ<56) {r M : ℝ}
    (hr : 0<r)
    (hclose : PolynomialOrder.value f 1*PolynomialSupersolution.value (κ:ℝ) 1<M)
    (hlip : scale*(2*μ/r^3)≤(κ:ℝ))
    (hq : ∀ t ∈ Icc (0:ℝ) 1, r+M≤‖q t‖)
    (hx : Continuous x) (hv : Continuous xv) (hcq : Continuous q) (hcqv : Continuous qv)
    (hdx : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt x (xv t) t)
    (hdv : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt xv (scale • (field μ (x t)+thrust t)) t)
    (hdq : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt q (qv t) t)
    (hdqv : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt qv (qa t) t)
    (hip : x 0=q 0) (hiv : xv 0=qv 0)
    (hdefect : ∀ t ∈ Icc (0:ℝ) 1,
      ‖scale • (field μ (q t)+thrust t)-qa t‖≤PolynomialOrder.value f t) :
    ∀ t ∈ Icc (0:ℝ) 1, ‖x t-q t‖≤PolynomialOrder.value p t ∧
      ‖xv t-qv t‖≤PolynomialOrder.value (differentiate p) t := by
  have hκR : (0:ℝ)≤κ := by exact_mod_cast hκ
  have hkR : (κ:ℝ)<56 := by exact_mod_cast hk
  have hb := PolynomialSupersolution.bounds hκR hkR (show (1:ℝ) ∈ Icc 0 1 by norm_num)
  have hi := PolynomialSupersolution.initial (κ:ℝ)
  have hipoly := PolynomialForcing.initial κ f p hp
  exact prediction_certificate μ scale hμ hscale x xv q qv qa thrust
    (PolynomialOrder.value f) (PolynomialOrder.value p)
    (PolynomialOrder.value (differentiate p))
    (PolynomialOrder.value (differentiate (differentiate p)))
    (PolynomialSupersolution.value (κ:ℝ)) (PolynomialSupersolution.velocity (κ:ℝ))
    (PolynomialSupersolution.acceleration (κ:ℝ)) hκR hb.1 hb.2.2.1
    (PolynomialOrder.value_nonnegative f hp.1 (by norm_num)) hr
    (by simpa only [mul_comm] using hclose) hlip hq hx hv hcq hcqv hdx hdv hdq hdqv
    (PolynomialOrder.value_derivative p) (PolynomialOrder.value_derivative (differentiate p))
    (PolynomialSupersolution.derivative (κ:ℝ))
    (PolynomialSupersolution.velocity_derivative (κ:ℝ)) hip hiv hipoly.1 hipoly.2 hi.1 hi.2
    (fun _ ht => PolynomialSupersolution.supersolution hkR ht)
    (fun _ ht => let hb := PolynomialSupersolution.bounds hκR hkR ht; ⟨hb.2.1,hb.2.2.2⟩)
    (fun _ ht => PolynomialOrder.value_le_endpoint f hp.1 ht)
    (fun _ ht => PolynomialForcing.supersolution κ f p hp ht) hdefect

/-- Endpoint values of the nonnegative polynomial envelopes bound every
prefix of the physical trajectory, including all unmodeled gravity terms
already charged in `hdefect`. -/
theorem polynomial_prediction (μ scale : ℝ) (hμ : 0≤μ) (hscale : 0≤scale)
    (x xv q qv qa thrust : ℝ → E) {κ : ℚ} (f p : List ℚ)
    (hp : PolynomialForcing.Valid κ f p) (hκ : 0≤κ) (hk : κ<56) {r M : ℝ}
    (hr : 0<r)
    (hclose : PolynomialOrder.value f 1*PolynomialSupersolution.value (κ:ℝ) 1<M)
    (hlip : scale*(2*μ/r^3)≤(κ:ℝ))
    (hq : ∀ t ∈ Icc (0:ℝ) 1, r+M≤‖q t‖)
    (hx : Continuous x) (hv : Continuous xv) (hcq : Continuous q) (hcqv : Continuous qv)
    (hdx : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt x (xv t) t)
    (hdv : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt xv (scale • (field μ (x t)+thrust t)) t)
    (hdq : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt q (qv t) t)
    (hdqv : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt qv (qa t) t)
    (hip : x 0=q 0) (hiv : xv 0=qv 0)
    (hdefect : ∀ t ∈ Icc (0:ℝ) 1,
      ‖scale • (field μ (q t)+thrust t)-qa t‖≤PolynomialOrder.value f t) :
    ∀ t ∈ Icc (0:ℝ) 1, ‖x t-q t‖≤((evaluate p 1:ℚ):ℝ) ∧
      ‖xv t-qv t‖≤((evaluate (differentiate p) 1:ℚ):ℝ) := by
  have h := polynomial_prediction_curve μ scale hμ hscale x xv q qv qa thrust
    f p hp hκ hk hr hclose hlip hq hx hv hcq hcqv hdx hdv hdq hdqv hip hiv hdefect
  intro t ht
  have hP := PolynomialOrder.value_le_endpoint p hp.2.1 ht
  have hV := PolynomialOrder.value_le_endpoint (differentiate p) hp.2.2.1 ht
  have heP := PolynomialOrder.value_at_rational p 1
  have heV := PolynomialOrder.value_at_rational (differentiate p) 1
  simp only [Rat.cast_one] at heP heV
  exact ⟨(h t ht).1.trans (heP ▸ hP),(h t ht).2.trans (heV ▸ hV)⟩

end GNC.Gravity
