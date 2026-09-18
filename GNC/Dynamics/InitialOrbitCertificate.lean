import GNC.Analysis.InitialSecondOrderCertificate
import GNC.Dynamics.PolynomialForcingCertificate
import GNC.Analysis.InitialPolynomialForcing

/-! Certified uncertainty growth from nonzero initial position/velocity
errors. Any predictor representation can use this full-gravity theorem;
initial uncertainty and differential approximation defect are separate. -/
noncomputable section
namespace GNC.Gravity
open Set Planning.PolynomialKernel
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem initial_prediction_certificate (μ scale : ℝ) (hμ : 0≤μ) (hs : 0≤scale)
    (x xv q qv qa thrust : ℝ → E) (f P V W b bv bw : ℝ → ℝ)
    {κ B BV r M : ℝ} (hκ : 0≤κ) (hB : 0≤B) (hBV : 0≤BV) (hr : 0<r)
    (hM : 0≤M) (hclose : ∀ t ∈ Icc (0:ℝ) 1, P t<M)
    (hlip : scale*(2*μ/r^3)≤κ)
    (hq : ∀ t ∈ Icc (0:ℝ) 1, r+M≤‖q t‖)
    (hx : Continuous x) (hv : Continuous xv) (hcq : Continuous q) (hcqv : Continuous qv)
    (hdx : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt x (xv t) t)
    (hdv : ∀ t ∈ Icc (0:ℝ) 1,
      HasDerivAt xv (scale • (field μ (x t)+thrust t)) t)
    (hdq : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt q (qv t) t)
    (hdqv : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt qv (qa t) t)
    (hP : ∀ t, HasDerivAt P (V t) t) (hV : ∀ t, HasDerivAt V (W t) t)
    (hb : ∀ t, HasDerivAt b (bv t) t) (hbv : ∀ t, HasDerivAt bv (bw t) t)
    (hip : ‖x 0-q 0‖≤P 0) (hiv : ‖xv 0-qv 0‖≤V 0)
    (hib : b 0=0) (hibv : bv 0=0)
    (hshape : ∀ t ∈ Icc (0:ℝ) 1, κ*b t+1≤bw t)
    (hbounds : ∀ t ∈ Icc (0:ℝ) 1, b t≤B ∧ bv t≤BV)
    (hsuper : ∀ t ∈ Icc (0:ℝ) 1, κ*P t+f t≤W t)
    (hdefect : ∀ t ∈ Icc (0:ℝ) 1,
      ‖scale • (field μ (q t)+thrust t)-qa t‖≤f t) :
    ∀ t ∈ Icc (0:ℝ) 1, ‖x t-q t‖≤P t ∧ ‖xv t-qv t‖≤V t := by
  apply SecondOrderCertificate.regional_initial_response
    (fun t => x t-q t) (fun t => xv t-qv t)
    (fun t => scale • (field μ (x t)+thrust t)-qa t) f P V W b bv bw
    (by norm_num) hκ hB hBV hclose (hx.sub hcq) (hv.sub hcqv)
    (fun t ht => (hdx t ht).sub (hdq t ht))
    (fun t ht => (hdv t ht).sub (hdqv t ht)) hP hV hb hbv
    hip hiv hib hibv hshape hbounds hsuper
  intro t ht hreg
  have hg := field_difference_ball μ hμ (q t) (x t-q t) 0 hr (hq t ht)
    hreg (by simpa using hM)
  simp only [add_sub_cancel,add_zero,sub_zero] at hg
  have hscaled : ‖scale • (field μ (x t)-field μ (q t))‖≤κ*‖x t-q t‖ := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hs]
    exact (mul_le_mul_of_nonneg_left hg hs).trans (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hlip (norm_nonneg _))
  have hid : scale • (field μ (x t)+thrust t)-qa t =
      scale • (field μ (x t)-field μ (q t))+
      (scale • (field μ (q t)+thrust t)-qa t) := by module
  rw [hid]
  exact (norm_add_le _ _).trans (add_le_add hscaled (hdefect t ht))

/-- A finite rational polynomial certifies the entire uncertainty tube,
not just sampled times or the terminal point. -/
theorem initial_polynomial_prediction (μ scale : ℝ) (hμ : 0≤μ) (hs : 0≤scale)
    (x xv q qv qa thrust : ℝ → E) {κ p₀ v₀ : ℚ} (f p : List ℚ)
    (hp : InitialPolynomialForcing.Valid κ p₀ v₀ f p) (hκ : 0≤κ) (hk : κ<56)
    {r M : ℝ} (hr : 0<r) (hM : 0≤M)
    (hclose : PolynomialOrder.value p 1<M) (hlip : scale*(2*μ/r^3)≤(κ:ℝ))
    (hq : ∀ t ∈ Icc (0:ℝ) 1, r+M≤‖q t‖)
    (hx : Continuous x) (hv : Continuous xv) (hcq : Continuous q) (hcqv : Continuous qv)
    (hdx : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt x (xv t) t)
    (hdv : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt xv (scale • (field μ (x t)+thrust t)) t)
    (hdq : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt q (qv t) t)
    (hdqv : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt qv (qa t) t)
    (hip : ‖x 0-q 0‖≤(p₀:ℝ)) (hiv : ‖xv 0-qv 0‖≤(v₀:ℝ))
    (hdefect : ∀ t ∈ Icc (0:ℝ) 1,
      ‖scale • (field μ (q t)+thrust t)-qa t‖≤PolynomialOrder.value f t) :
    ∀ t ∈ Icc (0:ℝ) 1, ‖x t-q t‖≤PolynomialOrder.value p t ∧
      ‖xv t-qv t‖≤PolynomialOrder.value (differentiate p) t := by
  have hκR : (0:ℝ)≤κ := by exact_mod_cast hκ
  have hkR : (κ:ℝ)<56 := by exact_mod_cast hk
  have hb := PolynomialSupersolution.bounds hκR hkR (show (1:ℝ) ∈ Icc 0 1 by norm_num)
  have hi := PolynomialSupersolution.initial (κ:ℝ)
  have hipoly := InitialPolynomialForcing.initial hp
  exact initial_prediction_certificate μ scale hμ hs x xv q qv qa thrust
    (PolynomialOrder.value f) (PolynomialOrder.value p)
    (PolynomialOrder.value (differentiate p))
    (PolynomialOrder.value (differentiate (differentiate p)))
    (PolynomialSupersolution.value (κ:ℝ)) (PolynomialSupersolution.velocity (κ:ℝ))
    (PolynomialSupersolution.acceleration (κ:ℝ)) hκR hb.1 hb.2.2.1 hr hM
    (fun _ ht => (PolynomialOrder.value_le_endpoint p hp.position_nonnegative ht).trans_lt hclose)
    hlip hq hx hv hcq hcqv hdx hdv hdq hdqv
    (PolynomialOrder.value_derivative p) (PolynomialOrder.value_derivative (differentiate p))
    (PolynomialSupersolution.derivative (κ:ℝ))
    (PolynomialSupersolution.velocity_derivative (κ:ℝ))
    (hipoly.1.symm ▸ hip) (hipoly.2.symm ▸ hiv) hi.1 hi.2
    (fun _ ht => PolynomialSupersolution.supersolution hkR ht)
    (fun _ ht => let h := PolynomialSupersolution.bounds hκR hkR ht; ⟨h.2.1,h.2.2.2⟩)
    (fun _ ht => InitialPolynomialForcing.supersolution hp ht) hdefect

end GNC.Gravity
