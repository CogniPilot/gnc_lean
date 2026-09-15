import GNC.Dynamics.OrbitalCertificate
import GNC.Analysis.PolynomialSupersolution

/-! A constructive constant-defect orbital certificate. The comparison
polynomial and its endpoint gains are explicit; all region conditions are
checks on the candidate. There is no extra numerical error allowance. -/
noncomputable section
namespace GNC.Gravity
open Set
open PolynomialSupersolution (value velocity acceleration)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem constant_prediction (μ scale : ℝ) (hμ : 0 ≤ μ) (hscale : 0 ≤ scale)
    (x xv q qv qa thrust : ℝ → E) {κ F r M : ℝ}
    (hκ : 0 ≤ κ) (hk : κ < 56) (hF : 0 ≤ F) (hr : 0 < r)
    (hclose : F*value κ 1 < M) (hlip : scale*(2*μ/r^3) ≤ κ)
    (hq : ∀ t ∈ Icc (0:ℝ) 1, r+M ≤ ‖q t‖)
    (hx : Continuous x) (hv : Continuous xv) (hcq : Continuous q) (hcqv : Continuous qv)
    (hdx : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt x (xv t) t)
    (hdv : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt xv (scale • (field μ (x t)+thrust t)) t)
    (hdq : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt q (qv t) t)
    (hdqv : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt qv (qa t) t)
    (hip : x 0 = q 0) (hiv : xv 0 = qv 0)
    (hdefect : ∀ t ∈ Icc (0:ℝ) 1, ‖scale • (field μ (q t)+thrust t)-qa t‖ ≤ F) :
    ∀ t ∈ Icc (0:ℝ) 1,
      ‖x t-q t‖ ≤ F*value κ 1 ∧ ‖xv t-qv t‖ ≤ F*velocity κ 1 := by
  have hb := PolynomialSupersolution.bounds hκ hk (show (1:ℝ) ∈ Icc 0 1 by norm_num)
  have hi := PolynomialSupersolution.initial κ
  have h := prediction_certificate μ scale hμ hscale x xv q qv qa thrust (fun _ => F)
    (fun t => F*value κ t) (fun t => F*velocity κ t) (fun t => F*acceleration κ t)
    (value κ) (velocity κ) (acceleration κ) hκ hb.1 hb.2.2.1 hF hr
    (by simpa only [mul_comm] using hclose) hlip hq hx hv hcq hcqv hdx hdv hdq hdqv
    (fun t => (PolynomialSupersolution.derivative κ t).const_mul F)
    (fun t => (PolynomialSupersolution.velocity_derivative κ t).const_mul F)
    (PolynomialSupersolution.derivative κ) (PolynomialSupersolution.velocity_derivative κ)
    hip hiv (by change F*value κ 0 = 0; rw [hi.1,mul_zero])
    (by change F*velocity κ 0 = 0; rw [hi.2,mul_zero]) hi.1 hi.2
    (fun _ ht => PolynomialSupersolution.supersolution hk ht)
    (fun _ ht => let hb := PolynomialSupersolution.bounds hκ hk ht; ⟨hb.2.1,hb.2.2.2⟩)
    (fun _ _ => le_rfl) (fun t ht => by
      have h := mul_le_mul_of_nonneg_left (PolynomialSupersolution.supersolution hk ht) hF
      nlinarith) hdefect
  intro t ht
  have htbound := PolynomialSupersolution.bounds hκ hk ht
  exact ⟨(h t ht).1.trans (mul_le_mul_of_nonneg_left htbound.2.1 hF),
    (h t ht).2.trans (mul_le_mul_of_nonneg_left htbound.2.2.2 hF)⟩

end GNC.Gravity
