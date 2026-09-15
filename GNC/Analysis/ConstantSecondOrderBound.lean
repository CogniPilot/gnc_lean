import GNC.Analysis.SecondOrderCertificate
import GNC.Analysis.PolynomialSupersolution

/-! Explicit noniterative bounds for a zero-initial second-order response.
The matrix may vary in time; only its norm gain is bounded. The polynomial
supersolution closes its own tail and does not charge a numerical allowance. -/
noncomputable section
namespace GNC.ConstantSecondOrderBound
open Set PolynomialSupersolution
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem response (p v a : ℝ → E) {κ F : ℝ}
    (hk0 : 0 ≤ κ) (hk : κ < 56) (hF : 0 ≤ F)
    (hp : Continuous p) (hv : Continuous v)
    (hdp : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt p (v t) t)
    (hdv : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt v (a t) t)
    (hip : p 0 = 0) (hiv : v 0 = 0)
    (ha : ∀ t ∈ Icc (0:ℝ) 1, ‖a t‖ ≤ κ*‖p t‖+F) :
    ∀ t ∈ Icc (0:ℝ) 1,
      ‖p t‖ ≤ F*value κ t ∧ ‖v t‖ ≤ F*velocity κ t := by
  have h1 := bounds hk0 hk (show (1:ℝ) ∈ Icc 0 1 by norm_num)
  have hi := initial κ
  apply SecondOrderCertificate.response p v a (fun _ => F)
    (fun t => F*value κ t) (fun t => F*velocity κ t)
    (fun t => F*acceleration κ t) (value κ) (velocity κ) (acceleration κ)
    hk0 h1.1 h1.2.2.1 hp hv hdp hdv
    (fun t => (derivative κ t).const_mul F)
    (fun t => (velocity_derivative κ t).const_mul F)
    (derivative κ) (velocity_derivative κ)
    hip hiv (by simp [hi.1]) (by simp [hi.2]) hi.1 hi.2
    (fun _ ht => supersolution hk ht)
    (fun _ ht => let h := bounds hk0 hk ht; ⟨h.2.1,h.2.2.2⟩)
    (fun t ht => by
      have h := mul_le_mul_of_nonneg_left (supersolution hk ht) hF
      nlinarith) ha

theorem endpoint_bounds (p v a : ℝ → E) {κ F : ℝ}
    (hk0 : 0 ≤ κ) (hk : κ < 56) (hF : 0 ≤ F)
    (hp : Continuous p) (hv : Continuous v)
    (hdp : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt p (v t) t)
    (hdv : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt v (a t) t)
    (hip : p 0 = 0) (hiv : v 0 = 0)
    (ha : ∀ t ∈ Icc (0:ℝ) 1, ‖a t‖ ≤ κ*‖p t‖+F) :
    ∀ t ∈ Icc (0:ℝ) 1,
      ‖p t‖ ≤ F*value κ 1 ∧ ‖v t‖ ≤ F*velocity κ 1 := by
  have h := response p v a hk0 hk hF hp hv hdp hdv hip hiv ha
  intro t ht
  have hb := bounds hk0 hk ht
  exact ⟨(h t ht).1.trans (mul_le_mul_of_nonneg_left hb.2.1 hF),
    (h t ht).2.trans (mul_le_mul_of_nonneg_left hb.2.2.2 hF)⟩

end GNC.ConstantSecondOrderBound
