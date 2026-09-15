import GNC.Analysis.ConstantSecondOrderBound
import GNC.Analysis.MonomialSupersolution

/-! Zero-initial response to a monomial forcing envelope. The source's
time profile is retained, using the same comparison proof as the constant
case; no iteration or fitted residual allowance is introduced. -/
noncomputable section
namespace GNC.MonomialSecondOrderBound
open Set PolynomialSupersolution
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem response (p v a : ℝ → E) (n : ℕ) {κ F : ℝ}
    (hk0 : 0≤κ) (hk : κ<56) (hF : 0≤F)
    (hp : Continuous p) (hv : Continuous v)
    (hdp : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt p (v t) t)
    (hdv : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt v (a t) t)
    (hip : p 0=0) (hiv : v 0=0)
    (ha : ∀ t ∈ Icc (0:ℝ) 1, ‖a t‖≤κ*‖p t‖+F*t^n) :
    ∀ t ∈ Icc (0:ℝ) 1,
      ‖p t‖≤F*MonomialSupersolution.value κ n t ∧
      ‖v t‖≤F*MonomialSupersolution.velocity κ n t := by
  have h1 := bounds hk0 hk (show (1:ℝ) ∈ Icc 0 1 by norm_num)
  have hi := initial κ
  have hm := MonomialSupersolution.initial κ n
  apply SecondOrderCertificate.response p v a (fun t => F*t^n)
    (fun t => F*MonomialSupersolution.value κ n t)
    (fun t => F*MonomialSupersolution.velocity κ n t)
    (fun t => F*MonomialSupersolution.acceleration κ n t)
    (value κ) (velocity κ) (acceleration κ) hk0 h1.1 h1.2.2.1 hp hv hdp hdv
    (fun t => (MonomialSupersolution.derivative κ n t).const_mul F)
    (fun t => (MonomialSupersolution.velocity_derivative κ n t).const_mul F)
    (derivative κ) (velocity_derivative κ)
    hip hiv (by simp [hm.1]) (by simp [hm.2]) hi.1 hi.2
    (fun _ ht => supersolution hk ht)
    (fun _ ht => let h := bounds hk0 hk ht; ⟨h.2.1,h.2.2.2⟩)
    (fun t ht => by
      have h := mul_le_mul_of_nonneg_left
        (MonomialSupersolution.supersolution_of_gain_lt n hk ht) hF
      nlinarith) ha

end GNC.MonomialSecondOrderBound
