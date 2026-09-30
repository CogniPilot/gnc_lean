import GNC.Dynamics.OrbitalCertificate
import GNC.Analysis.MonomialProfile

/-! Automatic polynomial envelopes for a physical orbital predictor whose
defect is a nonnegative sum of monomials. The actual nonlinear gravity
region is closed by first exit; there is no assumed actual-trajectory tube.
This is the real-coefficient counterpart of the checked rational polynomial
certificate, with a fixed constructive envelope rather than a proposal. -/
noncomputable section
namespace GNC.Gravity
open Set
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem monomial_prediction (μ : ℝ) (hμ : 0≤μ)
    (x xv q qv qa thrust : ℝ → E) {N : ℕ} (F : Fin N → ℝ) (n : Fin N → ℕ)
    {κ r M : ℝ} (hκ : 0≤κ) (hk : κ<56) (hF : ∀ i, 0≤F i) (hr : 0<r)
    (hclose : (∑ i, F i)*PolynomialSupersolution.value κ 1<M)
    (hlip : 2*μ/r^3≤κ) (hq : ∀ t ∈ Icc (0:ℝ) 1, r+M≤‖q t‖)
    (hx : Continuous x) (hv : Continuous xv) (hcq : Continuous q) (hcqv : Continuous qv)
    (hdx : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt x (xv t) t)
    (hdv : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt xv (field μ (x t)+thrust t) t)
    (hdq : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt q (qv t) t)
    (hdqv : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt qv (qa t) t)
    (hip : x 0=q 0) (hiv : xv 0=qv 0)
    (hdefect : ∀ t ∈ Icc (0:ℝ) 1,
      ‖field μ (q t)+thrust t-qa t‖≤∑ i, F i*t^(n i)) :
    ∀ t ∈ Icc (0:ℝ) 1,
      ‖x t-q t‖≤∑ i, F i*MonomialSupersolution.value κ (n i) t ∧
      ‖xv t-qv t‖≤∑ i, F i*MonomialSupersolution.velocity κ (n i) t := by
  have hb := PolynomialSupersolution.bounds hκ hk (show (1:ℝ) ∈ Icc 0 1 by norm_num)
  have hi := PolynomialSupersolution.initial κ
  apply prediction_certificate μ 1 hμ (by norm_num) x xv q qv qa thrust
    (fun t => ∑ i, F i*t^(n i))
    (fun t => ∑ i, F i*MonomialSupersolution.value κ (n i) t)
    (fun t => ∑ i, F i*MonomialSupersolution.velocity κ (n i) t)
    (fun t => ∑ i, F i*MonomialSupersolution.acceleration κ (n i) t)
    (PolynomialSupersolution.value κ) (PolynomialSupersolution.velocity κ)
    (PolynomialSupersolution.acceleration κ)
    hκ hb.1 hb.2.2.1 (Finset.sum_nonneg (fun i _ => hF i)) hr
    (by simpa [mul_comm] using hclose) (by simpa using hlip) hq hx hv hcq hcqv
    hdx (by simpa using hdv) hdq hdqv
    (fun t => HasDerivAt.fun_sum (fun i _ =>
      (MonomialSupersolution.derivative κ (n i) t).const_mul (F i)))
    (fun t => HasDerivAt.fun_sum (fun i _ =>
      (MonomialSupersolution.velocity_derivative κ (n i) t).const_mul (F i)))
    (PolynomialSupersolution.derivative κ) (PolynomialSupersolution.velocity_derivative κ)
    hip hiv (by simp [(MonomialSupersolution.initial κ _).1])
    (by simp [(MonomialSupersolution.initial κ _).2]) hi.1 hi.2
    (fun _ ht => PolynomialSupersolution.supersolution hk ht)
    (fun _ ht => let h := PolynomialSupersolution.bounds hκ hk ht; ⟨h.2.1,h.2.2.2⟩)
    (fun t ht => Finset.sum_le_sum (fun i _ => by
      simpa using mul_le_mul_of_nonneg_left (pow_le_one₀ ht.1 ht.2) (hF i)))
    (fun t ht => ?_) (by simpa using hdefect)
  rw [Finset.mul_sum, ←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  have h := mul_le_mul_of_nonneg_left
    (MonomialSupersolution.supersolution_of_gain_lt (n i) hk ht) (hF i)
  nlinarith

end GNC.Gravity
