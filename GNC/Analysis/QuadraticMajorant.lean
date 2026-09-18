import GNC.Analysis.InitialSecondOrderCertificate
import GNC.Analysis.PolynomialSupersolution

/-! A closed, non-iterative quadratic norm bound for a second-order response.
The denominator `2 - κ` comes from the second derivative of `t²`.
It is a sufficient short-interval bound, not an optimal response envelope.
-/
noncomputable section
namespace GNC.QuadraticMajorant
open Set

def coefficient (κ a b f : ℝ) : ℝ := (κ*(a+b)+f)/(2-κ)
def value (κ a b f t : ℝ) : ℝ := a+b*t+coefficient κ a b f*t^2
def velocity (κ a b f t : ℝ) : ℝ := b+2*coefficient κ a b f*t

theorem coefficient_nonnegative {κ a b f : ℝ}
    (hκ : 0≤κ) (hk : κ<2) (ha : 0≤a) (hb : 0≤b) (hf : 0≤f) :
    0≤coefficient κ a b f := by
  unfold coefficient
  exact div_nonneg (add_nonneg (mul_nonneg hκ (add_nonneg ha hb)) hf)
    (sub_pos.mpr hk).le

theorem derivative (κ a b f t : ℝ) :
    HasDerivAt (value κ a b f) (velocity κ a b f t) t := by
  convert (((hasDerivAt_id t).const_mul b).const_add a).add
    (((hasDerivAt_id t).pow 2).const_mul (coefficient κ a b f)) using 1
  dsimp only [velocity,id_eq]
  ring

theorem velocity_derivative (κ a b f t : ℝ) :
    HasDerivAt (velocity κ a b f) (2*coefficient κ a b f) t := by
  convert ((hasDerivAt_id t).const_mul (2*coefficient κ a b f)).const_add b using 1
  ring

theorem supersolution {κ a b f t : ℝ}
    (hκ : 0≤κ) (hk : κ<2) (ha : 0≤a) (hb : 0≤b) (hf : 0≤f)
    (ht : t ∈ Icc (0:ℝ) 1) :
    κ*value κ a b f t+f≤2*coefficient κ a b f := by
  have hc := coefficient_nonnegative hκ hk ha hb hf
  have he : (2-κ)*coefficient κ a b f=κ*(a+b)+f := by
    unfold coefficient
    exact mul_div_cancel₀ _ (ne_of_gt (sub_pos.mpr hk))
  have ht2 := pow_le_one₀ ht.1 ht.2 (n := 2)
  have hbt := mul_le_of_le_one_right hb ht.2
  have hct := mul_le_of_le_one_right hc ht2
  dsimp only [value]
  nlinarith [mul_nonneg hκ (sub_nonneg.mpr hbt),
    mul_nonneg hκ (sub_nonneg.mpr hct)]

theorem bounds {κ a b f t : ℝ}
    (hκ : 0≤κ) (hk : κ<2) (ha : 0≤a) (hb : 0≤b) (hf : 0≤f)
    (ht : t ∈ Icc (0:ℝ) 1) :
    value κ a b f t≤value κ a b f 1 ∧
      velocity κ a b f t≤velocity κ a b f 1 := by
  have hc := coefficient_nonnegative hκ hk ha hb hf
  have ht2 := pow_le_one₀ ht.1 ht.2 (n := 2)
  dsimp only [value,velocity]
  constructor <;> nlinarith [mul_le_of_le_one_right hb ht.2,
    mul_le_of_le_one_right hc ht2, mul_le_of_le_one_right hc ht.2]

/-- Computed responses qualify through their actual acceleration bound;
they need not solve a linear response equation exactly. -/
theorem response {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p v acc : ℝ → E) {κ a b f : ℝ}
    (hκ : 0≤κ) (hk : κ<2) (ha : 0≤a) (hb : 0≤b) (hf : 0≤f)
    (hp : Continuous p) (hv : Continuous v)
    (hdp : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt p (v t) t)
    (hdv : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt v (acc t) t)
    (hip : ‖p 0‖≤a) (hiv : ‖v 0‖≤b)
    (hacc : ∀ t ∈ Icc (0:ℝ) 1, ‖acc t‖≤κ*‖p t‖+f) :
    ∀ t ∈ Icc (0:ℝ) 1,
      ‖p t‖≤value κ a b f t ∧ ‖v t‖≤velocity κ a b f t := by
  have hk' : κ<56 := hk.trans (by norm_num)
  have hb' := PolynomialSupersolution.bounds hκ hk' (show (1:ℝ) ∈ Icc 0 1 by norm_num)
  have hi := PolynomialSupersolution.initial κ
  exact SecondOrderCertificate.initial_response p v acc (fun _ => f)
    (value κ a b f) (velocity κ a b f) (fun _ => 2*coefficient κ a b f)
    (PolynomialSupersolution.value κ) (PolynomialSupersolution.velocity κ)
    (PolynomialSupersolution.acceleration κ) hκ hb'.1 hb'.2.2.1 hp hv hdp hdv
    (derivative κ a b f) (velocity_derivative κ a b f)
    (PolynomialSupersolution.derivative κ) (PolynomialSupersolution.velocity_derivative κ)
    (by simpa [value] using hip) (by simpa [velocity] using hiv) hi.1 hi.2
    (fun _ ht => PolynomialSupersolution.supersolution hk' ht)
    (fun _ ht => let h := PolynomialSupersolution.bounds hκ hk' ht; ⟨h.2.1,h.2.2.2⟩)
    (fun _ ht => supersolution hκ hk ha hb hf ht) hacc

end GNC.QuadraticMajorant
