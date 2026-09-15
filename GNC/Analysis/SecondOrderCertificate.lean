import GNC.Analysis.SecondOrderEnvelope
import Mathlib.Tactic

/-! A parameterized residual certificate for a second-order ODE. A supplied
scalar supersolution closes the region and bounds the actual error. The
auxiliary strict comparison margin is eliminated; no numerical allowance
appears in the conclusion. -/
noncomputable section
namespace GNC.SecondOrderCertificate
open Set

theorem remove_slack {a b k : ℝ} (hk : 0 ≤ k)
    (h : ∀ ε > 0, a ≤ b+ε*k) : a ≤ b := by
  by_cases hk0 : k = 0
  · simpa [hk0] using h 1 (by norm_num)
  · have hkp : 0 < k := lt_of_le_of_ne hk (Ne.symm hk0)
    apply le_of_forall_pos_le_add
    intro δ hδ
    simpa [div_mul_cancel₀ _ hk0] using h (δ/k) (div_pos hδ hkp)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A supplied unit-forcing supersolution makes zero-initial comparison
non-strict, without retaining an initial margin in the result. -/
theorem response (p v acc : ℝ → E) (f P V W b bv bw : ℝ → ℝ)
    {T κ B BV : ℝ} (hκ : 0 ≤ κ) (hB : 0 ≤ B) (hBV : 0 ≤ BV)
    (hp : Continuous p) (hv : Continuous v)
    (hdp : ∀ t ∈ Icc 0 T, HasDerivAt p (v t) t)
    (hdv : ∀ t ∈ Icc 0 T, HasDerivAt v (acc t) t)
    (hP : ∀ t, HasDerivAt P (V t) t) (hV : ∀ t, HasDerivAt V (W t) t)
    (hb : ∀ t, HasDerivAt b (bv t) t) (hbv : ∀ t, HasDerivAt bv (bw t) t)
    (hip : p 0 = 0) (hiv : v 0 = 0) (hiP : P 0 = 0) (hiV : V 0 = 0)
    (hib : b 0 = 0) (hibv : bv 0 = 0)
    (hshape : ∀ t ∈ Icc 0 T, κ*b t+1 ≤ bw t)
    (hbounds : ∀ t ∈ Icc 0 T, b t ≤ B ∧ bv t ≤ BV)
    (hsuper : ∀ t ∈ Icc 0 T, κ*P t+f t ≤ W t)
    (ha : ∀ t ∈ Icc 0 T, ‖acc t‖ ≤ κ*‖p t‖+f t) :
    ∀ t ∈ Icc 0 T, ‖p t‖ ≤ P t ∧ ‖v t‖ ≤ V t := by
  intro t ht
  have hε (ε : ℝ) (he : 0 < ε) :
      ‖p t‖ ≤ P t+ε*(1+κ*B) ∧ ‖v t‖ ≤ V t+ε*(κ*BV) := by
    have h := SecondOrderEnvelope.barrier p v acc
      (fun s => P s+ε+(κ*ε)*b s) (fun s => V s+(κ*ε)*bv s)
      (fun s => W s+(κ*ε)*bw s) hp hv hdp hdv
      (fun s => ((hP s).add_const ε).add ((hb s).const_mul (κ*ε)))
      (fun s => (hV s).add ((hbv s).const_mul (κ*ε)))
      (by simpa [hip,hiP,hib] using he) (by simp [hiv,hiV,hibv]) (by
        intro s hs hreg
        have hs' := hsuper s hs
        have hb' := mul_le_mul_of_nonneg_left (hshape s hs) (mul_nonneg hκ he.le)
        have ha' := ha s hs
        have hc := mul_le_mul_of_nonneg_left hreg hκ
        nlinarith) t ht
    have hb' := mul_le_mul_of_nonneg_left (hbounds t ht).1 (mul_nonneg hκ he.le)
    have hv' := mul_le_mul_of_nonneg_left (hbounds t ht).2 (mul_nonneg hκ he.le)
    constructor <;> nlinarith
  exact ⟨remove_slack (by positivity) (fun ε he => (hε ε he).1),
    remove_slack (mul_nonneg hκ hBV) (fun ε he => (hε ε he).2)⟩

/-- The acceleration inequality need hold only in a candidate-centered
region. Its strict closure uses the unit-forcing response and a forcing
supremum; the final bound retains the full forcing time profile. -/
theorem regional_response (p v acc : ℝ → E) (f P V W b bv bw : ℝ → ℝ)
    {T κ B BV F M : ℝ} (hκ : 0 ≤ κ) (hB : 0 ≤ B) (hBV : 0 ≤ BV) (hF : 0 ≤ F)
    (hclose : B*F < M)
    (hp : Continuous p) (hv : Continuous v)
    (hdp : ∀ t ∈ Icc 0 T, HasDerivAt p (v t) t)
    (hdv : ∀ t ∈ Icc 0 T, HasDerivAt v (acc t) t)
    (hP : ∀ t, HasDerivAt P (V t) t) (hV : ∀ t, HasDerivAt V (W t) t)
    (hb : ∀ t, HasDerivAt b (bv t) t) (hbv : ∀ t, HasDerivAt bv (bw t) t)
    (hip : p 0 = 0) (hiv : v 0 = 0) (hiP : P 0 = 0) (hiV : V 0 = 0)
    (hib : b 0 = 0) (hibv : bv 0 = 0)
    (hshape : ∀ t ∈ Icc 0 T, κ*b t+1 ≤ bw t)
    (hbounds : ∀ t ∈ Icc 0 T, b t ≤ B ∧ bv t ≤ BV)
    (hforcing : ∀ t ∈ Icc 0 T, f t ≤ F)
    (hsuper : ∀ t ∈ Icc 0 T, κ*P t+f t ≤ W t)
    (ha : ∀ t ∈ Icc 0 T, ‖p t‖ ≤ M → ‖acc t‖ ≤ κ*‖p t‖+f t) :
    ∀ t ∈ Icc 0 T, ‖p t‖ ≤ P t ∧ ‖v t‖ ≤ V t := by
  have hMp : 0 < M := (mul_nonneg hB hF).trans_lt hclose
  have hregion := IntegralTube.prefix_closure hp.norm
    (show ‖p 0‖ < M by simpa [hip] using hMp) (a := 0) (b := T) (by
      intro t ht hprefix
      have sub (s : ℝ) (hs : s ∈ Icc 0 t) : s ∈ Icc (0:ℝ) T := ⟨hs.1,hs.2.trans ht.2⟩
      have hr := response p v acc (fun _ => F) (fun s => F*b s)
        (fun s => F*bv s) (fun s => F*bw s) b bv bw hκ hB hBV hp hv
        (fun s hs => hdp s (sub s hs)) (fun s hs => hdv s (sub s hs))
        (fun s => (hb s).const_mul F) (fun s => (hbv s).const_mul F) hb hbv
        hip hiv (by simp [hib]) (by simp [hibv]) hib hibv
        (fun s hs => hshape s (sub s hs)) (fun s hs => hbounds s (sub s hs)) (by
          intro s hs
          have h := mul_le_mul_of_nonneg_left (hshape s (sub s hs)) hF
          nlinarith) (by
          intro s hs
          exact (ha s (sub s hs) (hprefix s hs)).trans
            (add_le_add_right (hforcing s (sub s hs)) _)) t ⟨ht.1,le_rfl⟩
      have hb' := mul_le_mul_of_nonneg_left (hbounds t ht).1 hF
      nlinarith [hr.1])
  exact response p v acc f P V W b bv bw hκ hB hBV hp hv hdp hdv hP hV hb hbv
    hip hiv hiP hiV hib hibv hshape hbounds hsuper
    (fun t ht => ha t ht (hregion t ht).le)

end GNC.SecondOrderCertificate
