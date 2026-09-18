import GNC.Analysis.SecondOrderCertificate

/-! Nonzero initial uncertainty in a second-order error certificate.
The scalar envelope carries initial position and velocity radii; the
auxiliary strict margin is eliminated. Its checked maximum closes the
region without assuming an actual trajectory tube. -/
noncomputable section
namespace GNC.SecondOrderCertificate
open Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem initial_response (p v acc : ℝ → E) (f P V W b bv bw : ℝ → ℝ)
    {T κ B BV : ℝ} (hκ : 0≤κ) (hB : 0≤B) (hBV : 0≤BV)
    (hp : Continuous p) (hv : Continuous v)
    (hdp : ∀ t ∈ Icc 0 T, HasDerivAt p (v t) t)
    (hdv : ∀ t ∈ Icc 0 T, HasDerivAt v (acc t) t)
    (hP : ∀ t, HasDerivAt P (V t) t) (hV : ∀ t, HasDerivAt V (W t) t)
    (hb : ∀ t, HasDerivAt b (bv t) t) (hbv : ∀ t, HasDerivAt bv (bw t) t)
    (hip : ‖p 0‖≤P 0) (hiv : ‖v 0‖≤V 0)
    (hib : b 0=0) (hibv : bv 0=0)
    (hshape : ∀ t ∈ Icc 0 T, κ*b t+1≤bw t)
    (hbounds : ∀ t ∈ Icc 0 T, b t≤B ∧ bv t≤BV)
    (hsuper : ∀ t ∈ Icc 0 T, κ*P t+f t≤W t)
    (ha : ∀ t ∈ Icc 0 T, ‖acc t‖≤κ*‖p t‖+f t) :
    ∀ t ∈ Icc 0 T, ‖p t‖≤P t ∧ ‖v t‖≤V t := by
  intro t ht
  have hε (ε : ℝ) (he : 0<ε) :
      ‖p t‖≤P t+ε*(1+κ*B) ∧ ‖v t‖≤V t+ε*(κ*BV) := by
    have hh := SecondOrderEnvelope.barrier p v acc
      (fun s => P s+ε+(κ*ε)*b s) (fun s => V s+(κ*ε)*bv s)
      (fun s => W s+(κ*ε)*bw s) hp hv hdp hdv
      (fun s => ((hP s).add_const ε).add ((hb s).const_mul (κ*ε)))
      (fun s => (hV s).add ((hbv s).const_mul (κ*ε)))
      (by dsimp only; rw [hib]; nlinarith)
      (by simpa only [hibv,mul_zero,add_zero] using hiv) (by
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

/-- The very same nonzero-initial envelope also proves its region valid.
No independently assumed tube or added physical initial slack is needed. -/
theorem regional_initial_response (p v acc : ℝ → E) (f P V W b bv bw : ℝ → ℝ)
    {T κ B BV M : ℝ} (hT : 0≤T) (hκ : 0≤κ) (hB : 0≤B) (hBV : 0≤BV)
    (hclose : ∀ t ∈ Icc 0 T, P t<M)
    (hp : Continuous p) (hv : Continuous v)
    (hdp : ∀ t ∈ Icc 0 T, HasDerivAt p (v t) t)
    (hdv : ∀ t ∈ Icc 0 T, HasDerivAt v (acc t) t)
    (hP : ∀ t, HasDerivAt P (V t) t) (hV : ∀ t, HasDerivAt V (W t) t)
    (hb : ∀ t, HasDerivAt b (bv t) t) (hbv : ∀ t, HasDerivAt bv (bw t) t)
    (hip : ‖p 0‖≤P 0) (hiv : ‖v 0‖≤V 0)
    (hib : b 0=0) (hibv : bv 0=0)
    (hshape : ∀ t ∈ Icc 0 T, κ*b t+1≤bw t)
    (hbounds : ∀ t ∈ Icc 0 T, b t≤B ∧ bv t≤BV)
    (hsuper : ∀ t ∈ Icc 0 T, κ*P t+f t≤W t)
    (ha : ∀ t ∈ Icc 0 T, ‖p t‖≤M → ‖acc t‖≤κ*‖p t‖+f t) :
    ∀ t ∈ Icc 0 T, ‖p t‖≤P t ∧ ‖v t‖≤V t := by
  have hregion := IntegralTube.prefix_closure hp.norm
    (hip.trans_lt (hclose 0 ⟨le_rfl,hT⟩)) (a := 0) (b := T) (by
      intro t ht hprefix
      have sub (s : ℝ) (hs : s ∈ Icc 0 t) : s ∈ Icc (0:ℝ) T := ⟨hs.1,hs.2.trans ht.2⟩
      have h := initial_response p v acc f P V W b bv bw hκ hB hBV hp hv
        (fun s hs => hdp s (sub s hs)) (fun s hs => hdv s (sub s hs))
        hP hV hb hbv hip hiv hib hibv
        (fun s hs => hshape s (sub s hs)) (fun s hs => hbounds s (sub s hs))
        (fun s hs => hsuper s (sub s hs))
        (fun s hs => ha s (sub s hs) (hprefix s hs)) t ⟨ht.1,le_rfl⟩
      exact h.1.trans_lt (hclose t ht))
  exact initial_response p v acc f P V W b bv bw hκ hB hBV hp hv hdp hdv
    hP hV hb hbv hip hiv hib hibv hshape hbounds hsuper
    (fun t ht => ha t ht (hregion t ht).le)

end GNC.SecondOrderCertificate
