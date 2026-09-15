import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

/-! A first-exit theorem for integral response enclosures. Strict closure of
a proposed region prevents the use of its own residual bound from becoming
circular. Bounds are required on a whole time prefix, not a finite grid. -/
noncomputable section
open Set MeasureTheory
namespace GNC.IntegralTube

theorem prefix_closure {f : ℝ → ℝ} {a b level : ℝ} (hf : Continuous f)
    (hinit : f a < level)
    (hclose : ∀ t ∈ Icc a b, (∀ s ∈ Icc a t, f s ≤ level) → f t < level) :
    ∀ t ∈ Icc a b, f t < level := by
  intro t ht
  by_contra hbad
  have hbad' : level ≤ f t := le_of_not_gt hbad
  let S := Icc a t ∩ {s | f s = level}
  have hc : IsCompact S := isCompact_Icc.inter_right (isClosed_eq hf continuous_const)
  have hn : S.Nonempty := by
    obtain ⟨s, hs, he⟩ := intermediate_value_Icc ht.1 hf.continuousOn ⟨hinit.le, hbad'⟩
    exact ⟨s, hs, he⟩
  obtain ⟨u, hu, hmin⟩ := hc.exists_isLeast hn
  have hprefix : ∀ s ∈ Icc a u, f s ≤ level := by
    intro s hs
    by_contra hsbad
    obtain ⟨v, hv, he⟩ := intermediate_value_Icc hs.1 hf.continuousOn
      ⟨hinit.le, (lt_of_not_ge hsbad).le⟩
    have hvS : v ∈ S := ⟨⟨hv.1, hv.2.trans (hs.2.trans hu.1.2)⟩, he⟩
    have heq : s = u := le_antisymm hs.2 ((hmin hvS).trans hv.2)
    have : f s = level := heq ▸ hu.2
    exact hsbad this.le
  have h := hclose u ⟨hu.1.1, hu.1.2.trans ht.2⟩ hprefix
  exact (ne_of_lt h) hu.2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem response_bound (K : ℝ → E →L[ℝ] E) (r : ℝ → E) {a b R gain : ℝ}
    (hab : a ≤ b) (hK : Continuous K) (hr : Continuous r)
    (hR : 0 ≤ R) (hbound : ∀ s ∈ Icc a b, ‖r s‖ ≤ R)
    (hgain : (∫ s in a..b, ‖K s‖) ≤ gain) :
    ‖∫ s in a..b, K s (r s)‖ ≤ gain*R := by
  have hp := intervalIntegral.integral_mono_on (μ := volume) hab
    ((hK.clm_apply hr).norm.intervalIntegrable a b)
    ((hK.norm.mul_const R).intervalIntegrable a b) (fun s hs =>
      ((K s).le_opNorm (r s)).trans (mul_le_mul_of_nonneg_left (hbound s hs) (norm_nonneg _)))
  rw [intervalIntegral.integral_mul_const] at hp
  exact (intervalIntegral.norm_integral_le_integral_norm hab).trans
    (hp.trans (mul_le_mul_of_nonneg_right hgain hR))

/-- Coupled position/velocity closure. The prefix response hypotheses can
be derived with `response_bound` from the two blocks of a fundamental flow. -/
theorem two_region_closure (p v : ℝ → E) {a b P V Lp Lv Gp Gv R : ℝ}
    (hp : Continuous p) (hv : Continuous v) (hP : 0 < P) (hV : 0 < V)
    (hi : ‖p a‖ < P ∧ ‖v a‖ < V)
    (hc : Lp+Gp*R < P ∧ Lv+Gv*R < V)
    (hresponse : ∀ t ∈ Icc a b,
      (∀ s ∈ Icc a t, ‖p s‖ ≤ P ∧ ‖v s‖ ≤ V) →
      ‖p t‖ ≤ Lp+Gp*R ∧ ‖v t‖ ≤ Lv+Gv*R) :
    ∀ t ∈ Icc a b, ‖p t‖ < P ∧ ‖v t‖ < V := by
  have h := prefix_closure (f := fun t => max (‖p t‖/P) (‖v t‖/V))
    ((hp.norm.div_const P).max (hv.norm.div_const V))
    (show max (‖p a‖/P) (‖v a‖/V) < 1 by
      exact max_lt ((div_lt_one hP).mpr hi.1) ((div_lt_one hV).mpr hi.2))
    (a := a) (b := b) (fun t ht hprefix => by
      have hr := hresponse t ht (fun s hs => by
        have hh := max_le_iff.mp (hprefix s hs)
        exact ⟨(div_le_one hP).mp hh.1, (div_le_one hV).mp hh.2⟩)
      exact max_lt ((div_lt_one hP).mpr (hr.1.trans_lt hc.1))
        ((div_lt_one hV).mpr (hr.2.trans_lt hc.2)))
  intro t ht
  have hh := max_lt_iff.mp (h t ht)
  exact ⟨(div_lt_one hP).mp hh.1, (div_lt_one hV).mp hh.2⟩

end GNC.IntegralTube
