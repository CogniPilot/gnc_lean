import GNC.Control.IntegralTube
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod

/-! A componentwise first-exit certificate for a differentiable error curve.
The derivative equation and bound need only hold inside the proposed error
box. Strict closure establishes that region instead of assuming it.
-/
noncomputable section
namespace GNC.BoxCertificate
open Set
variable {n : ℕ}

theorem response (e d : ℝ → Fin n → ℝ) (B C I : Fin n → ℝ) {T : ℝ}
    (hT : 0 ≤ T) (hB : ∀ i, 0 < B i) (hC : ∀ i, 0 ≤ C i)
    (hclose : ∀ i, I i + T * C i < B i)
    (he : Continuous e) (hi : ∀ i, |e 0 i| ≤ I i)
    (hd : ∀ t ∈ Icc (0 : ℝ) T, (∀ i, |e t i| ≤ B i) → HasDerivAt e (d t) t)
    (hbound : ∀ t ∈ Icc (0 : ℝ) T, (∀ i, |e t i| ≤ B i) → ∀ i, |d t i| ≤ C i) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ i, |e t i| < B i := by
  let scaled := fun t i => e t i / B i
  have hc : Continuous scaled := continuous_pi fun i =>
    ((continuous_apply i).comp he).div_const _
  have hinitial : ‖scaled 0‖ < 1 := by
    apply (pi_norm_lt_iff (by norm_num : (0 : ℝ) < 1)).mpr
    intro i
    simp only [scaled, Real.norm_eq_abs, abs_div, abs_of_pos (hB i)]
    apply (div_lt_one (hB i)).mpr
    exact (hi i).trans_lt (lt_of_le_of_lt (le_add_of_nonneg_right (mul_nonneg hT (hC i))) (hclose i))
  have hprefix := IntegralTube.prefix_closure hc.norm hinitial (a := 0) (b := T) (by
    intro t ht hpref
    have herr (s : ℝ) (hs : s ∈ Icc (0 : ℝ) t) (i : Fin n) : |e s i| ≤ B i := by
      have h := (norm_le_pi_norm (scaled s) i).trans (hpref s hs)
      simp only [scaled, Real.norm_eq_abs, abs_div, abs_of_pos (hB i)] at h
      exact (div_le_one (hB i)).mp h
    apply (pi_norm_lt_iff (by norm_num : (0 : ℝ) < 1)).mpr
    intro i
    have hm := norm_image_sub_le_of_norm_deriv_le_segment'
      (fun s hs => (hasDerivAt_pi.mp (hd s ⟨hs.1, hs.2.trans ht.2⟩ (herr s hs)) i).hasDerivWithinAt)
      (fun s hs => by
        simpa only [Real.norm_eq_abs] using
          hbound s ⟨hs.1, hs.2.le.trans ht.2⟩ (herr s (Ico_subset_Icc_self hs)) i)
      t (right_mem_Icc.mpr ht.1)
    simp only [sub_zero, Real.norm_eq_abs] at hm
    simp only [scaled, Real.norm_eq_abs, abs_div, abs_of_pos (hB i)]
    apply (div_lt_one (hB i)).mpr
    have hg := abs_sub_abs_le_abs_sub (e t i) (e 0 i)
    have htC := mul_le_mul_of_nonneg_right ht.2 (hC i)
    nlinarith [hi i, hclose i])
  intro t ht i
  have h := (norm_le_pi_norm (scaled t) i).trans_lt (hprefix t ht)
  simp only [scaled, Real.norm_eq_abs, abs_div, abs_of_pos (hB i)] at h
  exact (div_lt_one (hB i)).mp h

end GNC.BoxCertificate
