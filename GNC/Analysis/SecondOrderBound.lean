import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

/-! Finite-horizon bounds for a zero-initial second-order response.
The acceleration may depend on the state and time. A bound by K times the
position norm plus R is sufficient; no constant generator is assumed.
-/
namespace GNC.SecondOrderBound
open Set
set_option autoImplicit false
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Integrating a bounded acceleration gives the exact linear/quadratic
time factors. The calculus is mathlib's norm comparison theorem. -/
theorem acceleration_bound (p v a : ℝ → E) {T B : ℝ}
    (hp : ContinuousOn p (Icc 0 T)) (hv : ContinuousOn v (Icc 0 T))
    (hdp : ∀ t ∈ Ico 0 T, HasDerivWithinAt p (v t) (Ici t) t)
    (hdv : ∀ t ∈ Ico 0 T, HasDerivWithinAt v (a t) (Ici t) t)
    (hip : p 0 = 0) (hiv : v 0 = 0)
    (ha : ∀ t ∈ Ico 0 T, ‖a t‖ ≤ B) :
    ∀ t ∈ Icc 0 T, ‖p t‖ ≤ B*t^2/2 ∧ ‖v t‖ ≤ B*t := by
  have hb : ∀ t ∈ Icc 0 T, ‖v t‖ ≤ B*t := by
    have h := norm_image_sub_le_of_norm_deriv_right_le_segment hv hdv ha
    simpa only [hiv,sub_zero] using h
  have hquad (t : ℝ) : HasDerivAt (fun s => B*s^2/2) (B*t) t := by
    convert (((hasDerivAt_id t).pow 2).const_mul B).div_const 2 using 1
    simp only [id_eq]
    ring
  have h := image_norm_le_of_norm_deriv_right_le_deriv_boundary hp hdp
    (show ‖p 0‖ ≤ B*0^2/2 by simp [hip]) hquad
    (fun t ht => hb t (Ico_subset_Icc_self ht))
  exact fun t ht => ⟨h ht,hb t ht⟩

/-- A finite-horizon small-gain bound using a maximum on the entire compact
interval. The budget can be non-strict, including the zero-input case. -/
theorem small_gain (p v a : ℝ → E) {T K R P : ℝ}
    (hT : 0 ≤ T) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hp : ContinuousOn p (Icc 0 T)) (hv : ContinuousOn v (Icc 0 T))
    (hdp : ∀ t ∈ Ico 0 T, HasDerivWithinAt p (v t) (Ici t) t)
    (hdv : ∀ t ∈ Ico 0 T, HasDerivWithinAt v (a t) (Ici t) t)
    (hip : p 0 = 0) (hiv : v 0 = 0)
    (ha : ∀ t ∈ Ico 0 T, ‖a t‖ ≤ K*‖p t‖+R)
    (hgain : K*T^2/2 < 1) (hbudget : (K*P+R)*T^2/2 ≤ P) :
    ∀ t ∈ Icc 0 T, ‖p t‖ ≤ P ∧ ‖v t‖ ≤ (K*P+R)*t := by
  obtain ⟨s,hs,hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hT) hp.norm
  have hB : 0 ≤ K*‖p s‖+R := by positivity
  have hb := acceleration_bound p v a hp hv hdp hdv hip hiv (fun t ht =>
    (ha t ht).trans (add_le_add
      (mul_le_mul_of_nonneg_left (hmax (Ico_subset_Icc_self ht)) hK) le_rfl))
  have hs2 : s^2 ≤ T^2 := by nlinarith [hs.1,hs.2]
  have hm : ‖p s‖ ≤ (K*‖p s‖+R)*T^2/2 :=
    (hb s hs).1.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hs2 hB) (by norm_num))
  have hd : 0 < 1-K*T^2/2 := by linarith
  have hleft : (1-K*T^2/2)*‖p s‖ ≤ T^2/2*R := by nlinarith [hm]
  have hright : T^2/2*R ≤ (1-K*T^2/2)*P := by nlinarith [hbudget]
  have hmP : ‖p s‖ ≤ P := le_of_mul_le_mul_left (hleft.trans hright) hd
  have hpP : ∀ t ∈ Icc 0 T, ‖p t‖ ≤ P := fun t ht => (hmax ht).trans hmP
  have hf := acceleration_bound p v a hp hv hdp hdv hip hiv (fun t ht =>
    (ha t ht).trans (add_le_add
      (mul_le_mul_of_nonneg_left (hpP t (Ico_subset_Icc_self ht)) hK) le_rfl))
  exact fun t ht => ⟨hpP t ht,(hf t ht).2⟩

/-- Useful rational gains on [0,3/5] when the gravity-gradient norm is at
most four. These bounds hold for every time and every bounded forcing. -/
theorem horizon_three_fifths (p v a : ℝ → E) {R : ℝ} (hR : 0 ≤ R)
    (hp : ContinuousOn p (Icc 0 (3/5))) (hv : ContinuousOn v (Icc 0 (3/5)))
    (hdp : ∀ t ∈ Ico 0 (3/5), HasDerivWithinAt p (v t) (Ici t) t)
    (hdv : ∀ t ∈ Ico 0 (3/5), HasDerivWithinAt v (a t) (Ici t) t)
    (hip : p 0 = 0) (hiv : v 0 = 0)
    (ha : ∀ t ∈ Ico 0 (3/5), ‖a t‖ ≤ 4*‖p t‖+R) :
    ∀ t ∈ Icc 0 (3/5), ‖p t‖ ≤ (9/14)*R ∧ ‖v t‖ ≤ (15/7)*R := by
  have h := small_gain p v a (P := (9/14)*R) (by norm_num) (by norm_num) hR hp hv
    hdp hdv hip hiv ha (by norm_num) (by nlinarith)
  intro t ht
  refine ⟨(h t ht).1,?_⟩
  have hc : 0 ≤ 4*((9/14)*R)+R := by positivity
  have hm := mul_le_mul_of_nonneg_left ht.2 hc
  nlinarith [(h t ht).2]

end GNC.SecondOrderBound
