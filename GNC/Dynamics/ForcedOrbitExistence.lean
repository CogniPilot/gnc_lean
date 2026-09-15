import GNC.Analysis.EuclideanClip
import GNC.Analysis.TimeDependentODE
import GNC.Dynamics.GravityLipschitz
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Finite-horizon existence of a forced relative inverse-square orbit.
The bounded extension is an existence device. A Grönwall estimate proves
that no clipping is active on the whole normalized horizon [0,1].
Consequently the resulting solution obeys the original singular field,
and its position stays away from collision. -/
noncomputable section
namespace GNC.ForcedOrbitExistence
open Set EuclideanClip
open scoped NNReal
abbrev State := E3 × E3

def rate (μ scale : ℝ) (c d : E3) (x : State) : State :=
  (x.2, scale • (Gravity.field μ (c+x.1)-Gravity.field μ c)+d)

def extension (μ scale : ℝ) (R : ℚ) (c d : E3) (x : State) : State :=
  (clip R x.2, scale • (Gravity.field μ (c+clip R x.1)-Gravity.field μ c)+d)

variable {μ scale r : ℝ} {R : ℚ}

theorem gravity_difference (hμ : 0 ≤ μ) (hs : 0 ≤ scale) (hr : 0 < r)
    (hR : 0 ≤ R) (hgain : scale*(2*μ/r^3) ≤ 1)
    (c : E3) (hc : r+2*(R:ℝ) ≤ ‖c‖) (x y : E3) :
    ‖scale • (Gravity.field μ (c+clip R x)-Gravity.field μ (c+clip R y))‖ ≤
      ‖clip R x-clip R y‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs]
  have h := Gravity.field_difference_ball μ hμ c (clip R x) (clip R y)
    hr hc (norm_bound hR x) (norm_bound hR y)
  calc
    _ ≤ scale*((2*μ/r^3)*‖clip R x-clip R y‖) := mul_le_mul_of_nonneg_left h hs
    _ ≤ ‖clip R x-clip R y‖ := by
      nlinarith [mul_le_mul_of_nonneg_right hgain (norm_nonneg (clip R x-clip R y))]

theorem extension_lipschitz (hμ : 0 ≤ μ) (hs : 0 ≤ scale) (hr : 0 < r)
    (hR : 0 ≤ R) (hgain : scale*(2*μ/r^3) ≤ 1)
    (c d : E3) (hc : r+2*(R:ℝ) ≤ ‖c‖) :
    LipschitzWith 2 (extension μ scale R c d) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm, NNReal.coe_ofNat]
  apply norm_prod_le_iff.mpr
  constructor
  · exact (difference R x.2 y.2).trans
      (mul_le_mul_of_nonneg_left (norm_snd_le (x-y)) (by norm_num))
  · change ‖(scale • (Gravity.field μ (c+clip R x.1)-Gravity.field μ c)+d)-
      (scale • (Gravity.field μ (c+clip R y.1)-Gravity.field μ c)+d)‖ ≤ _
    rw [add_sub_add_right_eq_sub, ← smul_sub, sub_sub_sub_cancel_right]
    exact (gravity_difference hμ hs hr hR hgain c hc x.1 y.1).trans
      ((difference R x.1 y.1).trans
        (mul_le_mul_of_nonneg_left (norm_fst_le (x-y)) (by norm_num)))

theorem extension_zero (hR : 0 ≤ R) (c d : E3) :
    extension μ scale R c d 0 = (0,d) := by
  simp [extension, EuclideanClip.zero hR]

theorem extension_bound (hμ : 0 ≤ μ) (hs : 0 ≤ scale) (hr : 0 < r)
    (hR : 0 ≤ R) (hgain : scale*(2*μ/r^3) ≤ 1)
    (c d : E3) (hc : r+2*(R:ℝ) ≤ ‖c‖) {D : ℝ} (hd : ‖d‖ ≤ D) (x : State) :
    ‖extension μ scale R c d x‖ ≤ 2*(R:ℝ)+D := by
  have hD : 0 ≤ D := (norm_nonneg d).trans hd
  apply norm_prod_le_iff.mpr
  constructor
  · exact (norm_bound hR x.2).trans (by linarith)
  · have hg := gravity_difference hμ hs hr hR hgain c hc x.1 0
    rw [EuclideanClip.zero hR, add_zero, sub_zero] at hg
    exact (norm_add_le _ d).trans (add_le_add (hg.trans (norm_bound hR x.1)) hd)

theorem shifted_nonzero (hr : 0 < r) (hR : 0 ≤ R)
    (c : E3) (hc : r+2*(R:ℝ) ≤ ‖c‖) (x : E3) : c+clip R x ≠ 0 := by
  have hh : ‖c‖ ≤ ‖c+clip R x‖+‖clip R x‖ := by
    simpa only [add_sub_cancel_right] using norm_sub_le (c+clip R x) (clip R x)
  exact norm_pos_iff.mp (by linarith [norm_bound hR x])

theorem extension_continuous (hr : 0 < r) (hR : 0 ≤ R)
    (c d : ℝ → E3) (hc : Continuous c) (hd : Continuous d)
    (hregion : ∀ t, r+2*(R:ℝ) ≤ ‖c t‖) :
    Continuous (fun z : ℝ × State => extension μ scale R (c z.1) (d z.1) z.2) := by
  have hshift : Continuous (fun z : ℝ × State => c z.1+clip R z.2.1) :=
    (hc.comp continuous_fst).add ((lipschitz R).continuous.comp continuous_snd.fst)
  have hg : Continuous (fun z : ℝ × State => Gravity.field μ (c z.1+clip R z.2.1)) := by
    unfold Gravity.field
    exact (continuous_const.div (hshift.norm.pow 3) (fun z =>
      pow_ne_zero 3 (norm_ne_zero_iff.mpr (shifted_nonzero hr hR _ (hregion z.1) _)))).smul hshift
  have hc0 (t : ℝ) : c t ≠ 0 := by
    have hRr : (0:ℝ) ≤ R := by exact_mod_cast hR
    exact norm_pos_iff.mp (by linarith [hregion t])
  have hg0 : Continuous (fun z : ℝ × State => Gravity.field μ (c z.1)) := by
    unfold Gravity.field
    exact (continuous_const.div ((hc.comp continuous_fst).norm.pow 3)
      (fun z => pow_ne_zero 3 (norm_ne_zero_iff.mpr (hc0 z.1)))).smul (hc.comp continuous_fst)
  exact ((lipschitz R).continuous.comp continuous_snd.snd).prodMk
    (((hg.sub hg0).const_smul scale).add (hd.comp continuous_fst))

/-- A coarse construction bound; it is not added to a subsequent certified
prediction-error budget. `4D ≤ R` proves the clipping is inactive. -/
theorem exists_relative (hμ : 0 ≤ μ) (hs : 0 ≤ scale) (hr : 0 < r)
    (hR : 0 ≤ R) (hgain : scale*(2*μ/r^3) ≤ 1)
    (c d : ℝ → E3) (hc : Continuous c) (hd : Continuous d)
    (hregion : ∀ t, r+2*(R:ℝ) ≤ ‖c t‖)
    {D : ℝ} (hD : 0 ≤ D) (hforce : ∀ t, ‖d t‖ ≤ D) (hclose : 4*D ≤ (R:ℝ)) :
    ∃ x : ℝ → State, Continuous x ∧ x 0 = 0 ∧
      (∀ t ∈ Icc (0:ℝ) 1, ‖x t‖ ≤ 4*D) ∧
      (∀ t ∈ Icc (0:ℝ) 1, r ≤ ‖c t+(x t).1‖) ∧
      ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt x (rate μ scale (c t) (d t) (x t)) t := by
  have hRr : (0:ℝ) ≤ R := by exact_mod_cast hR
  let L : ℝ≥0 := ⟨2*(R:ℝ)+D, by positivity⟩
  obtain ⟨x,hx,hx0,hxd⟩ := BoundedODE.exists_time_dependent
    (fun t => extension μ scale R (c t) (d t)) 2 L
    (fun t => extension_lipschitz hμ hs hr hR hgain _ _ (hregion t))
    (extension_continuous hr hR c d hc hd hregion)
    (fun t x => extension_bound hμ hs hr hR hgain _ _ (hregion t) (hforce t) x)
    0 (by norm_num : (0:ℝ) ≤ 1)
  have hb : ∀ t ∈ Icc (0:ℝ) 1, ‖x t‖ ≤ 4*D := by
    have hgrowth (t : ℝ) :
        ‖extension μ scale R (c t) (d t) (x t)‖ ≤ 2*‖x t‖+D := by
      have hl := (extension_lipschitz hμ hs hr hR hgain (c t) (d t) (hregion t)).dist_le_mul (x t) 0
      rw [dist_eq_norm, dist_zero_right, extension_zero hR] at hl
      have hz : ‖((0,d t):State)‖ = ‖d t‖ := by simp
      have hh := norm_le_norm_sub_add (extension μ scale R (c t) (d t) (x t)) (0,d t)
      rw [hz] at hh
      norm_num only [NNReal.coe_ofNat] at hl
      linarith [hforce t]
    have h := norm_le_gronwallBound_of_norm_deriv_right_le
      (a := 0) (b := 1) (δ := 0) (K := 2) (ε := D) hx.continuousOn
      (fun t ht => (hxd t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
      (by simp [hx0]) (fun t _ => hgrowth t)
    intro t ht
    have he : Real.exp (2*t) ≤ 9 := by
      calc
        Real.exp (2*t) ≤ Real.exp (2:ℝ) := Real.exp_le_exp.mpr (by linarith [ht.2])
        _ = (Real.exp 1)^2 := by simpa using Real.exp_nat_mul (1:ℝ) 2
        _ ≤ 9 := by nlinarith [Real.exp_one_lt_three, Real.exp_pos (1:ℝ)]
    have hh := h t ht
    norm_num [gronwallBound] at hh
    nlinarith [mul_le_mul_of_nonneg_left he hD]
  have hinactive (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      clip R (x t).1 = (x t).1 ∧ clip R (x t).2 = (x t).2 :=
    ⟨eq_self ((norm_fst_le (x t)).trans ((hb t ht).trans hclose)),
      eq_self ((norm_snd_le (x t)).trans ((hb t ht).trans hclose))⟩
  refine ⟨x,hx,hx0,hb,?_,?_⟩
  · intro t ht
    have hh : ‖c t‖ ≤ ‖c t+(x t).1‖+‖(x t).1‖ := by
      simpa only [add_sub_cancel_right] using norm_sub_le (c t+(x t).1) (x t).1
    have hp := (norm_fst_le (x t)).trans ((hb t ht).trans hclose)
    linarith [hregion t]
  · intro t ht
    simpa only [extension, (hinactive t ht).1, (hinactive t ht).2, rate] using hxd t ht

end GNC.ForcedOrbitExistence
