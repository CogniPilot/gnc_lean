import GNC.Dynamics.GravityLipschitz
import GNC.Control.IntegralTube
import Mathlib.Analysis.ODE.Gronwall

/-! Uniqueness for a forced inverse-square orbit on a known nonsingular
reference solution. A first-exit argument supplies the second solution's
region; no noncollision or proximity hypothesis is imposed on it. -/
noncomputable section
namespace GNC.ForcedOrbitUniqueness
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem unique (μ scale : ℝ) (hμ : 0 ≤ μ) (hs : 0 ≤ scale)
    (p v q w u : ℝ → E) (hp : Continuous p) (hv : Continuous v)
    (hq : Continuous q) (hw : Continuous w)
    (hdp : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt p (v t) t)
    (hdv : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt v (scale • (Gravity.field μ (p t)+u t)) t)
    (hdq : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt q (w t) t)
    (hdw : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt w (scale • (Gravity.field μ (q t)+u t)) t)
    (hp0 : p 0 = q 0) (hv0 : v 0 = w 0) {r M : ℝ}
    (hr : 0 < r) (hM : 0 < M) (hgain : scale*(2*μ/r^3) ≤ 1)
    (hregion : ∀ t ∈ Icc (0:ℝ) 1, r+M ≤ ‖q t‖) :
    ∀ t ∈ Icc (0:ℝ) 1, p t = q t ∧ v t = w t := by
  let e : ℝ → E × E := fun t => (p t-q t,v t-w t)
  let de : ℝ → E × E := fun t =>
    (v t-w t, scale • (Gravity.field μ (p t)-Gravity.field μ (q t)))
  have he : Continuous e := (hp.sub hq).prodMk (hv.sub hw)
  have he0 : e 0 = 0 := by simp [e,hp0,hv0]
  have hed (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : HasDerivAt e (de t) t := by
    have h := ((hdp t ht).sub (hdq t ht)).prodMk ((hdv t ht).sub (hdw t ht))
    convert h using 1
    dsimp [de]
    rw [← smul_sub,add_sub_add_right_eq_sub]
  have hlocal (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) (hb : ‖e t‖ ≤ M) : ‖de t‖ ≤ ‖e t‖ := by
    have hpos : ‖p t-q t‖ ≤ M := (norm_fst_le (e t)).trans hb
    have hg := Gravity.field_difference_ball μ hμ (q t) (p t-q t) 0 hr
      (hregion t ht) hpos (by simpa only [norm_zero] using hM.le)
    simp only [add_sub_cancel,add_zero,sub_zero] at hg
    apply norm_prod_le_iff.mpr
    refine ⟨norm_snd_le (e t),?_⟩
    change ‖scale • (Gravity.field μ (p t)-Gravity.field μ (q t))‖ ≤ ‖e t‖
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hs]
    have h := mul_le_mul_of_nonneg_left hg hs
    have hh := mul_le_mul_of_nonneg_right hgain (norm_nonneg (p t-q t))
    have hp := norm_fst_le (e t)
    change ‖p t-q t‖ ≤ ‖e t‖ at hp
    nlinarith
  have hzero (T : ℝ) (hT : T ≤ 1)
      (hb : ∀ t ∈ Icc (0:ℝ) T, ‖e t‖ ≤ M) :
      ∀ t ∈ Icc (0:ℝ) T, e t = 0 := by
    apply eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
      (K := 1) he.continuousOn
      (fun t ht => (hed t ⟨ht.1,ht.2.le.trans hT⟩).hasDerivWithinAt) he0
    intro t ht
    simpa only [one_mul] using hlocal t ⟨ht.1,ht.2.le.trans hT⟩ (hb t (Ico_subset_Icc_self ht))
  have hclosed := IntegralTube.prefix_closure he.norm
    (show ‖e 0‖ < M by simpa only [he0,norm_zero] using hM)
    (a := 0) (b := 1) (by
      intro t ht hb
      rw [hzero t ht.2 hb t ⟨ht.1,le_rfl⟩,norm_zero]
      exact hM)
  intro t ht
  have h := hzero 1 le_rfl (fun t ht => (hclosed t ht).le) t ht
  have hp := congrArg Prod.fst h
  have hv := congrArg Prod.snd h
  exact ⟨sub_eq_zero.mp hp,sub_eq_zero.mp hv⟩

end GNC.ForcedOrbitUniqueness
