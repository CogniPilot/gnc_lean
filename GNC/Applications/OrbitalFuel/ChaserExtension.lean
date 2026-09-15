import GNC.Dynamics.GravityLipschitz
import GNC.Analysis.ClippedPolynomial
import GNC.Analysis.SwitchedODE

/-! A bounded extension of the solar chaser's scaled relative dynamics.
The first component is position error and the second is velocity error / 4.
Clipping constructs solutions only; it will be proved inactive on the mission.
-/
noncomputable section
set_option autoImplicit false
namespace GNC.Applications.OrbitalFuel.ChaserExtension
open GNC GNC.Gravity GNC.PolynomialODE Set

abbrev State := Vec3 × Vec3

def drift (c a : Vec3) (x : State) : State :=
  ((4:ℝ) • clip (1/20) x.2,
    (1/4:ℝ) • (field3 1 (c+clip (1/20) x.1)-field3 1 c-a))

theorem clipped_norm (x : Vec3) : ‖clip (1/20) x‖ ≤ (1/20:ℝ) := by
  simpa using clip_norm (by norm_num : (0:ℚ) ≤ 1/20) x

theorem clipped_difference (x y : Vec3) :
    ‖clip (1/20) x-clip (1/20) y‖ ≤ ‖x-y‖ := by
  simpa only [dist_eq_norm,NNReal.coe_one,one_mul] using
    (clip_lipschitz (n := 3) (1/20)).dist_le_mul x y

theorem clipped_zero : clip (1/20) (0:Vec3) = 0 := by
  apply clip_eq
  intro i
  norm_num

theorem shift_radius (c p : Vec3) (hc : (79/100:ℝ) ≤ GNC.enorm c)
    (hp : ‖p‖ ≤ (1/20:ℝ)) : (69/100:ℝ) ≤ GNC.enorm (c+p) := by
  have h : GNC.enorm c ≤ GNC.enorm (c+p)+GNC.enorm p := by
    simpa only [add_neg_cancel_right,GNC.enorm_neg] using GNC.enorm_add_le (c+p) (-p)
  linarith [enorm_le_two_pi_norm p]

theorem drift_lipschitz (c a : Vec3) (hc : (79/100:ℝ) ≤ GNC.enorm c) :
    LipschitzWith 4 (drift c a) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm,NNReal.coe_ofNat]
  apply norm_prod_le_iff.mpr
  constructor
  · change ‖(4:ℝ) • clip (1/20) x.2-4 • clip (1/20) y.2‖ ≤ _
    rw [← smul_sub,norm_smul]
    norm_num
    have h := clipped_difference x.2 y.2
    have hxy := norm_snd_le (x-y)
    change ‖x.2-y.2‖ ≤ ‖x-y‖ at hxy
    linarith
  · change ‖(1/4:ℝ) • (field3 1 (c+clip (1/20) x.1)-field3 1 c-a)-
      (1/4:ℝ) • (field3 1 (c+clip (1/20) y.1)-field3 1 c-a)‖ ≤ _
    rw [← smul_sub]
    have he : (field3 1 (c+clip (1/20) x.1)-field3 1 c-a)-
        (field3 1 (c+clip (1/20) y.1)-field3 1 c-a) =
        field3 1 (c+clip (1/20) x.1)-field3 1 (c+clip (1/20) y.1) := by abel
    rw [he,norm_smul]
    norm_num
    have hg := field3_difference_box c _ _ hc (clipped_norm x.1) (clipped_norm y.1)
    have hp := clipped_difference x.1 y.1
    have hxy := norm_fst_le (x-y)
    change ‖x.1-y.1‖ ≤ ‖x-y‖ at hxy
    linarith

theorem drift_zero (c a : Vec3) : ‖drift c a 0‖ = ‖a‖/4 := by
  change max ‖(4:ℝ) • clip (1/20) (0:Vec3)‖
    ‖(1/4:ℝ) • (field3 1 (c+clip (1/20) (0:Vec3))-field3 1 c-a)‖ = _
  rw [clipped_zero]
  norm_num [norm_smul]
  ring

theorem drift_bound (c a : Vec3) (hc : (79/100:ℝ) ≤ GNC.enorm c)
    (ha : ‖a‖ ≤ (1/2500:ℝ)) (x : State) : ‖drift c a x‖ ≤ 1 := by
  apply norm_prod_le_iff.mpr
  constructor
  · change ‖(4:ℝ) • clip (1/20) x.2‖ ≤ 1
    rw [norm_smul]
    norm_num
    linarith [clipped_norm x.2]
  · change ‖(1/4:ℝ) • (field3 1 (c+clip (1/20) x.1)-field3 1 c-a)‖ ≤ 1
    rw [norm_smul]
    norm_num
    have hg := field3_difference_box c (clip (1/20) x.1) 0 hc
      (clipped_norm x.1) (by norm_num)
    simp only [add_zero,sub_zero] at hg
    have ht := norm_sub_le (field3 1 (c+clip (1/20) x.1)-field3 1 c) a
    linarith [clipped_norm x.1]

theorem drift_continuous {X : Type*} [TopologicalSpace X] (c a : X → Vec3)
    (hc : Continuous c) (ha : Continuous a) (hr : ∀ t, (79/100:ℝ) ≤ GNC.enorm (c t)) :
    Continuous (fun z : X × State => drift (c z.1) (a z.1) z.2) := by
  have hp : Continuous (fun z : X × State => c z.1+clip (1/20) z.2.1) :=
    (hc.comp continuous_fst).add
      ((clip_lipschitz (n := 3) (1/20)).continuous.comp continuous_snd.fst)
  have hg : Continuous (fun z : X × State => field3 1 (c z.1+clip (1/20) z.2.1)) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    apply (field3_continuousAt 1 (by
      have h := shift_radius (c z.1) _ (hr z.1) (clipped_norm z.2.1)
      linarith)).comp hp.continuousAt
  have hg₀ : Continuous (fun z : X × State => field3 1 (c z.1)) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    exact (field3_continuousAt 1 (by linarith [hr z.1])).comp (hc.comp continuous_fst).continuousAt
  have hf : Continuous (fun z : X × State => (4:ℝ) • clip (1/20) z.2.2) :=
    ((clip_lipschitz (n := 3) (1/20)).continuous.comp continuous_snd.snd).const_smul (4:ℝ)
  exact hf.prodMk
    (((hg.sub hg₀).sub (ha.comp continuous_fst)).const_smul (1/4:ℝ))

theorem drift_eq (c a : Vec3) {x : State} (hx : ‖x‖ ≤ (1/20:ℝ)) :
    drift c a x = ((4:ℝ) • x.2,(1/4:ℝ) • (field3 1 (c+x.1)-field3 1 c-a)) := by
  have hp : clip (1/20) x.1 = x.1 := clip_eq (fun i => by
    have h := (norm_le_pi_norm x.1 i).trans ((norm_fst_le x).trans hx)
    simpa only [Real.norm_eq_abs,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using h)
  have hv : clip (1/20) x.2 = x.2 := clip_eq (fun i => by
    have h := (norm_le_pi_norm x.2 i).trans ((norm_snd_le x).trans hx)
    simpa only [Real.norm_eq_abs,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using h)
  simp only [drift,hp,hv]

end GNC.Applications.OrbitalFuel.ChaserExtension
