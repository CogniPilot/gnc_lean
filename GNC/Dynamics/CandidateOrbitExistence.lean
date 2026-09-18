import GNC.Dynamics.ForcedOrbitExistence

/-! A bounded candidate defect constructs a nonsingular physical trajectory
with the candidate's actual initial position and velocity. The initial state
need not agree with an auxiliary nominal trajectory. Clamping extends only
the existence problem; no clamp is active in the returned physical ODE. -/
noncomputable section
namespace GNC.Gravity
open Set EuclideanClip

theorem exists_near_candidate {μ scale r D : ℝ} {R : ℚ}
    (hμ : 0≤μ) (hs : 0≤scale) (hr : 0<r) (hR : 0≤R)
    (hgain : scale*(2*μ/r^3)≤1)
    (q qv qa thrust : ℝ → E3)
    (hq : Continuous q) (hv : Continuous qv) (ha : Continuous qa) (hu : Continuous thrust)
    (hdq : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt q (qv t) t)
    (hdv : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt qv (qa t) t)
    (hregion : ∀ t ∈ Icc (0:ℝ) 1, r+2*(R:ℝ)≤‖q t‖)
    (hD : 0≤D)
    (hdefect : ∀ t ∈ Icc (0:ℝ) 1, ‖scale • (field μ (q t)+thrust t)-qa t‖≤D)
    (hclose : 4*D≤(R:ℝ)) :
    ∃ p v : ℝ → E3, Continuous p ∧ Continuous v ∧ p 0=q 0 ∧ v 0=qv 0 ∧
      (∀ t ∈ Icc (0:ℝ) 1, HasDerivAt p (v t) t) ∧
      (∀ t ∈ Icc (0:ℝ) 1, HasDerivAt v (scale • (field μ (p t)+thrust t)) t) ∧
      ∀ t ∈ Icc (0:ℝ) 1, r≤‖p t‖ := by
  let clamp : ℝ → ℝ := fun t => max 0 (min 1 t)
  have hc : Continuous clamp := continuous_const.max (continuous_const.min continuous_id)
  have hi (t : ℝ) : clamp t ∈ Icc (0:ℝ) 1 := by
    exact ⟨le_max_left _ _,max_le (by norm_num) (min_le_left _ _)⟩
  have he (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : clamp t=t := by
    simp only [clamp,min_eq_right ht.2,max_eq_right ht.1]
  let c : ℝ → E3 := q ∘ clamp
  let d : ℝ → E3 := fun t => scale • (field μ (c t)+thrust (clamp t))-qa (clamp t)
  have hcc : Continuous c := hq.comp hc
  have hcr (t : ℝ) : r+2*(R:ℝ)≤‖c t‖ := hregion _ (hi t)
  have hRr : (0:ℝ)≤R := by exact_mod_cast hR
  have hcn (t : ℝ) : c t ≠ 0 := norm_pos_iff.mp (by linarith [hcr t])
  have hcg : Continuous (fun t => field μ (c t)) := by
    unfold field
    exact (continuous_const.div (hcc.norm.pow 3)
      (fun t => pow_ne_zero 3 (norm_ne_zero_iff.mpr (hcn t)))).smul hcc
  have hdc : Continuous d := ((hcg.add (hu.comp hc)).const_smul scale).sub (ha.comp hc)
  obtain ⟨e,hec,he0,_,her,hed⟩ := ForcedOrbitExistence.exists_relative
    hμ hs hr hR hgain c d hcc hdc hcr hD (fun t => hdefect _ (hi t)) hclose
  refine ⟨(fun t => q t+(e t).1),(fun t => qv t+(e t).2),
    hq.add hec.fst,hv.add hec.snd,?_,?_,?_,?_,?_⟩
  · simp only [he0,Prod.fst_zero,add_zero]
  · simp only [he0,Prod.snd_zero,add_zero]
  · intro t ht
    exact (hdq t ht).add (hed t ht).fst
  · intro t ht
    convert (hdv t ht).add (hed t ht).snd using 1
    dsimp [ForcedOrbitExistence.rate,d,c,Function.comp_def]
    rw [he t ht]
    module
  · intro t ht
    simpa only [c,Function.comp_apply,he t ht] using her t ht

end GNC.Gravity
