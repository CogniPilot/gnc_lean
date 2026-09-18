import GNC.Dynamics.CandidateOrbitExistence

/-! Nonvacuity of an initial uncertainty family: every permitted initial
position and velocity has a full-horizon solution of the unclipped field. -/
noncomputable section
namespace GNC.Gravity
open Set EuclideanClip

theorem exists_near_initial_shift {μ scale r D L : ℝ} {R : ℚ}
    (hμ : 0≤μ) (hs : 0≤scale) (hr : 0<r) (hR : 0≤R) (hL : 0≤L)
    (hgain : scale*(2*μ/r^3)≤1)
    (q qv qa thrust : ℝ → E3)
    (hq : Continuous q) (hv : Continuous qv) (ha : Continuous qa) (hu : Continuous thrust)
    (hdq : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt q (qv t) t)
    (hdv : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt qv (qa t) t)
    (hregion : ∀ t ∈ Icc (0:ℝ) 1, r+2*(R:ℝ)+L≤‖q t‖)
    (hD : 0≤D)
    (hdefect : ∀ t ∈ Icc (0:ℝ) 1, ‖scale • (field μ (q t)+thrust t)-qa t‖≤D)
    (hclose : 4*(D+L)≤(R:ℝ)) (a b : E3) (hab : ‖a‖+‖b‖≤L) :
    ∃ p v : ℝ → E3, Continuous p ∧ Continuous v ∧ p 0=q 0+a ∧ v 0=qv 0+b ∧
      (∀ t ∈ Icc (0:ℝ) 1, HasDerivAt p (v t) t) ∧
      (∀ t ∈ Icc (0:ℝ) 1, HasDerivAt v (scale • (field μ (p t)+thrust t)) t) ∧
      ∀ t ∈ Icc (0:ℝ) 1, r≤‖p t‖ := by
  have hRr : (0:ℝ)≤R := by exact_mod_cast hR
  have hshift (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : ‖a+t • b‖≤L := by
    calc
      _ ≤ ‖a‖+‖t • b‖ := norm_add_le _ _
      _ = ‖a‖+t*‖b‖ := by rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1]
      _ ≤ ‖a‖+‖b‖ := by nlinarith [ht.2,norm_nonneg b]
      _ ≤ L := hab
  have hbound (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      ‖scale • (field μ (q t+(a+t • b))+thrust t)-qa t‖≤D+L := by
    have hg := field_difference_ball μ hμ (q t) (a+t • b) 0 hr
      (show r+L≤‖q t‖ by linarith [hregion t ht]) (hshift t ht) (by simpa using hL)
    simp only [add_zero,sub_zero] at hg
    have hscaled : ‖scale • (field μ (q t+(a+t • b))-field μ (q t))‖≤L := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hs]
      have hh := mul_le_mul_of_nonneg_left hg hs
      have hh' := mul_le_mul_of_nonneg_right hgain (norm_nonneg (a+t • b))
      nlinarith [hshift t ht]
    have hid : scale • (field μ (q t+(a+t • b))+thrust t)-qa t =
        scale • (field μ (q t+(a+t • b))-field μ (q t))+
          (scale • (field μ (q t)+thrust t)-qa t) := by module
    rw [hid]
    exact (norm_add_le _ _).trans (by linarith [hdefect t ht])
  obtain ⟨p,v,hp,hv',hip,hiv,hdp,hdv',hfloor⟩ := exists_near_candidate hμ hs hr hR hgain
    (fun t => q t+(a+t • b)) (fun t => qv t+b) qa thrust
    (hq.add (continuous_const.add (continuous_id.smul continuous_const)))
    (hv.add continuous_const) ha hu
    (fun t ht => by simpa using (hdq t ht).add ((hasDerivAt_id t).smul_const b |>.const_add a))
    (fun t ht => (hdv t ht).add_const b)
    (by intro t ht
        have hn := norm_sub_le (q t+(a+t • b)) (a+t • b)
        simp only [add_sub_cancel_right] at hn
        linarith [hregion t ht,hshift t ht])
    (add_nonneg hD hL) hbound hclose
  exact ⟨p,v,hp,hv',by simpa using hip,hiv,hdp,hdv',hfloor⟩

end GNC.Gravity
