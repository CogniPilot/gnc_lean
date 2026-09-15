import GNC.Dynamics.ForcedOrbitExistence

/-! A longer-horizon existence certificate using velocity divided by two
in the construction norm. It permits gravity gain four instead of one.
The coarse construction radius is not added to later prediction errors. -/
noncomputable section
namespace GNC.ForcedOrbitExistence
open Set EuclideanClip
open scoped NNReal

/-- The factor ten follows from exp(4) < 81 in the rescaled-state Grönwall
argument. It is an explicit sufficient existence condition, not a numerical
error allowance. The returned state obeys the original physical ODE. -/
theorem exists_relative_four_gain {μ scale r : ℝ} {R : ℚ}
    (hμ : 0≤μ) (hs : 0≤scale) (hr : 0<r) (hR : 0≤R)
    (hgain : (scale/4)*(2*μ/r^3)≤1)
    (c d : ℝ → E3) (hc : Continuous c) (hd : Continuous d)
    (hregion : ∀ t, r+2*(R:ℝ)≤‖c t‖) {D : ℝ} (hD : 0≤D)
    (hforce : ∀ t, ‖d t‖≤D) (hclose : 10*D≤(R:ℝ)) :
    ∃ x : ℝ → State, Continuous x ∧ x 0=0 ∧
      (∀ t ∈ Icc (0:ℝ) 1, r≤‖c t+(x t).1‖) ∧
      ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt x (rate μ scale (c t) (d t) (x t)) t := by
  have hs4 : 0≤scale/4 := by positivity
  have hRr : (0:ℝ)≤R := by exact_mod_cast hR
  let d4 := fun t => (1/4:ℝ) • d t
  have hd4 : Continuous d4 := hd.const_smul _
  have hb4 (t : ℝ) : ‖d4 t‖≤D/4 := by
    dsimp [d4]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<1/4)]
    nlinarith [hforce t]
  let f := fun t x => (2:ℝ) • extension μ (scale/4) R (c t) (d4 t) x
  have hfK (t : ℝ) : LipschitzWith 4 (f t) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have h := (extension_lipschitz hμ hs4 hr hR hgain (c t) (d4 t) (hregion t)).dist_le_mul x y
    simp only [f,dist_eq_norm,← smul_sub,norm_smul,Real.norm_eq_abs,
      abs_of_pos (by norm_num : (0:ℝ)<2),NNReal.coe_ofNat] at *
    linarith
  have hfc : Continuous (fun z : ℝ × State => f z.1 z.2) :=
    (extension_continuous hr hR c d4 hc hd4 hregion).const_smul _
  let L : ℝ≥0 := ⟨4*(R:ℝ)+D/2,by positivity⟩
  have hfb (t : ℝ) (x : State) : ‖f t x‖≤L := by
    have h := extension_bound hμ hs4 hr hR hgain (c t) (d4 t) (hregion t) (hb4 t) x
    dsimp [f,L]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<2)]
    linarith
  obtain ⟨y,hy,hy0,hyd⟩ := BoundedODE.exists_time_dependent f 4 L hfK hfc hfb
    0 (by norm_num : (0:ℝ)≤1)
  have hgrowth (t : ℝ) : ‖f t (y t)‖≤4*‖y t‖+D/2 := by
    have hl := (hfK t).dist_le_mul (y t) 0
    rw [dist_eq_norm,dist_zero_right] at hl
    have hz : ‖f t 0‖≤D/2 := by
      dsimp [f]
      rw [extension_zero hR,norm_smul,Real.norm_eq_abs]
      norm_num only [abs_of_pos (by norm_num : (0:ℝ)<2),Prod.norm_mk,
        norm_zero,max_eq_right (norm_nonneg _)]
      linarith [hb4 t]
    have hh := norm_le_norm_sub_add (f t (y t)) (f t 0)
    norm_num only [NNReal.coe_ofNat] at hl
    linarith
  have hb : ∀ t ∈ Icc (0:ℝ) 1, ‖y t‖≤10*D := by
    have hg := norm_le_gronwallBound_of_norm_deriv_right_le
      (a := 0) (b := 1) (δ := 0) (K := 4) (ε := D/2) hy.continuousOn
      (fun t ht => (hyd t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
      (by simp [hy0]) (fun t _ => hgrowth t)
    intro t ht
    have he : Real.exp (4*t)≤81 := by
      calc
        Real.exp (4*t)≤Real.exp (4:ℝ) := Real.exp_le_exp.mpr (by linarith [ht.2])
        _ = (Real.exp 1)^4 := by simpa using Real.exp_nat_mul (1:ℝ) 4
        _ ≤ 3^4 := pow_le_pow_left₀ (Real.exp_pos _).le Real.exp_one_lt_three.le _
        _ = 81 := by norm_num
    have hh := hg t ht
    norm_num [gronwallBound] at hh
    nlinarith [mul_le_mul_of_nonneg_left he hD]
  have hi (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      clip R (y t).1=(y t).1 ∧ clip R (y t).2=(y t).2 :=
    ⟨eq_self ((norm_fst_le (y t)).trans ((hb t ht).trans hclose)),
      eq_self ((norm_snd_le (y t)).trans ((hb t ht).trans hclose))⟩
  refine ⟨fun t => ((y t).1,(2:ℝ) • (y t).2),hy.fst.prodMk (hy.snd.const_smul _),
    by simp [hy0],?_,?_⟩
  · intro t ht
    have hh : ‖c t‖≤‖c t+(y t).1‖+‖(y t).1‖ := by
      simpa only [add_sub_cancel_right] using norm_sub_le (c t+(y t).1) (y t).1
    have hp := (norm_fst_le (y t)).trans ((hb t ht).trans hclose)
    dsimp
    linarith [hregion t]
  · intro t ht
    have hp := (ContinuousLinearMap.fst ℝ E3 E3).hasFDerivAt.comp_hasDerivAt t (hyd t ht)
    have hv := (ContinuousLinearMap.snd ℝ E3 E3).hasFDerivAt.comp_hasDerivAt t (hyd t ht)
    have h := hp.prodMk (hv.const_smul (2:ℝ))
    convert h using 1
    dsimp [f,rate,extension,d4]
    rw [(hi t ht).1,(hi t ht).2]
    congr 1 <;> module

end GNC.ForcedOrbitExistence
