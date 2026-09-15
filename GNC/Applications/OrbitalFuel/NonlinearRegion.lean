import GNC.Applications.OrbitalFuel.GravityPrefixBound
import GNC.Control.IntegralTube

/-! Close a continuous solar-chaser region using the complete gravity
remainder, rather than assuming the computed trajectories stay in it.
All constants and SI conversions are checked with exact arithmetic.
-/
noncomputable section
namespace GNC.Applications.OrbitalFuel.SolarRegion
open GNC GNC.ThrustSupport PolynomialOrbit PolynomialOrbitTransition RetainedPhysical Matrix Set
set_option autoImplicit false

def proposedPosition : ℝ := 10130000
def normalizedPosition : ℝ := proposedPosition/(RetainedNorm.lengthScale:ℝ)
def gravityReserve : ℝ := 3*normalizedPosition^2/(7997/10000-normalizedPosition)^4

theorem length_pos : 0 < (RetainedNorm.lengthScale:ℝ) := by norm_num [RetainedNorm.lengthScale]
theorem separation : normalizedPosition < 7997/10000 := by
  norm_num [normalizedPosition,proposedPosition,RetainedNorm.lengthScale]
theorem gravityReserve_nonneg : 0 ≤ gravityReserve := by
  unfold gravityReserve
  positivity

theorem position_allowance : (RetainedNorm.lengthScale:ℝ)*(9/14)*gravityReserve ≤ 3250 := by
  norm_num [gravityReserve,normalizedPosition,proposedPosition,RetainedNorm.lengthScale]

theorem velocity_allowance : SolarSensitivityFuel.speed*(15/7)*gravityReserve ≤ 11/5000 := by
  have hs : SolarSensitivityFuel.speed ≤ 29785 :=
    RetainedNorm.speed_upper.trans (by norm_num [RetainedNorm.speedUpper])
  have h := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hs (by norm_num : (0:ℝ) ≤ 15/7)) gravityReserve_nonneg
  exact h.trans (by
    norm_num [gravityReserve,normalizedPosition,proposedPosition,RetainedNorm.lengthScale])

theorem normalized_position (x : Vec3)
    (hx : GNC.enorm ((RetainedNorm.lengthScale:ℝ) • x) ≤ proposedPosition) :
    GNC.enorm x ≤ normalizedPosition := by
  unfold normalizedPosition
  apply (le_div_iff₀ length_pos).mpr
  simpa only [enorm_smul,abs_of_pos length_pos,mul_comm] using hx

/-- The acceleration remainder is bounded throughout the proposed prefix;
its full reference-dependent transport fits explicit SI allowances. -/
theorem prefix_gravity_si (w : ℝ → Fin 4 → ℝ) (p : ℝ → Vec3)
    (F : ℝ → Matrix (Fin 4) (Fin 4) ℝ) (H : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hw : Continuous w) (hp : Continuous p) (hF : Continuous F) (hH : Continuous H)
    (hdw : ∀ t ∈ Icc (0:ℝ) (3/5), HasDerivAt w
      (physicalRate (PolynomialTransition.alpha:ℝ) (w t)) t)
    (hdF : ∀ t ∈ Icc (0:ℝ) (3/5), HasDerivAt F (planeGenerator (lift (w t))*F t) t)
    (hdH : ∀ t ∈ Icc (0:ℝ) (3/5), HasDerivAt H (normalGenerator (lift (w t))*H t) t)
    (hiw : w 0 = ![4/5,0,0,Real.sqrt (3/2)]) (hiF : F 0 = 1) (hiH : H 0 = 1)
    {T : ℝ} (hT : T ∈ Icc (0:ℝ) (3/5))
    (hprefix : ∀ s ∈ Icc (0:ℝ) T,
      GNC.enorm ((RetainedNorm.lengthScale:ℝ) • (p s-position (w s))) ≤ proposedPosition) :
    GNC.enorm ((RetainedNorm.lengthScale:ℝ) •
      remainder F H (fun s => PlanarChaserError.residual (w s) (p s)) T 0) ≤ 3250 ∧
    GNC.enorm (SolarSensitivityFuel.speed •
      remainder F H (fun s => PlanarChaserError.residual (w s) (p s)) T 1) ≤ 11/5000 := by
  have hr := Reference.physical_solar_annulus w hw hdw hiw
  have hrad (s : ℝ) (hs : s ∈ Icc (0:ℝ) (3/5)) : 7997/10000 ≤ radius (w s) :=
    (hr s hs).1.le
  have hdom (s : ℝ) (hs : s ∈ Icc (0:ℝ) T) : s ∈ Icc (0:ℝ) (3/5) :=
    ⟨hs.1,hs.2.trans hT.2⟩
  have hc := PlanarChaserError.residual_continuousOn hw.continuousOn hp.continuousOn
    (fun s hs => lt_of_lt_of_le (by norm_num : (0:ℝ) < 7997/10000) (hrad s (hdom s hs)))
    (fun s hs => PlanarChaserError.chaser_nonzero (w s) (p s)
      (normalized_position _ (hprefix s hs)) (hrad s (hdom s hs)) separation)
  have hb := gravity_prefix_bound w F H (fun s => PlanarChaserError.residual (w s) (p s))
    gravityReserve_nonneg hT hF hH hc hrad hdF hdH hiF hiH
    (fun s hs => PlanarChaserError.residual_bound (w s) (p s)
      (normalized_position _ (hprefix s hs)) (hrad s (hdom s hs)) separation)
  constructor
  · rw [enorm_smul,abs_of_pos length_pos]
    exact (mul_le_mul_of_nonneg_left hb.1 length_pos.le).trans (by
      simpa only [mul_assoc] using position_allowance)
  · rw [enorm_smul,abs_of_pos SolarSensitivityFuel.speed_pos]
    exact (mul_le_mul_of_nonneg_left hb.2 SolarSensitivityFuel.speed_pos.le).trans (by
      simpa only [mul_assoc] using velocity_allowance)

section Motion
variable (w : ℝ → Fin 4 → ℝ) (p v : ℝ → Vec3)
    (F : ℝ → Matrix (Fin 4) (Fin 4) ℝ) (H : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (q : Vec3)
    (hw : Continuous w) (hp : Continuous p) (hv : Continuous v)
    (hF : Continuous F) (hH : Continuous H)
    (hr : ∀ t, 0 < radius (w t))
    (hn : ∀ t ∈ Icc (0:ℝ) (3/5), p t ≠ 0)
    (hdw : ∀ t ∈ Icc (0:ℝ) (3/5), HasDerivAt w
      (physicalRate (PolynomialTransition.alpha:ℝ) (w t)) t)
    (hdF : ∀ t ∈ Icc (0:ℝ) (3/5), HasDerivAt F (planeGenerator (lift (w t))*F t) t)
    (hdH : ∀ t ∈ Icc (0:ℝ) (3/5), HasDerivAt H (normalGenerator (lift (w t))*H t) t)
    (hiw : w 0 = ![4/5,0,0,Real.sqrt (3/2)]) (hiF : F 0 = 1) (hiH : H 0 = 1)
    (hip : PlanarChaserError.plane (w 0) (p 0) (v 0) = TerminalResponse.initialPlane (Real.sqrt (3/2)))
    (hin : PlanarChaserError.normal (p 0) (v 0) = TerminalResponse.initialNormal)
    (hdp : ∀ k < 37, ∀ t ∈ Ioo (BurnSchedule.time k:ℝ) (BurnSchedule.time (k+1):ℝ),
      HasDerivAt p (v t) t)
    (hdv : ∀ k < 37, ∀ t ∈ Ioo (BurnSchedule.time k:ℝ) (BurnSchedule.time (k+1):ℝ),
      HasDerivAt v (Gravity.field3 1 (p t)+BurnSchedule.input
        (fun j t => ChaserResponse.acceleration (RetainedPrefix.beta:ℝ) (lift (w t)) (commands q j)) k t) t)
    (hq : q ∈ Cap SharedBiasExample.axis SharedBiasCertificates.Solar.kappa)

include hw hp hv hF hH hr hn hdw hdF hdH hiw hiF hiH hip hin hdp hdv hq in
/-- All-time nonlinear enclosure for every common cap direction and every
existing physical trajectory with the specified initial data and burn ODE.
No position-tube or transported-remainder bound is assumed. Existence and
continuation of the noncolliding physical trajectory remain explicit.
-/
theorem continuous_nonlinear_enclosure :
    ∀ T ∈ Icc (0:ℝ) (3/5),
      GNC.enorm ((RetainedNorm.lengthScale:ℝ) • (p T-position (w T))) ≤ 10126251 ∧
      GNC.enorm (SolarSensitivityFuel.speed • (v T-velocity (w T))) ≤ 5122201/1000000 ∧
      GNC.enorm ((RetainedNorm.lengthScale:ℝ) •
        remainder F H (fun s => PlanarChaserError.residual (w s) (p s)) T 0) ≤ 3250 ∧
      GNC.enorm (SolarSensitivityFuel.speed •
        remainder F H (fun s => PlanarChaserError.residual (w s) (p s)) T 1) ≤ 11/5000 := by
  have hb (T : ℝ) (hT : T ∈ Icc (0:ℝ) (3/5)) :=
    nonlinear_enclosure w p v F H q hw hp hv hF hH hr hn hdw hdF hdH hiF hiH hip hin hdp hdv hT hiw hq
  have hc : Continuous (fun t => position (w t)) := by
    apply continuous_pi
    intro i
    fin_cases i <;> simp [position,Matrix.cons_val_two] <;> fun_prop
  have hf : Continuous (fun t => GNC.enorm ((RetainedNorm.lengthScale:ℝ) • (p t-position (w t)))) :=
    enorm_continuous.comp (continuous_const.smul (hp.sub hc))
  have hi : GNC.enorm ((RetainedNorm.lengthScale:ℝ) • (p 0-position (w 0))) < proposedPosition := by
    have h0 := (hb 0 (by norm_num)).1
    have hz : GNC.enorm (0 : Vec3) = 0 := (enorm_eq_zero_iff _).mpr rfl
    simp only [remainder_initial,smul_zero,hz,add_zero] at h0
    exact h0.trans_lt (by norm_num [proposedPosition])
  have hclose (T : ℝ) (hT : T ∈ Icc (0:ℝ) (3/5))
      (hprefix : ∀ s ∈ Icc (0:ℝ) T,
        GNC.enorm ((RetainedNorm.lengthScale:ℝ) • (p s-position (w s))) ≤ proposedPosition) :
      GNC.enorm ((RetainedNorm.lengthScale:ℝ) • (p T-position (w T))) < proposedPosition := by
    have hg := prefix_gravity_si w p F H hw hp hF hH hdw hdF hdH hiw hiF hiH hT hprefix
    have hh := (hb T hT).1.trans (add_le_add le_rfl hg.1)
    exact hh.trans_lt (by norm_num [proposedPosition])
  have hall := IntegralTube.prefix_closure hf hi hclose
  intro T hT
  have hg := prefix_gravity_si w p F H hw hp hF hH hdw hdF hdH hiw hiF hiH hT
    (fun s hs => (hall s ⟨hs.1,hs.2.trans hT.2⟩).le)
  refine ⟨(hb T hT).1.trans ?_,(hb T hT).2.trans ?_,hg⟩
  · linarith [hg.1]
  · linarith [hg.2]

end Motion
end GNC.Applications.OrbitalFuel.SolarRegion
