import GNC.Dynamics.OrbitalLogTube
import GNC.Analysis.ApproximateLinearTube

/-! Full physical orbital equations to a tube using an inexact propagator.
The generator defect is charged explicitly. No exact fundamental solution
of the retained orbital dynamics is assumed. Physical trajectories, a C1
log lift, an invertible differentiable candidate, and certified integral gains
remain explicit hypotheses. The candidate region is a conclusion, not a premise.
-/
noncomputable section
open Set MeasureTheory
namespace GNC.OrbitalApproximateTube
open OrbitalNearAffine OrbitalLogTube

/-- Approximate STM, full gravity, and exact physical reconstruction. -/
theorem certificate (C : Coordinates) (μ : ℝ) (hμ : 0≤μ)
    (X Y : ℝ → SE23) (x dx ν : ℝ → LogState)
    (Ψ : ℝ → Endˣ) (B : ℝ → End) (e : ℝ → ℝ) {T a d b r D p α w : ℝ}
    (hT : 0≤T) (ha : 0<a) (hd0 : 0≤d) (hd1 : d<1) (hb : 0≤b)
    (hsmall : 4*a*b<(1-d)^2)
    (hp : 0≤p) (hα : 0≤α) (hw : 0≤w)
    (hD : D<r) (hposDomain : p*(2*(a/(1-d)))≤D) (hangDomain : α*(2*(a/(1-d)))≤1)
    (hscalep : ∀ z, enorm (C z 0)≤p*‖z‖)
    (hscaleα : ∀ z, enorm (C z 2)≤α*‖z‖)
    (hscalew : ∀ v, ‖C.symm (velocityOnly v)‖≤w*enorm v)
    (hq : ∀ t ∈ Icc 0 T, r≤enorm (Y t).pos)
    (hx : Continuous x) (hdx : Continuous dx)
    (hd : ∀ t ∈ Icc 0 T, HasDerivAt x (dx t) t)
    (hX : ∀ t ∈ Icc 0 T, HasDerivAt (fun s => SE23.toMatrix (X s))
      (spacecraftDerivative (X t) (ν t) (Gravity.field3 μ (X t).pos)) t)
    (hY : ∀ t ∈ Icc 0 T, HasDerivAt (fun s => SE23.toMatrix (Y s))
      (spacecraftDerivative (Y t) (ν t) (Gravity.field3 μ (Y t).pos)) t)
    (he : ∀ t, SE23.error (Y t) (X t)=groupExp (x t))
    (hB : Continuous B) (hec : Continuous e)
    (he0 : ∀ t ∈ Icc 0 T, 0≤e t)
    (hA : Continuous (fun t => scaledOperator C μ (Y t) (ν t)))
    (hc : Continuous (fun t => coefficient μ r D p α w (Y t).pos))
    (hΨ : ∀ t, HasDerivAt (fun s => (Ψ s).val)
      (B t*(Ψ t).val) t)
    (hdefect : ∀ t ∈ Icc 0 T, ‖scaledOperator C μ (Y t) (ν t)-B t‖≤e t)
    (hegain : ∀ t ∈ Icc 0 T,
      (∫ s in 0..t, ‖NearLinearTube.kernel Ψ t s‖*e s)≤d)
    (hΨ₀ : Ψ 0=1) (hi : ‖C.symm (x 0)‖≤a)
    (hlin : ∀ t ∈ Icc 0 T, ‖(Ψ t).val (C.symm (x 0))‖≤a)
    (hgain : ∀ t ∈ Icc 0 T,
      (∫ s in 0..t, ‖NearLinearTube.kernel Ψ t s‖*
        coefficient μ r D p α w (Y s).pos)≤b) :
    ∀ t ∈ Icc 0 T,
      ‖C.symm (x t)‖≤LinearQuadraticTube.radius a d b ∧
      ‖C.symm (x t)-(Ψ t).val (C.symm (x 0))‖≤d*LinearQuadraticTube.radius a d b+b*(LinearQuadraticTube.radius a d b)^2 ∧
      enorm (x t 2)≤1 ∧ enorm ((X t).pos-(Y t).pos)≤D := by
  let z : ℝ → LogState := fun t => C.symm (x t)
  let A : ℝ → End := fun t => scaledOperator C μ (Y t) (ν t)
  let res : ℝ → LogState := fun t => C.symm (dx t)-A t (z t)
  have hz : Continuous z := C.symm.continuous.comp hx
  have hr : Continuous res := (C.symm.continuous.comp hdx).sub (hA.clm_apply hz)
  have hode (t : ℝ) (ht : t ∈ Icc 0 T) : HasDerivAt z (A t (z t)+res t) t := by
    simpa [res] using C.symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t (hd t ht)
  have hrem (t : ℝ) (ht : t ∈ Icc 0 T) (hzr : ‖z t‖≤2*(a/(1-d))) :
      ‖res t‖≤coefficient μ r D p α w (Y t).pos*‖z t‖^2 := by
    have hpD := (mul_le_mul_of_nonneg_left hzr hp).trans hposDomain
    have hαD := (mul_le_mul_of_nonneg_left hzr hα).trans hangDomain
    have hxangle : enorm (x t 2)≤1 := by
      simpa [z] using (hscaleα (z t)).trans hαD
    have heq := log_equation μ (hX t ht) (hY t ht) (hd t ht) he
      (hxangle.trans_lt (by linarith [Real.pi_gt_three]))
    have hre := scaled_equation C μ (Y t) (ν t) (x t) (dx t) heq
    change res t=_ at hre
    rw [hre]
    simpa [z] using scaled_residual_bound C μ hμ (Y t).rot (Y t).pos (z t)
      hp hα hw hD (hq t ht) (hscalep _) (hscaleα _) hscalew hpD hαD
  have result := ApproximateLinearTube.certificate Ψ A B hΨ hΨ₀ z res e
    (fun t => coefficient μ r D p α w (Y t).pos) hT ha hd0 hd1 hb hsmall hz hr hA hB hec hc hode
    he0 (fun t _ => coefficient_nonneg hμ hp hα hw _) hi hlin hdefect hrem hegain hgain
  intro t ht
  obtain ⟨htotal, herr⟩ := result t ht
  have hz2 : ‖z t‖≤2*(a/(1-d)) := htotal.trans (LinearQuadraticTube.properties ha hd1 hb hsmall).2.1.le
  have hang : enorm (x t 2)≤1 := by
    simpa [z] using (hscaleα (z t)).trans
      ((mul_le_mul_of_nonneg_left hz2 hα).trans hangDomain)
  refine ⟨htotal, herr, hang, ?_⟩
  have hpos : enorm (x t 0)≤D := by
    simpa [z] using (hscalep (z t)).trans
      ((mul_le_mul_of_nonneg_left hz2 hp).trans hposDomain)
  rw [reconstruction (he t)]
  simpa only [SE23.mul_pos, groupExp, add_sub_cancel_left, rotate_enorm] using
    (leftAt_nonexpansive (x t 2) (x t 0) (by linarith [Real.pi_gt_three])).trans hpos

end GNC.OrbitalApproximateTube
