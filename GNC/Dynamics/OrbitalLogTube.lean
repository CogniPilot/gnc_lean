import GNC.Dynamics.OrbitalNearAffine
import GNC.Analysis.NearLinearTube

/-! Physical spacecraft trajectories to a certified, non-iterative log tube.

C maps dimensionless certificate coordinates to the paper's (p,v,phi)
log coordinates. Its fixed position/angle/output gains are verified linear
map bounds, not fitted nonlinear allowances. A trajectory and a C1 log lift
are supplied; their validity region is proved by the quadratic closure.
No global existence, floating-point STM, or input-mismatch claim is made.
-/
noncomputable section
open Set MeasureTheory
namespace GNC.OrbitalLogTube
open OrbitalNearAffine

abbrev End := LogState →L[ℝ] LogState
abbrev Coordinates := LogState ≃L[ℝ] LogState

def scaledOperator (C : Coordinates) (μ : ℝ) (Y : SE23) (ν : LogState) : End :=
  C.symm.toContinuousLinearMap * operator μ Y.rot Y.pos ν * C.toContinuousLinearMap

def coefficient (μ r D positionScale angleScale outputScale : ℝ) (q : Vec3) : ℝ :=
  outputScale*(2*(μ/enorm q^3)*angleScale*positionScale+
    (4*μ/(r-D)^4)*positionScale^2)

theorem coefficient_nonneg {μ r D p α w : ℝ} (hμ : 0≤μ) (hp : 0≤p)
    (hα : 0≤α) (hw : 0≤w) (q : Vec3) :
    0≤coefficient μ r D p α w q := by
  unfold coefficient
  have := enorm_nonneg q
  positivity

theorem scaled_residual_bound (C : Coordinates) (μ : ℝ) (hμ : 0≤μ)
    (R : SO3) (q : Vec3) (z : LogState) {r D p α w : ℝ}
    (hp : 0≤p) (hα : 0≤α) (hw : 0≤w) (hD : D<r) (hq : r≤enorm q)
    (hpos : enorm (C z 0)≤p*‖z‖) (hang : enorm (C z 2)≤α*‖z‖)
    (hout : ∀ v, ‖C.symm (velocityOnly v)‖≤w*enorm v)
    (hpd : p*‖z‖≤D) (had : α*‖z‖≤1) :
    ‖C.symm (velocityOnly (residual μ R q (C z)))‖ ≤
      coefficient μ r D p α w q * ‖z‖^2 := by
  have hb := residual_bound μ hμ R q (C z) hD hq (hpos.trans hpd) (hang.trans had)
  have hn := enorm_nonneg q
  have hp0 := enorm_nonneg (C z 0)
  have ha0 := enorm_nonneg (C z 2)
  have h1 : 2*(μ/enorm q^3)*enorm (C z 2)*enorm (C z 0) ≤
      2*(μ/enorm q^3)*(α*‖z‖)*(p*‖z‖) := by gcongr
  have h2 : (4*μ/(r-D)^4)*enorm (C z 0)^2 ≤
      (4*μ/(r-D)^4)*(p*‖z‖)^2 := by gcongr
  exact (hout _).trans ((mul_le_mul_of_nonneg_left
    (hb.trans (add_le_add h1 h2)) hw).trans_eq (by unfold coefficient; ring))

/-- Exact pullback of the retained physical linear operator. -/
theorem scaled_equation (C : Coordinates) (μ : ℝ) (Y : SE23) (ν x dx : LogState)
    (h : dx=operator μ Y.rot Y.pos ν x+velocityOnly (residual μ Y.rot Y.pos x)) :
    C.symm dx-scaledOperator C μ Y ν (C.symm x)=
      C.symm (velocityOnly (residual μ Y.rot Y.pos x)) := by
  rw [h, map_add]
  simp [scaledOperator, ContinuousLinearMap.mul_apply]

/-- The endpoint and all intermediate times are enclosed. The two small
domain checks turn the *proposed* radius into valid gravity/chart bounds;
no assumption that the actual trajectory stays in that radius is used.
The field and input may vary arbitrarily along the known reference.

The C1 lift is an existence/regularity hypothesis, not a pre-assumed bound.
The STM is exact and normalized; computed approximations need separately
checked defects before they can replace this STM.
-/
theorem certificate (C : Coordinates) (μ : ℝ) (hμ : 0≤μ)
    (X Y : ℝ → SE23) (x dx ν : ℝ → LogState)
    (Φ : ℝ → Endˣ) {T a b r D p α w : ℝ}
    (hT : 0≤T) (ha : 0<a) (hb : 0≤b) (hsmall : 4*a*b<1)
    (hp : 0≤p) (hα : 0≤α) (hw : 0≤w)
    (hD : D<r) (hposDomain : p*(2*a)≤D) (hangDomain : α*(2*a)≤1)
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
    (hA : Continuous (fun t => scaledOperator C μ (Y t) (ν t)))
    (hc : Continuous (fun t => coefficient μ r D p α w (Y t).pos))
    (hΦ : ∀ t, HasDerivAt (fun s => (Φ s).val)
      (scaledOperator C μ (Y t) (ν t)*(Φ t).val) t)
    (hΦ₀ : Φ 0=1) (hi : ‖C.symm (x 0)‖≤a)
    (hlin : ∀ t ∈ Icc 0 T, ‖(Φ t).val (C.symm (x 0))‖≤a)
    (hgain : ∀ t ∈ Icc 0 T,
      (∫ s in 0..t, ‖NearLinearTube.kernel Φ t s‖*
        coefficient μ r D p α w (Y s).pos)≤b) :
    ∀ t ∈ Icc 0 T,
      ‖C.symm (x t)‖≤QuadraticTube.radius a b ∧
      ‖C.symm (x t)-(Φ t).val (C.symm (x 0))‖≤b*(QuadraticTube.radius a b)^2 ∧
      enorm (x t 2)≤1 ∧ enorm ((X t).pos-(Y t).pos)≤D := by
  let z : ℝ → LogState := fun t => C.symm (x t)
  let A : ℝ → End := fun t => scaledOperator C μ (Y t) (ν t)
  let res : ℝ → LogState := fun t => C.symm (dx t)-A t (z t)
  have hz : Continuous z := C.symm.continuous.comp hx
  have hr : Continuous res := (C.symm.continuous.comp hdx).sub (hA.clm_apply hz)
  have hode (t : ℝ) (ht : t ∈ Icc 0 T) : HasDerivAt z (A t (z t)+res t) t := by
    simpa [res] using C.symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t (hd t ht)
  have hrem (t : ℝ) (ht : t ∈ Icc 0 T) (hzr : ‖z t‖≤2*a) :
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
  have result := NearLinearTube.certificate Φ A hΦ hΦ₀ z res
    (fun t => coefficient μ r D p α w (Y t).pos) hT ha hb hsmall hz hr hc hode
    (fun t _ => coefficient_nonneg hμ hp hα hw _) hi hlin hrem hgain
  intro t ht
  obtain ⟨htotal, herr⟩ := result t ht
  have hz2 : ‖z t‖≤2*a := htotal.trans (QuadraticTube.radius_properties ha hb hsmall).2.1.le
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

/-- Non-polynomial physical reachable enclosure: retain the exponential
map instead of enclosing its Cartesian Taylor coefficients. -/
def reachableTube (C : Coordinates) (Φ : ℝ → Endˣ) (Y : SE23)
    (initial : Set LogState) (ε t : ℝ) : Set SE23 :=
  {X | ∃ z₀ ∈ initial, ∃ e : LogState, ‖e‖≤ε ∧
    X=Y*groupExp (C ((Φ t).val z₀+e))}

/-- Applying the certificate uniformly to an initial set gives the physical
set inclusion. This step is exact, including finite-angle reconstruction. -/
theorem mem_reachableTube (C : Coordinates) (Φ : ℝ → Endˣ) (X Y : SE23)
    (x z₀ : LogState) (initial : Set LogState) {ε t : ℝ}
    (he : SE23.error Y X=groupExp x) (hi : z₀ ∈ initial)
    (herr : ‖C.symm x-(Φ t).val z₀‖≤ε) :
    X ∈ reachableTube C Φ Y initial ε t := by
  refine ⟨z₀, hi, C.symm x-(Φ t).val z₀, herr, ?_⟩
  simpa using reconstruction he

/-- Normalized coordinates can always be used without an external norm
oracle. The factors two are a conservative, proved conversion from the
three-component box norm to the Euclidean norm, not physical allowances. -/
theorem identity_coordinate_gains (z : LogState) (v : Vec3) :
    enorm (z 0)≤2*‖z‖ ∧ enorm (z 2)≤2*‖z‖ ∧ ‖velocityOnly v‖≤enorm v := by
  refine ⟨(enorm_le_two_pi_norm _).trans ?_, (enorm_le_two_pi_norm _).trans ?_, ?_⟩
  · exact mul_le_mul_of_nonneg_left (norm_le_pi_norm z 0) (by norm_num)
  · exact mul_le_mul_of_nonneg_left (norm_le_pi_norm z 2) (by norm_num)
  · apply (pi_norm_le_iff_of_nonneg (enorm_nonneg v)).mpr
    intro i
    fin_cases i <;> simp [velocityOnly, enorm_nonneg, pi_norm_le_enorm]

end GNC.OrbitalLogTube
