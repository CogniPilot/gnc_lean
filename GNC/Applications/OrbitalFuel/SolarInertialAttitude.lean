import GNC.Applications.OrbitalFuel.SolarAttitudeRealization
import GNC.Planning.CoastInterpolationBounds
import GNC.Lie.RotationTimeChange

/-! Smooth realization of the midpoint inertial-hold architecture.

The same exact solar reference supplies each burn's constant orientation.
A scalar clock traverses the reference only during coasts. This certifies
the attitude and its angular derivatives, not the new orbit terminal data.
The preceding rotating-command mission certificate does not transfer. -/
noncomputable section
set_option autoImplicit false
namespace GNC.Applications.OrbitalFuel.SolarInertialAttitude
open GNC GNC.RotationKinematics GNC.Planning ChaserReferenceData Set Matrix
open SolarAttitudeSchedule
open scoped Matrix Matrix.Norms.Operator

def midpoint (j : ℕ) : ℝ := j/30+1/60
def clock : ℝ → ℝ := CoastInterpolation.value midpoint coastStart coastDuration 17
def clockRate : ℝ → ℝ := CoastInterpolation.velocity midpoint coastStart coastDuration 17
def clockAcceleration : ℝ → ℝ := CoastInterpolation.acceleration midpoint coastStart coastDuration 17

theorem clock_derivative (t : ℝ) : HasDerivAt clock (clockRate t) t :=
  CoastInterpolation.value_derivative _ _ _ _ _
theorem clockRate_derivative (t : ℝ) : HasDerivAt clockRate (clockAcceleration t) t :=
  CoastInterpolation.velocity_derivative _ _ _ _ _

theorem clock_range (t : ℝ) : clock t ∈ Icc (0:ℝ) (3/5) := by
  have h := CoastInterpolation.value_bounds midpoint coastStart coastDuration 17 t
    (fun i _ => by dsimp [midpoint]; push_cast; linarith)
  norm_num [midpoint] at h
  change 1/60 ≤ clock t ∧ clock t ≤ 7/12 at h
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

theorem clock_bounds (t : ℝ) : |clockRate t| ≤ 80 ∧ |clockAcceleration t| ≤ 48000 := by
  have hd (i : ℕ) : midpoint (i+1)-midpoint i = 1/30 := by
    simp only [midpoint, Nat.cast_add, Nat.cast_one]
    ring
  have hv := CoastInterpolation.velocity_bound midpoint coastStart coastDuration 17 t
    (fun _ _ => by norm_num [coastDuration])
  have ha := CoastInterpolation.acceleration_bound midpoint coastStart coastDuration 17 t
    (fun _ _ => by norm_num [coastDuration])
  simp only [hd, coastDuration] at hv ha
  norm_num at hv ha
  exact ⟨hv.trans (by norm_num), ha.trans (by norm_num)⟩

theorem hold_conditions (j : Fin 18) {t : ℝ}
    (ht : t ∈ Icc ((j.val:ℝ)/30+1/150) ((j.val:ℝ)/30+2/75)) :
    (∀ i < j.val, coastStart i+coastDuration i ≤ t) ∧
    (∀ i ∈ Finset.range 17, j.val ≤ i → t ≤ coastStart i) := by
  constructor
  · intro i hi
    have hij : (i:ℝ)+1 ≤ j.val := by exact_mod_cast hi
    dsimp [coastStart, coastDuration]
    linarith [ht.1]
  · intro i _ hij
    have hij' : (j.val:ℝ) ≤ i := by exact_mod_cast hij
    dsimp [coastStart]
    linarith [ht.2]

theorem clock_on_burn (j : Fin 18) {t : ℝ}
    (ht : t ∈ Icc ((j.val:ℝ)/30+1/150) ((j.val:ℝ)/30+2/75)) :
    clock t = midpoint j.val ∧ clockRate t = 0 ∧ clockAcceleration t = 0 := by
  have h := hold_conditions j ht
  exact ⟨CoastInterpolation.at_hold midpoint coastStart coastDuration (by omega)
      (fun _ _ => by norm_num [coastDuration]) h.1 h.2,
    CoastInterpolation.jets_at_hold midpoint coastStart coastDuration
      (fun _ _ => by norm_num [coastDuration]) h.1 h.2⟩

theorem angle_jets_on_burn (k : Fin 3) (j : Fin 18) {t : ℝ}
    (ht : t ∈ Icc ((j.val:ℝ)/30+1/150) ((j.val:ℝ)/30+2/75)) :
    angleRate k t = 0 ∧ angleAcceleration k t = 0 := by
  have h := hold_conditions j ht
  exact CoastInterpolation.jets_at_hold (key k) coastStart coastDuration
    (fun _ _ => by norm_num [coastDuration]) h.1 h.2

def heldReference (r : Flow) : Path :=
  (SolarAttitudeRealization.reference r).timeChange clock clockRate clockAcceleration

def path (r : Flow) : Path :=
  (((heldReference r).compose SolarAttitudeRealization.firstZ).compose
    SolarAttitudeRealization.middleX).compose SolarAttitudeRealization.lastZ

def burnRotation (r : Flow) (j : Fin 18) : SO3 :=
  (SolarAttitudeRealization.reference r).rotation (midpoint j.val)*SharedBiasGeometry.cycleRotation j

theorem heldReference_jet (r : Flow) (t : ℝ) : (heldReference r).HasJet t :=
  Path.timeChange_jet _ (SolarAttitudeRealization.reference_jet r (clock_range t))
    (clock_derivative t) (clockRate_derivative t)

theorem path_jet (r : Flow) (t : ℝ) : (path r).HasJet t :=
  Path.compose_jet _ _ (Path.compose_jet _ _ (Path.compose_jet _ _ (heldReference_jet r t)
    (Path.z_jet (angle_derivative 0 t) (angleRate_derivative 0 t)))
    (Path.x_jet (angle_derivative 1 t) (angleRate_derivative 1 t)))
    (Path.z_jet (angle_derivative 2 t) (angleRate_derivative 2 t))

theorem path_continuous (r : Flow) : (path r).HasContinuousJet := by
  have hr : (heldReference r).HasContinuousJet := Path.timeChange_continuous _
    (SolarAttitudeRealization.reference_continuous r)
    (CoastInterpolation.value_continuous _ _ _ _)
    (CoastInterpolation.velocity_continuous _ _ _ _)
    (CoastInterpolation.acceleration_continuous _ _ _ _)
  exact Path.compose_continuous _ _ (Path.compose_continuous _ _
    (Path.compose_continuous _ _ hr
      (Path.z_continuous (angle_derivative 0) (angleRate_derivative 0) (angleAcceleration_continuous 0)))
    (Path.x_continuous (angle_derivative 1) (angleRate_derivative 1) (angleAcceleration_continuous 1)))
    (Path.z_continuous (angle_derivative 2) (angleRate_derivative 2) (angleAcceleration_continuous 2))

theorem on_burn (r : Flow) (j : Fin 18) {t : ℝ}
    (ht : t ∈ Icc ((j.val:ℝ)/30+1/150) ((j.val:ℝ)/30+2/75)) :
    (path r).rotation t = burnRotation r j := by
  simp only [path, Path.compose, heldReference, Path.timeChange, burnRotation,
    SolarAttitudeRealization.firstZ, SolarAttitudeRealization.middleX,
    SolarAttitudeRealization.lastZ, Path.x, Path.z, (clock_on_burn j ht).1,
    angle_on_burn 0 j ht, angle_on_burn 1 j ht, angle_on_burn 2 j ht,
    key_factorization, mul_assoc]

/-- Exact rest during each closed burn, rather than a small sampled rate. -/
theorem rest_on_burn (r : Flow) (j : Fin 18) {t : ℝ}
    (ht : t ∈ Icc ((j.val:ℝ)/30+1/150) ((j.val:ℝ)/30+2/75)) :
    (path r).velocity t = 0 ∧ (path r).acceleration t = 0 := by
  have hc := clock_on_burn j ht
  have h0 := angle_jets_on_burn 0 j ht
  have h1 := angle_jets_on_burn 1 j ht
  have h2 := angle_jets_on_burn 2 j ht
  have hr := Path.timeChange_at_hold (SolarAttitudeRealization.reference r)
    clock clockRate clockAcceleration t hc.2.1 hc.2.2
  change (heldReference r).velocity t = 0 ∧ (heldReference r).acceleration t = 0 at hr
  have hz : (![0,0,0]:Vec3) = 0 := by ext i; fin_cases i <;> rfl
  have hzv : SolarAttitudeRealization.firstZ.velocity t = 0 := by
    change (![0,0,angleRate 0 t]:Vec3) = 0
    rw [h0.1]; exact hz
  have hza : SolarAttitudeRealization.firstZ.acceleration t = 0 := by
    change (![0,0,angleAcceleration 0 t]:Vec3) = 0
    rw [h0.2]; exact hz
  have hxv : SolarAttitudeRealization.middleX.velocity t = 0 := by
    change (![angleRate 1 t,0,0]:Vec3) = 0
    rw [h1.1]; exact hz
  have hxa : SolarAttitudeRealization.middleX.acceleration t = 0 := by
    change (![angleAcceleration 1 t,0,0]:Vec3) = 0
    rw [h1.2]; exact hz
  have hlv : SolarAttitudeRealization.lastZ.velocity t = 0 := by
    change (![0,0,angleRate 2 t]:Vec3) = 0
    rw [h2.1]; exact hz
  have hla : SolarAttitudeRealization.lastZ.acceleration t = 0 := by
    change (![0,0,angleAcceleration 2 t]:Vec3) = 0
    rw [h2.2]; exact hz
  simp only [path, Path.compose, productRate, productAcceleration, hr.1, hr.2,
    hzv, hza, hxv, hxa, hlv, hla, rotate_zero, cross_self, zero_add, sub_zero, and_self]

theorem normalized_bounds (r : Flow) (t : ℝ) :
    GNC.enorm ((path r).velocity t) ≤ 9000 ∧
      GNC.enorm ((path r).acceleration t) ≤ 90000000 := by
  have hb := SolarAttitudeRealization.reference_bounds r (clock_range t)
  have hc := clock_bounds t
  have hr := Path.timeChange_bounds (SolarAttitudeRealization.reference r)
    clock clockRate clockAcceleration t hb.1 hb.2 hc.1 hc.2
  norm_num at hr
  have hy : GNC.enorm (SolarAttitudeRealization.firstZ.velocity t) = |angleRate 0 t| := z_axis_norm _
  have hp : GNC.enorm (SolarAttitudeRealization.middleX.velocity t) = |angleRate 1 t| := x_axis_norm _
  have hl : GNC.enorm (SolarAttitudeRealization.lastZ.velocity t) = |angleRate 2 t| := z_axis_norm _
  have hya : GNC.enorm (SolarAttitudeRealization.firstZ.acceleration t) = |angleAcceleration 0 t| := z_axis_norm _
  have hpa : GNC.enorm (SolarAttitudeRealization.middleX.acceleration t) = |angleAcceleration 1 t| := x_axis_norm _
  have hla : GNC.enorm (SolarAttitudeRealization.lastZ.acceleration t) = |angleAcceleration 2 t| := z_axis_norm _
  have h1 := Path.compose_bounds (heldReference r) SolarAttitudeRealization.firstZ t hr.1 hy.le hr.2 hya.le
  have h2 := Path.compose_bounds ((heldReference r).compose SolarAttitudeRealization.firstZ)
    SolarAttitudeRealization.middleX t h1.1 hp.le h1.2 hpa.le
  have h3 := Path.compose_bounds (((heldReference r).compose SolarAttitudeRealization.firstZ).compose
    SolarAttitudeRealization.middleX) SolarAttitudeRealization.lastZ t h2.1 hl.le h2.2 hla.le
  have hs := coordinate_sum_bounds t
  have hv : 560+|angleRate 0 t|+|angleRate 1 t|+|angleRate 2 t| ≤ 9000 := by
    linarith [Real.pi_lt_d2]
  have ha : 860800+|angleAcceleration 0 t|+|angleAcceleration 1 t|+|angleAcceleration 2 t| ≤ 6000000 := by
    linarith [Real.pi_lt_d2]
  dsimp only [path]
  constructor
  · exact h3.1.trans hv
  · have hsq : (560+|angleRate 0 t|+|angleRate 1 t|+|angleRate 2 t|)^2 ≤ 9000^2 :=
      pow_le_pow_left₀ (by positivity) hv 2
    have h01 := mul_nonneg (abs_nonneg (angleRate 0 t)) (abs_nonneg (angleRate 1 t))
    have h02 := mul_nonneg (abs_nonneg (angleRate 0 t)) (abs_nonneg (angleRate 2 t))
    have h12 := mul_nonneg (abs_nonneg (angleRate 1 t)) (abs_nonneg (angleRate 2 t))
    nlinarith [h3.2, sq_nonneg (angleRate 0 t), sq_nonneg (angleRate 1 t),
      sq_nonneg (angleRate 2 t), abs_nonneg (angleRate 0 t), abs_nonneg (angleRate 1 t),
      abs_nonneg (angleRate 2 t), sq_abs (angleRate 0 t), sq_abs (angleRate 1 t), sq_abs (angleRate 2 t)]

def physicalPath (r : Flow) : Path := (path r).rescale SolarPropulsion.timeScale

theorem physical_continuous (r : Flow) : (physicalPath r).HasContinuousJet :=
  Path.rescale_continuous _ (path_continuous r) _

theorem physical_jet (r : Flow) (s : ℝ) : (physicalPath r).HasJet s :=
  Path.rescale_jet _ _ _ (path_jet r _)

theorem physical_bounds (r : Flow) (s : ℝ) :
    GNC.enorm ((physicalPath r).velocity s) ≤ 9/5000 ∧
      GNC.enorm ((physicalPath r).acceleration s) ≤ 9/2500000 := by
  have h := normalized_bounds r (s/SolarPropulsion.timeScale)
  have ht := SolarPropulsion.timeScale_pos
  have ht2 : 0 < SolarPropulsion.timeScale^2 := sq_pos_of_pos ht
  simp only [physicalPath, Path.rescale, GNC.enorm_smul, abs_of_pos (one_div_pos.mpr ht),
    abs_of_pos (one_div_pos.mpr ht2), one_div_mul_eq_div]
  constructor
  · rw [div_le_iff₀ ht]
    linarith [SolarAttitudeRealization.timeScale_lower]
  · rw [div_le_iff₀ ht2]
    nlinarith [SolarAttitudeRealization.timeScale_lower]

theorem physical_on_burn (r : Flow) (j : Fin 18) {s : ℝ}
    (hs : s/SolarPropulsion.timeScale ∈
      Icc ((j.val:ℝ)/30+1/150) ((j.val:ℝ)/30+2/75)) :
    (physicalPath r).rotation s = burnRotation r j ∧
      (physicalPath r).velocity s = 0 ∧ (physicalPath r).acceleration s = 0 := by
  have h := rest_on_burn r j hs
  exact ⟨on_burn r j hs, by simp [physicalPath, Path.rescale, h.1, h.2]⟩

structure Contract (r : Flow) : Prop where
  continuous : (physicalPath r).HasContinuousJet
  kinematics : ∀ s, (physicalPath r).HasJet s
  bounds : ∀ s, GNC.enorm ((physicalPath r).velocity s) ≤ 9/5000 ∧
    GNC.enorm ((physicalPath r).acceleration s) ≤ 9/2500000
  hold : ∀ (j : Fin 18) s, s/SolarPropulsion.timeScale ∈
    Icc ((j.val:ℝ)/30+1/150) ((j.val:ℝ)/30+2/75) →
    (physicalPath r).rotation s = burnRotation r j ∧
      (physicalPath r).velocity s = 0 ∧ (physicalPath r).acceleration s = 0

theorem contract (r : Flow) : Contract r :=
  ⟨physical_continuous r, physical_jet r, physical_bounds r, fun j _ => physical_on_burn r j⟩

/-- Reference existence is proved; no claim about the new chaser terminal
box is included in this attitude realization theorem. -/
theorem exists_attitude : ∃ r : Flow, Contract r := by
  obtain ⟨r⟩ := ReferenceFlowExistence.exists_reference_flow
  exact ⟨r,contract r⟩

end GNC.Applications.OrbitalFuel.SolarInertialAttitude
