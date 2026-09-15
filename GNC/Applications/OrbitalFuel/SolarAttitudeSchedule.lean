import GNC.Applications.OrbitalFuel.SharedBiasGeometry
import GNC.Lie.AxisRotation
import GNC.Planning.CoastInterpolation

/-! A twice-differentiable Euler-angle schedule realizes every stored solar
burn orientation. Interpolation occurs exclusively in the prescribed coasts.
The inertial orbital frame and attitude actuator must be supplied separately.
-/
noncomputable section
set_option autoImplicit false
namespace GNC.Applications.OrbitalFuel.SolarAttitudeSchedule
open GNC GNC.AxisRotation GNC.Planning Matrix
open _root_.Real
open scoped Matrix Matrix.Norms.Operator

def basePsi : Fin 6 → ℝ := ![Real.pi/2,0,0,Real.pi/2,0,0]
def baseTheta : Fin 6 → ℝ := ![Real.pi/2,-Real.pi/2,0,-Real.pi/2,Real.pi/2,Real.pi]
def key (k : Fin 3) (j : ℕ) : ℝ :=
  ![basePsi ⟨j%6, Nat.mod_lt _ (by norm_num)⟩,
    baseTheta ⟨j%6, Nat.mod_lt _ (by norm_num)⟩,
    if j/6%2=1 then Real.pi else 0] k
def coastStart (j : ℕ) : ℝ := j/30+2/75
def coastDuration (_ : ℕ) : ℝ := 1/75
def angle (k : Fin 3) : ℝ → ℝ := CoastInterpolation.value (key k) coastStart coastDuration 17
def angleRate (k : Fin 3) : ℝ → ℝ := CoastInterpolation.velocity (key k) coastStart coastDuration 17
def angleAcceleration (k : Fin 3) : ℝ → ℝ :=
  CoastInterpolation.acceleration (key k) coastStart coastDuration 17

def rotation (t : ℝ) : SO3 := zRotation (angle 0 t)*xRotation (angle 1 t)*zRotation (angle 2 t)

theorem base_factorization (i : Fin 6) :
    SharedBiasGeometry.baseRotation i = zRotation (basePsi i)*xRotation (baseTheta i) := by
  apply Subtype.ext
  fin_cases i <;> ext r c <;> fin_cases r <;> fin_cases c <;>
    norm_num [SharedBiasGeometry.baseRotation, SharedBiasGeometry.base, basePsi, baseTheta,
      zRotation, xRotation, zMatrix, xMatrix, mul_apply, Fin.sum_univ_succ, neg_div]

theorem reversal_factorization : SharedBiasGeometry.rollReversal = zRotation Real.pi := by
  apply Subtype.ext
  ext r c
  fin_cases r <;> fin_cases c <;>
    norm_num [SharedBiasGeometry.rollReversal, SharedBiasGeometry.reversal, zRotation, zMatrix]

theorem key_factorization (j : Fin 18) : SharedBiasGeometry.cycleRotation j =
    zRotation (key 0 j.val)*xRotation (key 1 j.val)*zRotation (key 2 j.val) := by
  unfold SharedBiasGeometry.cycleRotation
  rw [base_factorization]
  dsimp [key]
  split_ifs
  · rw [reversal_factorization]
  · rw [z_zero]

theorem angle_derivative (k : Fin 3) (t : ℝ) : HasDerivAt (angle k) (angleRate k t) t :=
  CoastInterpolation.value_derivative _ _ _ _ _
theorem angleRate_derivative (k : Fin 3) (t : ℝ) :
    HasDerivAt (angleRate k) (angleAcceleration k t) t :=
  CoastInterpolation.velocity_derivative _ _ _ _ _
theorem angleAcceleration_continuous (k : Fin 3) : Continuous (angleAcceleration k) :=
  CoastInterpolation.acceleration_continuous _ _ _ _

theorem angle_twice_contDiff (k : Fin 3) : ContDiff ℝ 2 (angle k) :=
  CoastInterpolation.value_twice_contDiff _ _ _ _

def variation (k : Fin 3) : ℝ := ![11/2,23/2,2] k*Real.pi

theorem total_variation (k : Fin 3) :
    ∑ i ∈ Finset.range 17, |key k (i+1)-key k i| = variation k := by
  fin_cases k <;>
    norm_num [Finset.sum_range_succ, key, basePsi, baseTheta, variation] <;>
    ring_nf <;> norm_num [abs_mul, abs_of_pos Real.pi_pos] <;> ring

theorem coordinate_bounds (k : Fin 3) (t : ℝ) :
    |angleRate k t| ≤ variation k*(1125/8) ∧
    |angleAcceleration k t| ≤ variation k*84375 := by
  have hv := CoastInterpolation.velocity_bound (key k) coastStart coastDuration 17 t
    (fun _ _ => by norm_num [coastDuration])
  have ha := CoastInterpolation.acceleration_bound (key k) coastStart coastDuration 17 t
    (fun _ _ => by norm_num [coastDuration])
  simp only [coastDuration, div_eq_mul_inv, ← Finset.sum_mul, total_variation] at hv ha
  constructor
  · convert hv using 1 <;> norm_num <;> ring
  · convert ha using 1 <;> norm_num <;> ring

theorem coordinate_sum_bounds (t : ℝ) :
    |angleRate 0 t|+|angleRate 1 t|+|angleRate 2 t| ≤ 19*Real.pi*(1125/8) ∧
    |angleAcceleration 0 t|+|angleAcceleration 1 t|+|angleAcceleration 2 t| ≤
      19*Real.pi*84375 := by
  have h0 := coordinate_bounds 0 t
  have h1 := coordinate_bounds 1 t
  have h2 := coordinate_bounds 2 t
  norm_num [variation, Matrix.cons_val_two] at h0 h1 h2
  constructor <;> linarith

theorem angle_on_burn (k : Fin 3) (j : Fin 18) {t : ℝ}
    (ht : t ∈ Set.Icc ((j.val:ℝ)/30+1/150) ((j.val:ℝ)/30+2/75)) :
    angle k t = key k j.val := by
  apply CoastInterpolation.at_hold (key k) coastStart coastDuration (by omega)
    (fun _ _ => by norm_num [coastDuration])
  · intro i hi
    have hij : (i:ℝ)+1 ≤ j.val := by exact_mod_cast hi
    dsimp [coastStart, coastDuration]
    linarith [ht.1]
  · intro i hi hij
    have hij' : (j.val:ℝ) ≤ i := by exact_mod_cast hij
    dsimp [coastStart]
    linarith [ht.2]

theorem rotation_on_burn (j : Fin 18) {t : ℝ}
    (ht : t ∈ Set.Icc ((j.val:ℝ)/30+1/150) ((j.val:ℝ)/30+2/75)) :
    rotation t = SharedBiasGeometry.cycleRotation j := by
  rw [rotation, angle_on_burn 0 j ht, angle_on_burn 1 j ht, angle_on_burn 2 j ht,
    key_factorization]

end GNC.Applications.OrbitalFuel.SolarAttitudeSchedule
