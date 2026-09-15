import GNC.Applications.ApproachGate.Mission
import GNC.Dynamics.PhysicalScaling

/-! Exact frame and SI interpretation of the gate certificate.
Inertial velocity includes the rotation of the displaced position. The
time/length scaling satisfies the original dimensional gravity equation.
-/
noncomputable section
namespace GNC.ApproachGate
open Matrix

def speedSI : ℝ := Real.sqrt (speedSquaredSI : ℝ)
def timeSI : ℝ := (radiusSI : ℝ)/speedSI

theorem speed_positive : 0 < speedSI := by
  apply Real.sqrt_pos.mpr
  norm_num [speedSquaredSI]

theorem time_positive : 0 < timeSI :=
  div_pos (by norm_num [radiusSI]) speed_positive

theorem time_scaling : (398600441800000 : ℝ)/(radiusSI : ℝ)^2 = (radiusSI : ℝ)/timeSI^2 := by
  have hs : speedSI^2 = (speedSquaredSI : ℝ) :=
    Real.sq_sqrt (by norm_num [speedSquaredSI])
  rw [timeSI, div_pow, hs]
  norm_num [radiusSI, speedSquaredSI]

theorem velocity_scaling : (radiusSI : ℝ)/timeSI = speedSI := by
  rw [timeSI, div_div_eq_mul_div]
  norm_num [radiusSI]

theorem reconstruction_errors (z : Fin 11 → ℝ) (phase : ℝ) :
    CircularRendezvous3D.inertialPosition phase (project z)-
        CircularRendezvous3D.inertialPosition phase (fun i => (gateState i : ℝ)) =
      rotate (AxisRotation.zRotation phase) (positionError z) ∧
    CircularRendezvous3D.inertialVelocity phase (project z)-
        CircularRendezvous3D.inertialVelocity phase (fun i => (gateState i : ℝ)) =
      rotate (AxisRotation.zRotation phase) (velocityError z) := by
  constructor
  · simp only [CircularRendezvous3D.inertialPosition, ← rotate_sub]
    congr 1
    ext i
    fin_cases i <;> simp [CircularRendezvous3D.position, project, positionError, gateState,
      Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail] <;> ring
  · simp only [CircularRendezvous3D.inertialVelocity, ← rotate_sub]
    congr 1
    ext i
    fin_cases i <;> simp [CircularRendezvous3D.localInertialVelocity, project,
      velocityError, gateState, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail] <;> ring

theorem inertial_error_norms (z : Fin 11 → ℝ) (phase : ℝ) :
    enorm ((radiusSI : ℝ) •
      (CircularRendezvous3D.inertialPosition phase (project z)-
       CircularRendezvous3D.inertialPosition phase (fun i => (gateState i : ℝ)))) =
      enorm ((radiusSI : ℝ) • positionError z) ∧
    enorm (speedSI •
      (CircularRendezvous3D.inertialVelocity phase (project z)-
       CircularRendezvous3D.inertialVelocity phase (fun i => (gateState i : ℝ)))) =
      enorm (speedSI • velocityError z) := by
  rw [(reconstruction_errors z phase).1, (reconstruction_errors z phase).2]
  simp only [← rotate_smul, rotate_enorm, and_self]

end GNC.ApproachGate
