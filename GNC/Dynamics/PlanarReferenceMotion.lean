import GNC.Dynamics.PlanarAttitudeFrame
import GNC.Dynamics.PlanarChaserError
import GNC.Lie.RotationIsometry

/-! Physical position and velocity projections of a planar thrusting orbit.
The exact SO(3) frame supplies constant-magnitude tangential acceleration.+-/
noncomputable section
namespace GNC.PlanarReferenceMotion
open PolynomialOrbit PolynomialOrbitTransition Matrix

def tangent : Vec3 := ![0,1,0]

theorem tangent_norm : enorm tangent=1 := by
  have hs := enorm_sq tangent
  have hl : lengthSq tangent=1 := by norm_num [tangent,lengthSq,Matrix.cons_val_two]
  rw [hl] at hs
  nlinarith [enorm_nonneg tangent]

theorem thrust_rotation (a : ℝ) (w : Fin 4 → ℝ) (hr : 0<radius w) :
    PlanarChaserError.referenceThrust a w=
      a • rotate (PlanarAttitudeFrame.rotation w hr) tangent := rfl

theorem position_derivative {w : ℝ → Fin 4 → ℝ} {a t : ℝ}
    (hw : HasDerivAt w (physicalRate a (w t)) t) :
    HasDerivAt (fun s => position (w s)) (velocity (w t)) t := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa [position,velocity,physicalRate] using hasDerivAt_pi.mp hw 0
  · simpa [position,velocity,physicalRate] using hasDerivAt_pi.mp hw 1
  · simpa [position,velocity] using hasDerivAt_const t (0:ℝ)

theorem velocity_derivative {w : ℝ → Fin 4 → ℝ} {a t : ℝ}
    (hw : HasDerivAt w (physicalRate a (w t)) t) :
    HasDerivAt (fun s => velocity (w s))
      (Gravity.field3 1 (position (w t))+PlanarChaserError.referenceThrust a (w t)) t := by
  rw [←PlanarChaserError.reference_acceleration]
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa [velocity] using hasDerivAt_pi.mp hw 2
  · simpa [velocity] using hasDerivAt_pi.mp hw 3
  · simpa [velocity,Matrix.cons_val_two] using hasDerivAt_const t (0:ℝ)

theorem position_continuous {w : ℝ → Fin 4 → ℝ} (hw : Continuous w) :
    Continuous (fun t => position (w t)) := by
  apply continuous_pi
  intro i
  fin_cases i <;> simp [position,Matrix.cons_val_two] <;> fun_prop

theorem velocity_continuous {w : ℝ → Fin 4 → ℝ} (hw : Continuous w) :
    Continuous (fun t => velocity (w t)) := by
  apply continuous_pi
  intro i
  fin_cases i <;> simp [velocity,Matrix.cons_val_two] <;> fun_prop

theorem rotated_continuous {w : ℝ → Fin 4 → ℝ} (hw : Continuous w)
    (hr : ∀ t, 0<radius (w t)) (v : Vec3) :
    Continuous (fun t => rotate (PlanarAttitudeFrame.rotation (w t) (hr t)) v) := by
  have h := lift_continuous hw hr
  apply continuous_pi
  intro i
  fin_cases i <;>
    simp [rotate,PlanarAttitudeFrame.rotation,polynomialFrame,mulVec,dotProduct,
      Fin.sum_univ_succ,Matrix.cons_val_two] <;> fun_prop

end GNC.PlanarReferenceMotion
