import GNC.Dynamics.PolynomialOrbit
import GNC.Dynamics.ReactionWheels
import GNC.Lie.AxisRotation

/-! Exact spatial rendezvous dynamics about an unforced circular target.

Length is scaled by target radius and time by inverse mean motion. The RTN
relative state has three positions and three coordinate derivatives. The
normal gravitational acceleration is retained, as are all Coriolis and
centrifugal terms. Reconstruction below gives the actual inertial equations.
-/
noncomputable section
namespace GNC.CircularRendezvous3D
open Matrix Real
open scoped Matrix Matrix.Norms.Operator

def offset (w : Fin 6 → ℝ) : Vec3 := ![w 0, w 1, w 2]
def position (w : Fin 6 → ℝ) : Vec3 := ![1+w 0, w 1, w 2]
def coordinateVelocity (w : Fin 6 → ℝ) : Vec3 := ![w 3, w 4, w 5]
def radius (w : Fin 6 → ℝ) : ℝ := sqrt ((1+w 0)^2+w 1^2+w 2^2)

def physicalRate (u : Vec3) (w : Fin 6 → ℝ) : Fin 6 → ℝ :=
  ![w 3, w 4, w 5,
    2*w 4+1+w 0-(1+w 0)/(radius w)^3+u 0,
    -2*w 3+w 1-w 1/(radius w)^3+u 1,
    -w 2/(radius w)^3+u 2]

def rate (u : Vec3) (z : Fin 7 → ℝ) : Fin 7 → ℝ :=
  ![z 3, z 4, z 5,
    2*z 4+1+z 0-(1+z 0)*z 6^3+u 0,
    -2*z 3+z 1-z 1*z 6^3+u 1,
    -z 2*z 6^3+u 2,
    -z 6^3*((1+z 0)*z 3+z 1*z 4+z 2*z 5)]

def lift (w : Fin 6 → ℝ) : Fin 7 → ℝ :=
  ![w 0, w 1, w 2, w 3, w 4, w 5, (radius w)⁻¹]

theorem radius_eq_norm (w : Fin 6 → ℝ) : radius w = enorm (position w) := by
  have h : enorm (position w)^2 = (1+w 0)^2+w 1^2+w 2^2 := enorm_sq _
  rw [radius, ← h, sqrt_sq_eq_abs, abs_of_nonneg (enorm_nonneg _)]

theorem lift_continuous {w : ℝ → Fin 6 → ℝ} (hw : Continuous w)
    (hr : ∀ t, 0 < radius (w t)) : Continuous (fun t => lift (w t)) := by
  have hc : Continuous (fun t => radius (w t)) := by unfold radius; fun_prop
  apply continuous_pi
  intro i
  fin_cases i
  · change Continuous (fun t => w t 0)
    exact (continuous_apply 0).comp hw
  · change Continuous (fun t => w t 1)
    exact (continuous_apply 1).comp hw
  · change Continuous (fun t => w t 2)
    exact (continuous_apply 2).comp hw
  · change Continuous (fun t => w t 3)
    exact (continuous_apply 3).comp hw
  · change Continuous (fun t => w t 4)
    exact (continuous_apply 4).comp hw
  · change Continuous (fun t => w t 5)
    exact (continuous_apply 5).comp hw
  · change Continuous (fun t => (radius (w t))⁻¹)
    exact hc.inv₀ (fun t => ne_of_gt (hr t))

theorem lift_derivative {w : ℝ → Fin 6 → ℝ} {u : Vec3} {t : ℝ}
    (hw : HasDerivAt w (physicalRate u (w t)) t) (hr : 0 < radius (w t)) :
    HasDerivAt (fun s => lift (w s)) (rate u (lift (w t))) t := by
  have h0 := hasDerivAt_pi.mp hw 0
  have h1 := hasDerivAt_pi.mp hw 1
  have h2 := hasDerivAt_pi.mp hw 2
  have h3 := hasDerivAt_pi.mp hw 3
  have h4 := hasDerivAt_pi.mp hw 4
  have h5 := hasDerivAt_pi.mp hw 5
  simp only [physicalRate, Matrix.cons_val_zero, Matrix.cons_val_succ] at h0 h1 h2 h3 h4 h5
  have hs : (1+w t 0)^2+w t 1^2+w t 2^2 ≠ 0 := ne_of_gt (sqrt_pos.mp hr)
  have hi := (((((h0.const_add 1).pow 2).add (h1.pow 2)).add (h2.pow 2)).sqrt hs).inv (ne_of_gt hr)
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa [lift, rate] using h0
  · simpa [lift, rate] using h1
  · simpa [lift, rate] using h2
  · convert h3 using 1 <;> simp [rate, lift, div_eq_mul_inv]
  · convert h4 using 1 <;> simp [rate, lift, div_eq_mul_inv]
  · convert h5 using 1 <;> simp [rate, lift, div_eq_mul_inv]
  · convert hi using 1
    simp [rate, lift, radius]
    field_simp
    <;> ring

def localInertialVelocity (w : Fin 6 → ℝ) : Vec3 :=
  ![w 3-w 1, w 4+1+w 0, w 5]

def inertialRelativeVelocity (w : Fin 6 → ℝ) : Vec3 :=
  ![w 3-w 1, w 4+w 0, w 5]

def inertialPosition (phase : ℝ) (w : Fin 6 → ℝ) : Vec3 :=
  rotate (AxisRotation.zRotation phase) (position w)

def inertialVelocity (phase : ℝ) (w : Fin 6 → ℝ) : Vec3 :=
  rotate (AxisRotation.zRotation phase) (localInertialVelocity w)

theorem local_velocity_identity (w : Fin 6 → ℝ) :
    coordinateVelocity w + ![0,0,1] ⨯₃ position w = localInertialVelocity w := by
  ext i
  fin_cases i <;> simp [coordinateVelocity, position, localInertialVelocity,
    cross_apply, Matrix.vecHead, Matrix.vecTail] <;> ring

theorem position_derivative {w : ℝ → Fin 6 → ℝ} {u : Vec3} {t phase : ℝ}
    (hw : HasDerivAt w (physicalRate u (w t)) t) :
    HasDerivAt (fun s => inertialPosition (phase+s) (w s))
      (inertialVelocity (phase+t) (w t)) t := by
  have hp : HasDerivAt (fun s => position (w s)) (coordinateVelocity (w t)) t := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · simpa [position, coordinateVelocity, physicalRate] using (hasDerivAt_pi.mp hw 0).const_add 1
    · simpa [position, coordinateVelocity, physicalRate] using hasDerivAt_pi.mp hw 1
    · simpa [position, coordinateVelocity, physicalRate] using hasDerivAt_pi.mp hw 2
  have hR := AxisRotation.z_derivative ((hasDerivAt_id t).const_add phase)
  simpa only [local_velocity_identity] using ReactionWheels.rotate_derivative hR hp

theorem gravity_rotate (R : SO3) (p : Vec3) :
    rotate R (Gravity.field3 1 p) = Gravity.field3 1 (rotate R p) := by
  change rotate R ((-1/enorm p^3) • p) = (-1/enorm (rotate R p)^3) • rotate R p
  simp only [rotate_smul, rotate_enorm]

/-- The exact rotating-frame physical ODE reconstructs the inverse-square
inertial acceleration, with the delivered force rotated by the same frame. -/
theorem velocity_derivative {w : ℝ → Fin 6 → ℝ} {u : Vec3} {t phase : ℝ}
    (hw : HasDerivAt w (physicalRate u (w t)) t) :
    HasDerivAt (fun s => inertialVelocity (phase+s) (w s))
      (Gravity.field3 1 (inertialPosition (phase+t) (w t)) +
        rotate (AxisRotation.zRotation (phase+t)) u) t := by
  let a : Vec3 := ![(physicalRate u (w t)) 3-w t 4,
    (physicalRate u (w t)) 4+w t 3, (physicalRate u (w t)) 5]
  have hv : HasDerivAt (fun s => localInertialVelocity (w s)) a t := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · simpa [a, localInertialVelocity, physicalRate] using
        (hasDerivAt_pi.mp hw 3).sub (hasDerivAt_pi.mp hw 1)
    · simpa [a, localInertialVelocity, physicalRate] using
        ((hasDerivAt_pi.mp hw 4).add_const 1).add (hasDerivAt_pi.mp hw 0)
    · simpa [a, localInertialVelocity, physicalRate] using hasDerivAt_pi.mp hw 5
  have ha : a + ![0,0,1] ⨯₃ localInertialVelocity (w t) =
      Gravity.field3 1 (position (w t)) + u := by
    change a + ![0,0,1] ⨯₃ localInertialVelocity (w t) =
      (-1/enorm (position (w t))^3) • position (w t) + u
    rw [← radius_eq_norm]
    ext i
    fin_cases i <;> simp [a, physicalRate, localInertialVelocity, position,
      Gravity.field3, cross_apply, Matrix.vecHead, Matrix.vecTail, div_eq_mul_inv] <;> ring
  have hR := AxisRotation.z_derivative ((hasDerivAt_id t).const_add phase)
  have h := ReactionWheels.rotate_derivative hR hv
  simpa only [ha, rotate_add, gravity_rotate, inertialPosition, inertialVelocity] using h

end GNC.CircularRendezvous3D
