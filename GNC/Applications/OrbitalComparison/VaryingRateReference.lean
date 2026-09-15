import GNC.Applications.OrbitalComparison.SpatialRotatingFrame
import GNC.Dynamics.GravityField
import GNC.Lie.RotatingForce

/-! A physical circular reference with arbitrary differentiable angular rate.
Its required acceleration contains the radial balance and tangential Euler
term. This is an analytic nominal, not a constant-rate orbit selected during
a burn. The exact oblique pointing source has two harmonics of its phase.
These identities do not certify a numerical perturbed trajectory.
-/
noncomputable section
set_option autoImplicit false
namespace GNC.OrbitalComparison.VaryingRateReference
open SpatialBurn SpatialRotatingFrame Real Matrix
open scoped Matrix

def position (r φ : ℝ) : E3 := mix φ r 0 0
def velocity (r φ w : ℝ) : E3 := mix φ 0 (r*w) 0
def acceleration (r φ w α : ℝ) : E3 := mix φ (-r*w^2) (r*α) 0
def thrust (μ r φ w α : ℝ) : E3 := mix φ (μ/r^2-r*w^2) (r*α) 0

theorem position_norm (r φ : ℝ) (hr : 0 ≤ r) : ‖position r φ‖=r := by
  have h := mix_norm_sq φ r 0 0
  change ‖position r φ‖^2=r^2+0^2+0^2 at h
  nlinarith [norm_nonneg (position r φ)]

theorem position_derivative {φ : ℝ → ℝ} {w t : ℝ} (r : ℝ)
    (hφ : HasDerivAt φ w t) :
    HasDerivAt (fun s => position r (φ s)) (velocity r (φ t) w) t := by
  simpa [position,velocity,mul_comm] using
    mix_derivative hφ (hasDerivAt_const t r) (hasDerivAt_const t (0:ℝ))
      (hasDerivAt_const t (0:ℝ))

theorem velocity_derivative {φ w : ℝ → ℝ} {α t : ℝ} (r : ℝ)
    (hφ : HasDerivAt φ (w t) t) (hw : HasDerivAt w α t) :
    HasDerivAt (fun s => velocity r (φ s) (w s)) (acceleration r (φ t) (w t) α) t := by
  convert mix_derivative hφ (hasDerivAt_const t (0:ℝ)) (hw.const_mul r)
    (hasDerivAt_const t (0:ℝ)) using 1
  simp only [acceleration,zero_sub,mul_zero,add_zero]
  congr 1
  ring

theorem physical_acceleration (μ r φ w α : ℝ) (hr : 0 < r) :
    Gravity.field μ (position r φ)+thrust μ r φ w α=acceleration r φ w α := by
  rw [Gravity.field,position_norm r φ hr.le]
  unfold position thrust acceleration
  rw [←mix_smul,←mix_add]
  congr 1
  · field_simp
    ring
  · ring
  · ring

/-- The prescribed nominal solves the full inverse-square equation. Angular
acceleration determines tangential thrust and is not discarded. -/
theorem physical_velocity_derivative {φ w : ℝ → ℝ} {α t : ℝ} (μ r : ℝ)
    (hr : 0 < r) (hφ : HasDerivAt φ (w t) t) (hw : HasDerivAt w α t) :
    HasDerivAt (fun s => velocity r (φ s) (w s))
      (Gravity.field μ (position r (φ t))+thrust μ r (φ t) (w t) α) t := by
  rw [physical_acceleration μ r (φ t) (w t) α hr]
  exact velocity_derivative r hφ hw

/-- The body angular rate of the nominal attitude is (0,0,w(t)). -/
theorem attitude_derivative {φ : ℝ → ℝ} {w t : ℝ}
    (hφ : HasDerivAt φ w t) :
    HasDerivAt (fun s => (AxisRotation.zRotation (φ s)).val)
      ((AxisRotation.zRotation (φ t)).val*skew ![0,0,w]) t :=
  AxisRotation.z_derivative hφ

def firstForce (φ x y : ℝ) : Vec3 :=
  ![-(4/5)*y, (4/5)*x, (3/5)*(cos φ*x-sin φ*y)]

def secondForce (φ x y : ℝ) : Vec3 :=
  ![-(41/50)*x-(9/50)*cos (2*φ)*x+(9/50)*sin (2*φ)*y,
    (9/50)*sin (2*φ)*x-(41/50)*y+(9/50)*cos (2*φ)*y,
    -(12/25)*(sin φ*x+cos φ*y)]

theorem oblique_matrix (θ : ℝ) :
    (attitude θ).val =
      !![cos θ,-(4/5)*sin θ,-(3/5)*sin θ;
         (4/5)*sin θ,1-(16/25)*(1-cos θ),-(12/25)*(1-cos θ);
         (3/5)*sin θ,-(12/25)*(1-cos θ),1-(9/25)*(1-cos θ)] := by
  rw [attitude_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [axisFrameMatrix,AxisRotation.zMatrix,mul_apply,Fin.sum_univ_succ] <;> ring

/-- All three components of a fixed oblique attitude error. The fractions
come from the unit axis (0,-3/5,4/5), not error allowances. This is exact for
any reference phase and radial/transverse acceleration, including a changing
phase rate. No time or pointing Taylor expansion occurs here. -/
theorem pointing_source (θ φ x y : ℝ) :
    (AxisRotation.zMatrix (-φ)*((attitude θ).val-1)*AxisRotation.zMatrix φ) *ᵥ
      ![x,y,0] = sin θ • firstForce φ x y+(1-cos θ) • secondForce φ x y := by
  rw [RotatingForce.conjugation,oblique_matrix]
  ext i
  fin_cases i <;>
    simp [RotatingForce.harmonic,firstForce,secondForce] <;> ring

end GNC.OrbitalComparison.VaryingRateReference
