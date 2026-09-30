import GNC.Applications.OrbitalBibo.CascadeExample
import GNC.Applications.OrbitalComparison.PoweredCircle

/-! An exact synthetic powered circular reference for the BIBO benchmark.
The orbit is maintained with a constant radial outward acceleration; its
angular speed is slightly below the unforced Keplerian speed. No numerical
reference defect or state-dependent gravity cancellation is assumed.
-/
noncomputable section
namespace GNC.OrbitalBibo.PoweredReference
open GNC.OrbitalComparison.PoweredCircle
open CascadeExample
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def orbitRadius : ℝ := 42164000
def rateSq : ℝ := mu/orbitRadius^3-thrustAcceleration/orbitRadius
def rate : ℝ := Real.sqrt rateSq

theorem rate_bounds : 0 < rate ∧ rate ≤ 1/10000 := by
  have hs : 0 < rateSq := by norm_num [rateSq,mu,orbitRadius,thrustAcceleration]
  constructor
  · exact Real.sqrt_pos.mpr hs
  · apply (Real.sqrt_le_iff).mpr
    constructor
    · norm_num
    · norm_num [rateSq,mu,orbitRadius,thrustAcceleration]

def position (B : Plane E) (t : ℝ) : E := orbitRadius • B.radial (rate*t)
def velocity (B : Plane E) (t : ℝ) : E := (orbitRadius*rate) • B.tangent (rate*t)

theorem reference_radius (B : Plane E) (t : ℝ) : ‖position B t‖ = orbitRadius := by
  rw [position,norm_smul,Real.norm_eq_abs,B.norm_radial]
  norm_num [orbitRadius]

theorem reference_domain (B : Plane E) (t : ℝ) : radius ≤ ‖position B t‖ := by
  rw [reference_radius]
  norm_num [radius,orbitRadius]

theorem physical_reference (B : Plane E) (t : ℝ) :
    HasDerivAt (position B) (velocity B t) t ∧
    HasDerivAt (velocity B)
      (Gravity.field mu (position B t)+thrustAcceleration • B.radial (rate*t)) t := by
  have hd : HasDerivAt (fun s : ℝ => rate*s) rate t := by
    simpa using (hasDerivAt_id t).const_mul rate
  constructor
  · convert (B.radial_derivative hd).const_smul orbitRadius using 1
    dsimp [velocity]
    module
  · have hs : rate^2 = rateSq := Real.sq_sqrt (by
      norm_num [rateSq,mu,orbitRadius,thrustAcceleration])
    convert (B.tangent_derivative hd).const_smul (orbitRadius*rate) using 1
    rw [Gravity.field,reference_radius]
    dsimp [position]
    match_scalars
    rw [show orbitRadius*rate*(-rate*1) = -orbitRadius*rate^2 by ring,hs]
    norm_num [rateSq,mu,orbitRadius,thrustAcceleration]

end GNC.OrbitalBibo.PoweredReference
