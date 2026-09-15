import GNC.Applications.OrbitalComparison.HarmonicFrame
import GNC.Dynamics.GravityQuadraticResponse

/-! Exact powered-reference calculus at an arbitrary time scale.
The horizon is `600 * α` seconds. Rotation, Coriolis, centrifugal and the
quadratic gravity response are derived from the physical inverse-square
field; none of these identities truncate a rotation series. -/
noncomputable section
namespace GNC.OrbitalComparison.PointingCapFrame
open SpatialBurn SpatialRotatingFrame SpatialExactNominal UniformCertificate
open HarmonicPolynomial (linear)
open Set Real
open scoped RealInnerProductSpace

def scale (α : ℝ) : ℝ := 360000*α^2
def turn (α t : ℝ) : E3 →ₗ[ℝ] E3 := HarmonicFrame.turn (α*t)
def spin (α : ℝ) : E3 →ₗ[ℝ] E3 := α • HarmonicFrame.spin
def reference (α t : ℝ) : E3 := nominal.p (α*t)
def referenceVelocity (α t : ℝ) : E3 := α • nominal.v (α*t)
def physicalAcceleration (α : ℝ) (n : E3) (t : ℝ) (p : E3) : E3 :=
  scale α • (Gravity.field mu p+(Direct.thrust:ℝ) • turn α t n)

theorem turn_norm (α t : ℝ) (x : E3) : ‖turn α t x‖=‖x‖ :=
  HarmonicFrame.turn_norm _ _
theorem reference_norm (α t : ℝ) : ‖reference α t‖=7000000 := nominal_norm _

theorem turn_derivative (α : ℝ) {x : ℝ → E3} {v : E3} {t : ℝ}
    (hx : HasDerivAt x v t) :
    HasDerivAt (fun s => turn α s (x s)) (turn α t (v+spin α (x t))) t := by
  have hi (i : Fin 3) : HasDerivAt (fun s => x s i) (v i) t :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp_hasDerivAt t hx
  have h := mix_derivative (((hasDerivAt_id t).const_mul α).const_mul (omega:ℝ))
    (hi 0) (hi 1) (hi 2)
  convert h using 1
  simp [turn,HarmonicFrame.turn,spin,HarmonicFrame.spin_apply,pack_eq]
  all_goals ring

theorem spin_derivative (α : ℝ) {x : ℝ → E3} {v : E3} {t : ℝ}
    (hx : HasDerivAt x v t) : HasDerivAt (fun s => spin α (x s)) (spin α v) t :=
  (spin α).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hx

theorem reference_derivative (α t : ℝ) :
    HasDerivAt (reference α) (referenceVelocity α t) t := by
  have ha : HasDerivAt (fun s : ℝ => α*s) α t := by
    simpa using (hasDerivAt_id t).const_mul α
  simpa [reference,referenceVelocity,nominal,smul_eq_mul] using
    ((plane.physical_reference (α*t)).1.scomp t ha)

theorem referenceVelocity_derivative (α t : ℝ) :
    HasDerivAt (referenceVelocity α)
      (physicalAcceleration α e0 t (reference α t)) t := by
  have ha : HasDerivAt (fun s : ℝ => α*s) α t := by
    simpa using (hasDerivAt_id t).const_mul α
  have h := (((plane.physical_reference (α*t)).2.scomp t ha).const_smul α)
  have hs : plane.radial (PoweredCircle.rate*(α*t))=turn α t e0 := by
    simp [turn,HarmonicFrame.turn,mix,pack,PoweredCircle.Plane.radial,plane,
      UniformCertificate.constants.1,e0]
  convert h using 1
  simp only [physicalAcceleration,reference,nominal,PoweredCircle.thrust_bounds.2.1,hs,scale]
  module

def position (α : ℝ) (d : ℝ → E3) (t : ℝ) : E3 := reference α t+turn α t (d t)
def velocity (α : ℝ) (d v : ℝ → E3) (t : ℝ) : E3 :=
  referenceVelocity α t+turn α t (v t+spin α (d t))
def acceleration (α : ℝ) (d v a : ℝ → E3) (t : ℝ) : E3 :=
  physicalAcceleration α e0 t (reference α t)+
    turn α t (a t+(2:ℝ) • spin α (v t)+spin α (spin α (d t)))

theorem position_derivative (α : ℝ) {d v : ℝ → E3} {t : ℝ}
    (hd : HasDerivAt d (v t) t) : HasDerivAt (position α d) (velocity α d v t) t :=
  (reference_derivative α t).add (turn_derivative α hd)

theorem velocity_derivative (α : ℝ) {d v a : ℝ → E3} {t : ℝ}
    (hd : HasDerivAt d (v t) t) (hv : HasDerivAt v (a t) t) :
    HasDerivAt (velocity α d v) (acceleration α d v a t) t := by
  have h := (referenceVelocity_derivative α t).add
    (turn_derivative α (hv.add (spin_derivative α hd)))
  convert h using 1
  simp only [acceleration,Pi.add_apply,map_add,map_smul]
  module

def positionOperator (α : ℝ) : E3 →ₗ[ℝ] E3 := α^2 • linear HarmonicFrame.positionOperator
def velocityOperator (α : ℝ) : E3 →ₗ[ℝ] E3 := α • linear HarmonicFrame.velocityOperator
def quadratic (α : ℝ) (x : E3) : E3 :=
  (α^2*(gravity:ℝ)/7000000) •
    pack (-3*x 0^2+(3/2)*(x 1^2+x 2^2)) (3*x 0*x 1) (3*x 0*x 2)

theorem physical_gradient (α t : ℝ) (x : E3) :
    scale α • Gravity.gradient mu (reference α t) (turn α t x) =
      turn α t (positionOperator α x+spin α (spin α x)) := by
  have h := congrArg (fun x : E3 => α^2 • x) (HarmonicFrame.physical_gradient (α*t) x)
  convert h using 1
  · simp only [scale,smul_smul]; congr 1; ring
  · simp only [turn,positionOperator,spin,LinearMap.smul_apply,map_add,map_smul]
    module

theorem physical_quadratic (α t : ℝ) (x : E3) :
    scale α • ((1/2:ℝ) • Gravity.hessian mu (reference α t) (turn α t x) (turn α t x)) =
      turn α t (quadratic α x) := by
  have hn := pack_norm_sq (x 0) (x 1) (x 2)
  rw [HarmonicFrame.pack_components] at hn
  unfold Gravity.hessian
  rw [reference_norm]
  change scale α • ((1/2:ℝ) • _) = _
  change scale α • ((1/2:ℝ) •
    ((3*mu/7000000^5) • (⟪nominal.p (α*t),HarmonicFrame.turn (α*t) x⟫ • turn α t x+
      ⟪nominal.p (α*t),HarmonicFrame.turn (α*t) x⟫ • turn α t x+
      ⟪turn α t x,turn α t x⟫ • reference α t)-
      (15*mu*⟪nominal.p (α*t),HarmonicFrame.turn (α*t) x⟫*
        ⟪nominal.p (α*t),HarmonicFrame.turn (α*t) x⟫/7000000^7) • reference α t)) = _
  rw [HarmonicFrame.nominal_inner,real_inner_self_eq_norm_sq,turn_norm,hn]
  simp only [reference,nominal_position]
  ext i
  fin_cases i <;>
    simp [scale,quadratic,turn,HarmonicFrame.turn,mix,pack_eq,gravity,mu,Direct.gravityParameter] <;> ring

theorem linear_residual_identity (α t : ℝ) (d v a f : E3) :
    turn α t (a+(2:ℝ) • spin α v+spin α (spin α d))-
      scale α • Gravity.gradient mu (reference α t) (turn α t d)-turn α t f =
    turn α t (a-positionOperator α d-velocityOperator α v-f) := by
  have hv : velocityOperator α v=(-2:ℝ) • spin α v := by
    simp only [velocityOperator,LinearMap.smul_apply,HarmonicFrame.velocity_spin,spin]
    module
  rw [physical_gradient,hv]
  simp only [map_add,map_sub,map_smul]
  module

end GNC.OrbitalComparison.PointingCapFrame
