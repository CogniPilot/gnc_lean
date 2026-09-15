import GNC.Applications.OrbitalComparison.HarmonicBurn
import GNC.Dynamics.GravityRemainderMonotone

/-! Exact reference-frame calculus for the harmonic burn certificate.
The retained gravity gradient, Coriolis and centrifugal terms are derived
from the physical inertial equations. No rotation series is truncated. -/
noncomputable section
namespace GNC.OrbitalComparison.HarmonicFrame
open SpatialBurn SpatialRotatingFrame SpatialExactNominal UniformCertificate
open HarmonicPolynomial (Operator linear)
open Real Set
open scoped RealInnerProductSpace

theorem pack_components (x : E3) : pack (x 0) (x 1) (x 2) = x := by
  ext i
  fin_cases i <;> simp [pack_eq]

def turn (t : ℝ) : E3 →ₗ[ℝ] E3 where
  toFun x := mix ((omega:ℝ)*t) (x 0) (x 1) (x 2)
  map_add' _ _ := mix_add _ _ _ _ _ _ _
  map_smul' _ _ := mix_smul _ _ _ _ _

theorem turn_norm (t : ℝ) (x : E3) : ‖turn t x‖ = ‖x‖ := by
  change ‖mix ((omega:ℝ)*t) (x 0) (x 1) (x 2)‖ = _
  rw [mix_norm,pack_components]

def spin : E3 →ₗ[ℝ] E3 := linear
  ![![0,-omega,0],![omega,0,0],![0,0,0]]

theorem spin_apply (x : E3) : spin x = pack (-(omega:ℝ)*x 1) ((omega:ℝ)*x 0) 0 := by
  ext i
  fin_cases i <;>
    simp [spin,linear,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,pack_eq]

theorem turn_derivative {x : ℝ → E3} {v : E3} {t : ℝ}
    (hx : HasDerivAt x v t) :
    HasDerivAt (fun s => turn s (x s)) (turn t (v+spin (x t))) t := by
  have hi (i : Fin 3) : HasDerivAt (fun s => x s i) (v i) t :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp_hasDerivAt t hx
  have h := mix_derivative ((hasDerivAt_id t).const_mul (omega:ℝ)) (hi 0) (hi 1) (hi 2)
  convert h using 1
  simp [turn,spin_apply,pack_eq,sub_eq_add_neg]

theorem spin_derivative {x : ℝ → E3} {v : E3} {t : ℝ}
    (hx : HasDerivAt x v t) : HasDerivAt (fun s => spin (x s)) (spin v) t :=
  spin.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hx

theorem spin_bound (x : E3) : ‖spin x‖ ≤ (omega:ℝ)*‖x‖ := by
  have hw : (0:ℝ) ≤ omega := by norm_num [omega,Direct.angularSpeed]
  have hx := pack_norm_sq (x 0) (x 1) (x 2)
  rw [pack_components] at hx
  have hs := pack_norm_sq (-(omega:ℝ)*x 1) ((omega:ℝ)*x 0) 0
  rw [← spin_apply] at hs
  have hxw := congrArg (fun r : ℝ => (omega:ℝ)^2*r) hx
  have hz := mul_nonneg (sq_nonneg (omega:ℝ)) (sq_nonneg (x 2))
  have hp := mul_nonneg hw (norm_nonneg x)
  nlinarith [norm_nonneg (spin x)]

def positionOperator : Operator :=
  ![![2*gravity+omega^2,0,0],![0,-gravity+omega^2,0],![0,0,-gravity]]
def velocityOperator : Operator :=
  ![![0,2*omega,0],![-2*omega,0,0],![0,0,0]]

theorem velocity_spin (x : E3) : linear velocityOperator x = (-2:ℝ) • spin x := by
  ext i
  fin_cases i <;>
    simp [velocityOperator,linear,spin_apply,pack_eq,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  all_goals ring

theorem nominal_inner (t : ℝ) (x : E3) : ⟪nominal.p t,turn t x⟫ = 7000000*x 0 := by
  rw [nominal_position]
  simp [turn,mix,pack_eq,PiLp.inner_apply,Fin.sum_univ_succ]
  change (cos ((omega:ℝ)*t)*x 0-sin ((omega:ℝ)*t)*x 1)*(7000000*cos ((omega:ℝ)*t))+
    (sin ((omega:ℝ)*t)*x 0+cos ((omega:ℝ)*t)*x 1)*(7000000*sin ((omega:ℝ)*t)) = _
  linear_combination 7000000*x 0 * (sin_sq_add_cos_sq ((omega:ℝ)*t))

theorem physical_gradient (t : ℝ) (x : E3) :
    (360000:ℝ) • Gravity.gradient mu (nominal.p t) (turn t x) =
      turn t (linear positionOperator x+spin (spin x)) := by
  rw [Gravity.gradient,nominal_norm,nominal_inner,nominal_position]
  ext i
  fin_cases i <;>
    simp [turn,mix,pack_eq,spin_apply,positionOperator,linear,Matrix.mulVec,dotProduct,
      Fin.sum_univ_succ,gravity,mu,Direct.gravityParameter] <;> ring

def position (d : ℝ → E3) (t : ℝ) : E3 := nominal.p t+turn t (d t)
def velocity (d v : ℝ → E3) (t : ℝ) : E3 := nominal.v t+turn t (v t+spin (d t))
def acceleration (d v a : ℝ → E3) (t : ℝ) : E3 :=
  SpatialFieldCertificate.physicalAcceleration .rtnReferenceOffset 0 t (nominal.p t)+
    turn t (a t+(2:ℝ) • spin (v t)+spin (spin (d t)))

theorem position_derivative {d v : ℝ → E3} {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1)
    (hd : HasDerivAt d (v t) t) : HasDerivAt (position d) (velocity d v t) t :=
  (nominal.derivative_p t ht).add (turn_derivative hd)

theorem velocity_derivative {d v a : ℝ → E3} {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1)
    (hd : HasDerivAt d (v t) t) (hv : HasDerivAt v (a t) t) :
    HasDerivAt (velocity d v) (acceleration d v a t) t := by
  have h := (nominal.derivative_v t ht).add
    (turn_derivative (hv.add (spin_derivative hd)))
  convert h using 1
  simp only [acceleration,Pi.add_apply,map_add,map_smul]
  module

theorem linear_residual_identity (t : ℝ) (d v a f : E3) :
    turn t (a+(2:ℝ) • spin v+spin (spin d))-
      (360000:ℝ) • Gravity.gradient mu (nominal.p t) (turn t d)-turn t f =
    turn t (a-linear positionOperator d-linear velocityOperator v-f) := by
  rw [physical_gradient,velocity_spin]
  simp only [map_add,map_sub,map_smul]
  module

end GNC.OrbitalComparison.HarmonicFrame
