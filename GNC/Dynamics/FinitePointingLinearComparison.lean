import GNC.Dynamics.LieErrorReconstruction
import GNC.Dynamics.MatrixDynamics

/-! A narrowly scoped, exact coordinate comparison. It contrasts a
first-order physical Cartesian pointing prediction with exact reconstruction
of a linearly propagated logarithmic pointing error. It makes no claim
against nonlinear, higher-order, or redundantly lifted Cartesian methods. -/
noncomputable section
namespace GNC.FinitePointingLinearComparison
open Matrix Real

def physicalPosition (L θ : ℝ) : Vec3 := ![L*(cos θ-1), L*sin θ, 0]
def cartesianFirstOrder (L θ : ℝ) : Vec3 := ![0,L*θ,0]

/-- The nonlinear physical arc is the exact exponential reconstruction
of a translation coordinate linear in the yaw error. Includes θ=0. -/
theorem reconstruction (L θ : ℝ) :
    Jacobian.leftAt (![0,0,θ] : Vec3) (![0,L*θ,0] : Vec3)=physicalPosition L θ := by
  have hk : (![0,0,1] : Vec3) ⬝ᵥ ![0,0,1]=1 := by
    norm_num [dotProduct, Fin.sum_univ_succ]
  have h := factoredTranslation_eq (![0,0,1] : Vec3) (![0,L,0] : Vec3) hk θ
  have hφ : θ • (![0,0,1] : Vec3)=![0,0,θ] := by ext i; fin_cases i <;> simp
  have hp : θ • (![0,L,0] : Vec3)=![0,L*θ,0] := by
    ext i; fin_cases i <;> simp [mul_comm]
  rw [hφ,hp] at h
  rw [←h]
  ext i
  fin_cases i <;> simp [factoredTranslation,physicalPosition,cross_apply] <;> ring

/-- The exact physical endpoint error of the tangent prediction. -/
theorem error_squared (L θ : ℝ) :
    enorm (physicalPosition L θ-cartesianFirstOrder L θ)^2 =
      L^2*((cos θ-1)^2+(sin θ-θ)^2) := by
  rw [enorm_sq]
  simp [lengthSq,physicalPosition,cartesianFirstOrder,dotProduct]
  ring

/-- Missing radial displacement is an analytic error floor, with no
numerical integration tolerance or empirical allowance. -/
theorem radial_error_floor (L θ : ℝ) :
    L*(1-cos θ) ≤ enorm (physicalPosition L θ-cartesianFirstOrder L θ) := by
  have he := error_squared L θ
  have hn := enorm_nonneg (physicalPosition L θ-cartesianFirstOrder L θ)
  nlinarith [sq_nonneg (L*(sin θ-θ))]

theorem half_angle_floor (L θ : ℝ) :
    2*L*sin (θ/2)^2 ≤ enorm (physicalPosition L θ-cartesianFirstOrder L θ) := by
  have h := radial_error_floor L θ
  rw [Jacobian.half_cos θ] at h
  convert h using 1; ring

/-- Explicit linear-log solution for constant body acceleration and
zero body rate in the common-gravity limit. -/
def logSolution (a θ t : ℝ) : LogState :=
  ![![0,(a*t^2/2)*θ,0], ![0,a*t*θ,0], ![0,0,θ]]

theorem log_solution_derivative (a θ t : ℝ) :
    HasDerivAt (logSolution a θ)
      (logDrift (Jacobian.controlInput (![a,0,0] : Vec3) 0) (logSolution a θ t)) t := by
  have hp : HasDerivAt (fun s : ℝ => a*s^2/2*θ) (a*t*θ) t := by
    convert ((((hasDerivAt_id t).pow 2).const_mul a).div_const 2).mul_const θ using 1 <;>
      simp only [id_eq] <;> ring
  have hv : HasDerivAt (fun s : ℝ => a*s*θ) (a*θ) t := by
    simpa only [id_eq, mul_one] using (((hasDerivAt_id t).const_mul a).mul_const θ)
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  fin_cases i <;> fin_cases j <;>
    simp [logSolution,logDrift,ad,Jacobian.controlInput,cross_apply]
  all_goals first
    | exact hasDerivAt_const t _
    | exact hp
    | exact hv

theorem log_endpoint_reconstruction (a θ t : ℝ) :
    Jacobian.leftAt (logSolution a θ t 2) (logSolution a θ t 0)=
      physicalPosition (a*t^2/2) θ := reconstruction (a*t^2/2) θ

end GNC.FinitePointingLinearComparison
