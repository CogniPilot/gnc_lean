import GNC.Dynamics.ForcedLogDynamics

/-! Equivalence of the physical component equations (4) and the matrix
equations (5), and the forced log theorem with component-ODE hypotheses. -/
noncomputable section
open Matrix Real
open scoped Matrix Matrix.Norms.Operator
namespace GNC

def physicalDerivative (X : SE23) (a w g : Vec3) : Mat5 :=
  let D := X.rot.val*skew w
  let b := rotate X.rot a+g
  !![D 0 0,D 0 1,D 0 2,b 0,X.vel 0;
     D 1 0,D 1 1,D 1 2,b 1,X.vel 1;
     D 2 0,D 2 1,D 2 2,b 2,X.vel 2;
     0,0,0,0,0; 0,0,0,0,0]

set_option maxHeartbeats 800000 in
theorem spacecraftDerivative_components (X : SE23) (a w g : Vec3) :
    spacecraftDerivative X (Jacobian.controlInput a w) g = physicalDerivative X a w g := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spacecraftDerivative, Jacobian.controlInput, hat, velocityOnly, kinematicC,
      SE23.toMatrix, physicalDerivative, rotate, skew, Matrix.mul_apply, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ] <;> ring

/-- The three physical equations, allowing a general inertial gravity vector
at the time under consideration. -/
def SpacecraftODEAt (X : ℝ → SE23) (a w g : Vec3) (t : ℝ) : Prop :=
  HasDerivAt (fun s => (X s).pos) (X t).vel t ∧
  HasDerivAt (fun s => (X s).vel) (rotate (X t).rot a+g) t ∧
  HasDerivAt (fun s => (X s).rot.val) ((X t).rot.val*skew w) t

theorem spacecraft_ode_iff (X : ℝ → SE23) (a w g : Vec3) (t : ℝ) :
    SpacecraftODEAt X a w g t ↔
      HasDerivAt (fun s => SE23.toMatrix (X s))
        (spacecraftDerivative (X t) (Jacobian.controlInput a w) g) t := by
  rw [spacecraftDerivative_components]
  constructor
  · rintro ⟨hp,hv,hr⟩
    apply hasDerivAt_pi.mpr
    intro i
    apply hasDerivAt_pi.mpr
    intro j
    fin_cases i <;> fin_cases j <;> first
      | exact hasDerivAt_pi.mp (hasDerivAt_pi.mp hr _) _
      | exact hasDerivAt_pi.mp hv _
      | exact hasDerivAt_pi.mp hp _
      | exact hasDerivAt_const t (0:ℝ)
      | exact hasDerivAt_const t (1:ℝ)
  · intro h
    refine ⟨hasDerivAt_pi.mpr ?_,hasDerivAt_pi.mpr ?_,hasDerivAt_pi.mpr ?_⟩
    · intro i
      have hi := hasDerivAt_pi.mp (hasDerivAt_pi.mp h (i.castAdd 2)) 4
      fin_cases i <;> exact hi
    · intro i
      have hi := hasDerivAt_pi.mp (hasDerivAt_pi.mp h (i.castAdd 2)) 3
      fin_cases i <;> exact hi
    · intro i
      apply hasDerivAt_pi.mpr
      intro j
      have hi := hasDerivAt_pi.mp (hasDerivAt_pi.mp h (i.castAdd 2)) (j.castAdd 2)
      fin_cases i <;> fin_cases j <;> exact hi

/-- Proposition 1 in the reference-body gravity form, directly from (4). -/
theorem physical_log_equation {X Y : ℝ → SE23} {x : ℝ → LogState}
    {dx : LogState} {a w abar wbar g gbar : Vec3} {t : ℝ}
    (hX : SpacecraftODEAt X a w g t) (hY : SpacecraftODEAt Y abar wbar gbar t)
    (hx : HasDerivAt x dx t) (he : ∀ s, SE23.error (Y s) (X s) = groupExp (x s))
    (hθπ : enorm (x t 2) < π) :
    dx = logDrift (Jacobian.controlInput a w) (x t) + Jacobian.blockInverse (x t)
      (Jacobian.controlInput (a-abar) (w-wbar)+velocityOnly (rotate (Y t).rot⁻¹ (g-gbar))) := by
  simpa only [controlInput_sub] using spacecraft_log_equation
    ((spacecraft_ode_iff X a w g t).mp hX)
    ((spacecraft_ode_iff Y abar wbar gbar t).mp hY) hx he hθπ

end GNC
