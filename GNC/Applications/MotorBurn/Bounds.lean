import GNC.Applications.MotorBurn.Mission
import GNC.Analysis.EuclideanBox

/-! Convert a checked component tube to dimensional inertial position and
velocity error. These are errors from the supplied candidate at the same
angle, time and phase, not from the unforced reference or an arrival target.
The velocity bound includes the rotating-frame position correction.
-/
noncomputable section
namespace GNC.MotorBurn
open Matrix ParametricBox Set

/-- Every motion of the complete forced model obeys the tube. This result
does not require selecting the particular solution from the existence proof. -/
theorem motion_enclosed {C : Type} (A : Model C) (S : ℕ → Step C 13)
    (mode : Law) (command : ℕ → Fin 2 → ℚ) (on : ℕ → ℚ) (input : ℕ → Fin 13 → ℚ)
    (hv : ∀ j < 12, (S j).Valid A (field mode (command j) (on j)))
    (hj : ∀ j, j+1 < 12 → (S j).Compatible A (S (j+1)))
    (hT : ∀ j < 12, (S j).duration = stepDuration)
    (hA : ∀ j < 12, (S j).angle = angle)
    (hbudget : ∀ j < 12, ∀ i, A.bound (residual A (field mode (command j) (on j))
      (S j).coefficients i) (S j).duration (S j).angle+input j i ≤ (S j).defect i)
    {θ : ℝ} (hθ : |θ| ≤ (angle : ℝ))
    (hi : ∀ i, |initialState θ i-curve A (S 0).coefficients θ 0 i| ≤ ((S 0).initialError i : ℝ))
    {w : ℕ → ℝ → Vec3}
    (hw : ∀ j < 12, ∀ t ∈ Icc (0 : ℝ) (stepDuration : ℝ), ∀ i,
      |inputLift (w j t) i| ≤ (input j i : ℝ))
    (x : Motion mode command on w θ) :
    ∀ j < 12, ∀ t ∈ Icc (0 : ℝ) (stepDuration : ℝ), ∀ i,
      |x.state j t i-curve A (S j).coefficients θ t i| < ((S j).error i : ℝ) := by
  have step (j : ℕ) (hj : j < 12)
      (hi : ∀ i, |x.state j 0 i-curve A (S j).coefficients θ 0 i| ≤ ((S j).initialError i : ℝ)) :
      ∀ t ∈ Icc (0 : ℝ) (stepDuration : ℝ), ∀ i,
        |x.state j t i-curve A (S j).coefficients θ t i| < ((S j).error i : ℝ) := by
    have he := forced_step_sound A (S j) (field mode (command j) (on j)) (hv j hj)
      θ (by rw [hA j hj]; exact hθ) (x.state j) (x.continuous j hj)
      (fun t => inputLift (w j t)) (input j) (hbudget j hj)
      (fun t ht _ => hw j hj t (by simpa only [hT j hj] using ht))
      (by
        intro t ht _
        have hd := x.derivative j hj t (by simpa only [hT j hj] using ht)
        simpa only [field_value, ← Pi.add_def, ← rate_input] using hd) hi
    intro t ht
    exact he t (by simpa only [hT j hj] using ht)
  intro j
  induction j with
  | zero =>
    intro hj
    exact step 0 hj (by simpa only [x.initial] using hi)
  | succ j ih =>
    intro hj'
    have hj0 : j < 12 := by omega
    have hp := ih hj0 stepDuration (by norm_num [stepDuration])
    have hi' := handoff A (S j) (S (j+1)) (hj j hj')
      (by rw [hA j hj0]; exact hθ) (x.state j stepDuration)
      (by simpa only [hT j hj0] using (fun i => (hp i).le))
    rw [← x.join j hj'] at hi'
    exact step (j+1) hj' hi'

def positionDifference (z q : Fin 13 → ℝ) : Vec3 :=
  ![z 0-q 0,z 1-q 1,z 2-q 2]

def velocityDifference (z q : Fin 13 → ℝ) : Vec3 :=
  ![(z 3-q 3)-(z 1-q 1),(z 4-q 4)+(z 0-q 0),z 5-q 5]

def positionBudget (e : Fin 13 → ℚ) : Fin 3 → ℚ := ![e 0,e 1,e 2]
def velocityBudget (e : Fin 13 → ℚ) : Fin 3 → ℚ := ![e 3+e 1,e 4+e 0,e 5]

theorem reconstruction_differences (z q : Fin 13 → ℝ) (phase : ℝ) :
    CircularRendezvous3D.inertialPosition phase (project z)-
        CircularRendezvous3D.inertialPosition phase (project q) =
      rotate (AxisRotation.zRotation phase) (positionDifference z q) ∧
    CircularRendezvous3D.inertialVelocity phase (project z)-
        CircularRendezvous3D.inertialVelocity phase (project q) =
      rotate (AxisRotation.zRotation phase) (velocityDifference z q) := by
  constructor
  · simp only [CircularRendezvous3D.inertialPosition, ← rotate_sub]
    congr 1
    ext i
    fin_cases i <;> simp [CircularRendezvous3D.position, project, first, firstIndex,
      ApproachGate.project, positionDifference, Matrix.cons_val_two,
      Matrix.vecHead, Matrix.vecTail] <;> ring
  · simp only [CircularRendezvous3D.inertialVelocity, ← rotate_sub]
    congr 1
    ext i
    fin_cases i <;> simp [CircularRendezvous3D.localInertialVelocity, project, first,
      firstIndex, ApproachGate.project, velocityDifference, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail] <;> ring

theorem difference_components (z q : Fin 13 → ℝ) (e : Fin 13 → ℚ)
    (he : ∀ i, |z i-q i| ≤ (e i : ℝ)) :
    (∀ i, |positionDifference z q i| ≤ (positionBudget e i : ℝ)) ∧
    (∀ i, |velocityDifference z q i| ≤ (velocityBudget e i : ℝ)) := by
  constructor
  · intro i
    fin_cases i
    · exact he 0
    · exact he 1
    · exact he 2
  · intro i
    fin_cases i
    · change |(z 3-q 3)-(z 1-q 1)| ≤ ((e 3+e 1 : ℚ) : ℝ)
      exact (abs_sub _ _).trans (by push_cast; exact add_le_add (he 3) (he 1))
    · change |(z 4-q 4)+(z 0-q 0)| ≤ ((e 4+e 0 : ℚ) : ℝ)
      exact (abs_add_le _ _).trans (by push_cast; exact add_le_add (he 4) (he 0))
    · exact he 5

/-- The squared budgets are rational inequalities checked without a
floating-point square root. The final norms are in metres and metres/second. -/
theorem enclosure_norms (z q : Fin 13 → ℝ) (e : Fin 13 → ℚ) (phase : ℝ)
    (P V : ℚ) (hP : 0 ≤ P) (hV : 0 ≤ V)
    (he : ∀ i, |z i-q i| ≤ (e i : ℝ))
    (hp : ApproachGate.radiusSI^2*(∑ i, positionBudget e i^2) ≤ P^2)
    (hv : ApproachGate.speedSquaredSI*(∑ i, velocityBudget e i^2) ≤ V^2) :
    enorm ((ApproachGate.radiusSI : ℝ) •
      (CircularRendezvous3D.inertialPosition phase (project z)-
       CircularRendezvous3D.inertialPosition phase (project q))) ≤ (P : ℝ) ∧
    enorm (ApproachGate.speedSI •
      (CircularRendezvous3D.inertialVelocity phase (project z)-
       CircularRendezvous3D.inertialVelocity phase (project q))) ≤ (V : ℝ) := by
  have hc := difference_components z q e he
  rw [(reconstruction_differences z q phase).1, (reconstruction_differences z q phase).2]
  simp only [← rotate_smul, rotate_enorm]
  constructor
  · apply enorm_le_of_component_bounds _
      (fun i => (ApproachGate.radiusSI : ℝ)*(positionBudget e i : ℝ))
    · intro i
      simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
      rw [abs_of_nonneg (by norm_num [ApproachGate.radiusSI])]
      exact mul_le_mul_of_nonneg_left (hc.1 i) (by norm_num [ApproachGate.radiusSI])
    · exact_mod_cast hP
    · have h : (ApproachGate.radiusSI : ℝ)^2*(∑ i, (positionBudget e i : ℝ)^2) ≤ (P : ℝ)^2 := by
        exact_mod_cast hp
      simpa only [mul_pow, Finset.mul_sum] using h
  · apply enorm_le_of_component_bounds _
      (fun i => ApproachGate.speedSI*(velocityBudget e i : ℝ))
    · intro i
      simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
      rw [abs_of_pos ApproachGate.speed_positive]
      exact mul_le_mul_of_nonneg_left (hc.2 i) ApproachGate.speed_positive.le
    · exact_mod_cast hV
    · have h : (ApproachGate.speedSquaredSI : ℝ)*(∑ i, (velocityBudget e i : ℝ)^2) ≤ (V : ℝ)^2 := by
        exact_mod_cast hv
      have hs : ApproachGate.speedSI^2 = (ApproachGate.speedSquaredSI : ℝ) :=
        Real.sq_sqrt (by norm_num [ApproachGate.speedSquaredSI])
      simpa only [mul_pow, hs, Finset.mul_sum] using h

end GNC.MotorBurn
