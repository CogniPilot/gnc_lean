import GNC.Lie.RightJacobian

/-! Checks of the supplied log-linear backstepping manuscript.
The displayed inverse Jacobians fail at the identity. The energy counterexample
refutes the claimed unweighted Lyapunov estimate, not stability of the cascade.
-/
noncomputable section
open Matrix
namespace GNC.BacksteppingReview

theorem actual_left_inverse_zero (y : LogState) :
    Jacobian.blockInverse 0 y = y := by
  ext i j
  fin_cases i <;> simp [Jacobian.blockInverse, Jacobian.inverseAt, Jacobian.Q_at_zero]

theorem actual_right_inverse_zero (y : LogState) :
    Jacobian.blockRightInverse 0 y = y := by
  simpa [Jacobian.blockRightInverse] using actual_left_inverse_zero y

/-- The continuous zero-rotation specialization of the paper's Eq. (32). -/
def paperLeftAtZero (y : LogState) : LogState :=
  ![y 0 - (1/2:ℝ) • y 1, y 1, y 2]

/-- The continuous zero-rotation specialization of the paper's Eq. (33). -/
def paperRightAtZero (y : LogState) : LogState :=
  ![y 0 + (1/2:ℝ) • y 1, y 1, y 2]

def velocityDirection : LogState := ![0, ![1,0,0], 0]

theorem paper_left_inverse_counterexample :
    paperLeftAtZero velocityDirection ≠ Jacobian.blockInverse 0 velocityDirection := by
  rw [actual_left_inverse_zero]
  intro h
  have := congrArg (fun z : LogState => z 0 0) h
  norm_num [paperLeftAtZero, velocityDirection] at this

theorem paper_right_inverse_counterexample :
    paperRightAtZero velocityDirection ≠ Jacobian.blockRightInverse 0 velocityDirection := by
  rw [actual_right_inverse_zero]
  intro h
  have := congrArg (fun z : LogState => z 0 0) h
  norm_num [paperRightAtZero, velocityDirection] at this

/-- An actual invariant scalar subsystem of Eqs. (50)--(52), with B = 0
and zero reference rotation. Each scalar lies on the same fixed unit axis. -/
def energy (p v r : ℝ) : ℝ := (p^2 + v^2 + r^2)/2

theorem energy_derivative {p v r : ℝ → ℝ} {t kp kv kr : ℝ}
    (hp : HasDerivAt p (-kp*p t + v t) t)
    (hv : HasDerivAt v (-kv*v t) t)
    (hr : HasDerivAt r (-kr*r t) t) :
    HasDerivAt (fun s => energy (p s) (v s) (r s))
      (-kp*(p t)^2 + p t*v t - kv*(v t)^2 - kr*(r t)^2) t := by
  convert (((hp.pow 2).add (hv.pow 2)).add (hr.pow 2)).div_const 2 using 1
  dsimp [energy]
  ring

/-- All positive scalar gains satisfy the paper's condition when B = 0.
At p = v = 1, r = 0, its proposed unweighted V increases. -/
theorem unweighted_lyapunov_counterexample :
    (0:ℝ) < (1/10:ℝ) ∧ (0:ℝ) < (1/10:ℝ) ∧
    (1:ℝ) > 0^2/(2*(1/10:ℝ)) ∧
    -(1/10:ℝ)*1^2 + 1*1 - (1/10:ℝ)*1^2 - 1*0^2 = (4/5:ℝ) ∧
    ¬ (-(1/10:ℝ)*1^2 + 1*1 - (1/10:ℝ)*1^2 - 1*0^2 ≤
      -2*(1/20:ℝ)*energy 1 1 0) := by
  norm_num [energy]

/-- The exact term omitted when combining the two Young inequalities.
The velocity coefficient is -kv/2 + 1/(2*kp), not -kv/2. -/
theorem corrected_young_collection (kp kv kr b p v r : ℝ) :
    -kp*p^2 + (kp/2*p^2 + 1/(2*kp)*v^2) - kv*v^2 +
      (kv/2*v^2 + b^2/(2*kv)*r^2) - kr*r^2 =
    -(kp/2)*p^2 - (kv/2 - 1/(2*kp))*v^2 -
      (kr - b^2/(2*kv))*r^2 := by
  ring

/-- A weighted scalar cascade estimate, a checked algebraic ingredient for
a stronger stability theorem. Existence and vector trajectory decay remain
separate obligations. The hypotheses bound the two cross terms. -/
theorem weighted_cascade_estimate (kp kv kr b wp wv wr p v r : ℝ)
    (hpv : wp*p*v ≤ wp*kp/2*p^2 + wp/(2*kp)*v^2)
    (hvr : wv*b*v*r ≤ wv*kv/2*v^2 + wv*b^2/(2*kv)*r^2) :
    -wp*kp*p^2 + wp*p*v - wv*kv*v^2 + wv*b*v*r - wr*kr*r^2 ≤
      -(wp*kp/2)*p^2 -
      (wv*kv/2 - wp/(2*kp))*v^2 -
      (wr*kr - wv*b^2/(2*kv))*r^2 := by
  nlinarith

end GNC.BacksteppingReview
