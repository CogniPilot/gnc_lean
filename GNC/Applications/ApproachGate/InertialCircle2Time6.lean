import GNC.Applications.ApproachGate.Mission
import GNC.Applications.ApproachGate.Data.InertialCircle2Time6Step00
import GNC.Applications.ApproachGate.Data.InertialCircle2Time6Step01
import GNC.Applications.ApproachGate.Data.InertialCircle2Time6Step02
import GNC.Applications.ApproachGate.Data.InertialCircle2Time6Step03
import GNC.Applications.ApproachGate.Data.InertialCircle2Time6Step04
import GNC.Applications.ApproachGate.Data.InertialCircle2Time6Step05
import GNC.Applications.ApproachGate.Data.InertialCircle2Time6Step06
import GNC.Applications.ApproachGate.Data.InertialCircle2Time6Step07
import GNC.Applications.ApproachGate.Data.InertialCircle2Time6Step08
import GNC.Applications.ApproachGate.Data.InertialCircle2Time6Step09
import GNC.Applications.ApproachGate.Data.InertialCircle2Time6Step10
import GNC.Applications.ApproachGate.Data.InertialCircle2Time6Step11

/-! Generated exact certificate composition. The kernel checks all segment
handoffs and the terminal norm budget, including velocity frame correction.
Position and velocity display bounds are rounded outward, respectively to
0.01 m and 0.0001 m/s; they are conclusions, not physical error assumptions.
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace GNC.ApproachGate.InertialCircle2Time6
open ParametricBox PolynomialODE Set
def steps : ℕ → Step CirclePolynomial.Coefficients 11
  | 0 => Data.InertialCircle2Time6Step00.data
  | 1 => Data.InertialCircle2Time6Step01.data
  | 2 => Data.InertialCircle2Time6Step02.data
  | 3 => Data.InertialCircle2Time6Step03.data
  | 4 => Data.InertialCircle2Time6Step04.data
  | 5 => Data.InertialCircle2Time6Step05.data
  | 6 => Data.InertialCircle2Time6Step06.data
  | 7 => Data.InertialCircle2Time6Step07.data
  | 8 => Data.InertialCircle2Time6Step08.data
  | 9 => Data.InertialCircle2Time6Step09.data
  | 10 => Data.InertialCircle2Time6Step10.data
  | _ => Data.InertialCircle2Time6Step11.data
def command : ℕ → Fin 2 → ℚ
  | 0 => Data.InertialCircle2Time6Step00.command
  | 1 => Data.InertialCircle2Time6Step01.command
  | 2 => Data.InertialCircle2Time6Step02.command
  | 3 => Data.InertialCircle2Time6Step03.command
  | 4 => Data.InertialCircle2Time6Step04.command
  | 5 => Data.InertialCircle2Time6Step05.command
  | 6 => Data.InertialCircle2Time6Step06.command
  | 7 => Data.InertialCircle2Time6Step07.command
  | 8 => Data.InertialCircle2Time6Step08.command
  | 9 => Data.InertialCircle2Time6Step09.command
  | 10 => Data.InertialCircle2Time6Step10.command
  | _ => Data.InertialCircle2Time6Step11.command
theorem valid (j : ℕ) (hj : j < 12) :
    (steps j).Valid circle (field .inertial (command j)) := by
  interval_cases j
  · exact Data.InertialCircle2Time6Step00.valid
  · exact Data.InertialCircle2Time6Step01.valid
  · exact Data.InertialCircle2Time6Step02.valid
  · exact Data.InertialCircle2Time6Step03.valid
  · exact Data.InertialCircle2Time6Step04.valid
  · exact Data.InertialCircle2Time6Step05.valid
  · exact Data.InertialCircle2Time6Step06.valid
  · exact Data.InertialCircle2Time6Step07.valid
  · exact Data.InertialCircle2Time6Step08.valid
  · exact Data.InertialCircle2Time6Step09.valid
  · exact Data.InertialCircle2Time6Step10.valid
  · exact Data.InertialCircle2Time6Step11.valid
theorem joins (j : ℕ) (hj : j+1 < 12) :
    (steps j).Compatible circle (steps (j+1)) := by
  have hj' : j ≤ 10 := by omega
  interval_cases j <;> decide +kernel
theorem numbers (j : ℕ) (hj : j < 12) :
    (steps j).duration = stepDuration ∧ (steps j).angle = angle ∧
    (∀ i, (steps j).region i ≤ 2) ∧ (steps j).region 6 < 1 := by
  interval_cases j <;> decide +kernel
theorem initial_bound {θ : ℝ} (hθ : |θ| ≤ (angle : ℝ)) :
    ∀ i, |lift θ 0 (fun i => (initialState i : ℝ)) i-
      ParametricBox.curve circle (steps 0).coefficients θ 0 i| ≤ ((steps 0).initialError i : ℝ) := by
  refine initial_enclosure circle (steps 0) initialCircle (fun _ => 0)
    (by intro i; fin_cases i <;> decide +kernel) hθ _ ?_
  intro i
  have hi := congrFun (initial_circle_value θ 0) i
  change circle.value (initialCircle i) 0 θ = _ at hi
  rw [hi]
  norm_num
def positionBound : ℚ := (171/20)
def velocityBound : ℚ := (99/10000)
theorem terminal_numbers :
    radiusSI^2*(∑ i, (queryRadius circle (steps 11) (positionQuery i))^2) ≤ positionBound^2 ∧
    speedSquaredSI*(∑ i, (queryRadius circle (steps 11) (velocityQuery i))^2) ≤ velocityBound^2 := by
  constructor <;> decide +kernel
theorem meets_gate : positionBound ≤ 25 ∧ velocityBound ≤ 1/20 := by decide +kernel
def predictionPositionBound : ℚ := (1/800000)
theorem prediction_numbers (j : ℕ) (hj : j < 12) :
    radiusSI^2*((steps j).error 0^2+(steps j).error 1^2+(steps j).error 2^2) ≤ predictionPositionBound^2 := by
  interval_cases j <;> decide +kernel
theorem acceleration_numbers (j : ℕ) (hj : j < 12) :
    (speedSquaredSI/radiusSI)^2*((command j 0)^2+(command j 1)^2) ≤ (1/25 : ℚ)^2 := by
  interval_cases j <;> decide +kernel

theorem every_motion {θ : ℝ} (hθ : |θ| ≤ Real.pi/180) (x : Motion .inertial command θ) :
    enorm ((radiusSI : ℝ) • positionError (x.state 11 stepDuration)) ≤ (positionBound : ℝ) ∧
    enorm (Real.sqrt (speedSquaredSI : ℝ) • velocityError (x.state 11 stepDuration)) ≤ (velocityBound : ℝ) := by
  have ha := one_degree_enclosed hθ
  have he := motion_enclosed circle steps .inertial command valid joins
    (fun j hj => (numbers j hj).1) (fun j hj => (numbers j hj).2.1) θ ha (initial_bound ha) x
  apply terminal_norms circle (steps 11) (field .inertial (command 11)) (valid 11 (by norm_num))
    positionBound velocityBound (by decide +kernel) (by decide +kernel)
    terminal_numbers.1 terminal_numbers.2 ha (x.state 11 stepDuration)
  intro i
  exact (he 11 (by norm_num) stepDuration (by norm_num [stepDuration]) i).le

/-- Non-vacuous arrival guarantee for every allowed real pointing angle.
The projected motion satisfies the original three-dimensional inverse-square
equations, with positive physical radius throughout every burn/coast arc. -/
theorem exists_physical_and_safe {θ : ℝ} (hθ : |θ| ≤ Real.pi/180) :
    ∃ x : Motion .inertial command θ,
      (∀ j < 12, ∀ t ∈ Icc (0 : ℝ) (stepDuration : ℝ),
        0 < CircularRendezvous3D.radius (project (x.state j t)) ∧
        HasDerivAt (fun s => project (x.state j s))
          (CircularRendezvous3D.physicalRate
            (source .inertial θ ((j : ℝ)*stepDuration+t) (fun i => (command j i : ℝ)))
            (project (x.state j t))) t) ∧
      enorm ((radiusSI : ℝ) • positionError (x.state 11 stepDuration)) ≤ (positionBound : ℝ) ∧
      enorm (Real.sqrt (speedSquaredSI : ℝ) • velocityError (x.state 11 stepDuration)) ≤ (velocityBound : ℝ) := by
  have ha := one_degree_enclosed hθ
  obtain ⟨x, he⟩ := exists_motion circle steps .inertial command valid joins
    (fun j hj => (numbers j hj).1) (fun j hj => (numbers j hj).2.1)
    (fun j hj => (numbers j hj).2.2.1) θ ha (initial_bound ha)
  have hu := positive_inverse_radius circle steps .inertial command valid
    (fun j hj => (numbers j hj).1) (fun j hj => (numbers j hj).2.1)
    (fun j hj => (numbers j hj).2.2.2) ha x he
  exact ⟨x, x.physical hu, every_motion hθ x⟩
end GNC.ApproachGate.InertialCircle2Time6
