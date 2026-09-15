import GNC.Applications.MotorBurn.Bounds
import GNC.Applications.MotorBurn.Data.RTNSTT2Time6Step00
import GNC.Applications.MotorBurn.Data.RTNSTT2Time6Step01
import GNC.Applications.MotorBurn.Data.RTNSTT2Time6Step02
import GNC.Applications.MotorBurn.Data.RTNSTT2Time6Step03
import GNC.Applications.MotorBurn.Data.RTNSTT2Time6Step04
import GNC.Applications.MotorBurn.Data.RTNSTT2Time6Step05
import GNC.Applications.MotorBurn.Data.RTNSTT2Time6Step06
import GNC.Applications.MotorBurn.Data.RTNSTT2Time6Step07
import GNC.Applications.MotorBurn.Data.RTNSTT2Time6Step08
import GNC.Applications.MotorBurn.Data.RTNSTT2Time6Step09
import GNC.Applications.MotorBurn.Data.RTNSTT2Time6Step10
import GNC.Applications.MotorBurn.Data.RTNSTT2Time6Step11

/-! Exact burn/coast composition for every admissible continuous acceleration
history on each arc. No sampled disturbance history is used as a proof. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace GNC.MotorBurn.RTNSTT2Time6
open ParametricBox Set
def steps : ℕ → Step BivariatePolynomial.Coefficients 13
  | 0 => Data.RTNSTT2Time6Step00.data
  | 1 => Data.RTNSTT2Time6Step01.data
  | 2 => Data.RTNSTT2Time6Step02.data
  | 3 => Data.RTNSTT2Time6Step03.data
  | 4 => Data.RTNSTT2Time6Step04.data
  | 5 => Data.RTNSTT2Time6Step05.data
  | 6 => Data.RTNSTT2Time6Step06.data
  | 7 => Data.RTNSTT2Time6Step07.data
  | 8 => Data.RTNSTT2Time6Step08.data
  | 9 => Data.RTNSTT2Time6Step09.data
  | 10 => Data.RTNSTT2Time6Step10.data
  | _ => Data.RTNSTT2Time6Step11.data
def command : ℕ → Fin 2 → ℚ
  | 0 => Data.RTNSTT2Time6Step00.command
  | 1 => Data.RTNSTT2Time6Step01.command
  | 2 => Data.RTNSTT2Time6Step02.command
  | 3 => Data.RTNSTT2Time6Step03.command
  | 4 => Data.RTNSTT2Time6Step04.command
  | 5 => Data.RTNSTT2Time6Step05.command
  | 6 => Data.RTNSTT2Time6Step06.command
  | 7 => Data.RTNSTT2Time6Step07.command
  | 8 => Data.RTNSTT2Time6Step08.command
  | 9 => Data.RTNSTT2Time6Step09.command
  | 10 => Data.RTNSTT2Time6Step10.command
  | _ => Data.RTNSTT2Time6Step11.command
def on : ℕ → ℚ
  | 0 => Data.RTNSTT2Time6Step00.on
  | 1 => Data.RTNSTT2Time6Step01.on
  | 2 => Data.RTNSTT2Time6Step02.on
  | 3 => Data.RTNSTT2Time6Step03.on
  | 4 => Data.RTNSTT2Time6Step04.on
  | 5 => Data.RTNSTT2Time6Step05.on
  | 6 => Data.RTNSTT2Time6Step06.on
  | 7 => Data.RTNSTT2Time6Step07.on
  | 8 => Data.RTNSTT2Time6Step08.on
  | 9 => Data.RTNSTT2Time6Step09.on
  | 10 => Data.RTNSTT2Time6Step10.on
  | _ => Data.RTNSTT2Time6Step11.on
def input : ℕ → Fin 13 → ℚ
  | 0 => Data.RTNSTT2Time6Step00.inputBound
  | 1 => Data.RTNSTT2Time6Step01.inputBound
  | 2 => Data.RTNSTT2Time6Step02.inputBound
  | 3 => Data.RTNSTT2Time6Step03.inputBound
  | 4 => Data.RTNSTT2Time6Step04.inputBound
  | 5 => Data.RTNSTT2Time6Step05.inputBound
  | 6 => Data.RTNSTT2Time6Step06.inputBound
  | 7 => Data.RTNSTT2Time6Step07.inputBound
  | 8 => Data.RTNSTT2Time6Step08.inputBound
  | 9 => Data.RTNSTT2Time6Step09.inputBound
  | 10 => Data.RTNSTT2Time6Step10.inputBound
  | _ => Data.RTNSTT2Time6Step11.inputBound
theorem valid (j : ℕ) (hj : j < 12) :
    (steps j).Valid polynomial (field .rtn (command j) (on j)) := by
  interval_cases j
  · exact Data.RTNSTT2Time6Step00.valid
  · exact Data.RTNSTT2Time6Step01.valid
  · exact Data.RTNSTT2Time6Step02.valid
  · exact Data.RTNSTT2Time6Step03.valid
  · exact Data.RTNSTT2Time6Step04.valid
  · exact Data.RTNSTT2Time6Step05.valid
  · exact Data.RTNSTT2Time6Step06.valid
  · exact Data.RTNSTT2Time6Step07.valid
  · exact Data.RTNSTT2Time6Step08.valid
  · exact Data.RTNSTT2Time6Step09.valid
  · exact Data.RTNSTT2Time6Step10.valid
  · exact Data.RTNSTT2Time6Step11.valid
theorem input_budget (j : ℕ) (hj : j < 12) (i : Fin 13) :
    polynomial.bound (residual polynomial (field .rtn (command j) (on j)) (steps j).coefficients i)
      (steps j).duration (steps j).angle+input j i ≤ (steps j).defect i := by
  interval_cases j
  · exact Data.RTNSTT2Time6Step00.input_budget i
  · exact Data.RTNSTT2Time6Step01.input_budget i
  · exact Data.RTNSTT2Time6Step02.input_budget i
  · exact Data.RTNSTT2Time6Step03.input_budget i
  · exact Data.RTNSTT2Time6Step04.input_budget i
  · exact Data.RTNSTT2Time6Step05.input_budget i
  · exact Data.RTNSTT2Time6Step06.input_budget i
  · exact Data.RTNSTT2Time6Step07.input_budget i
  · exact Data.RTNSTT2Time6Step08.input_budget i
  · exact Data.RTNSTT2Time6Step09.input_budget i
  · exact Data.RTNSTT2Time6Step10.input_budget i
  · exact Data.RTNSTT2Time6Step11.input_budget i
theorem joins (j : ℕ) (hj : j+1 < 12) : (steps j).Compatible polynomial (steps (j+1)) := by
  have hj' : j ≤ 10 := by omega
  interval_cases j <;> decide +kernel
theorem numbers (j : ℕ) (hj : j < 12) :
    (steps j).duration = stepDuration ∧ (steps j).angle = angle ∧
    (∀ i, (steps j).region i ≤ 2) ∧ (steps j).region 6 < 1 ∧ (steps j).region 11 < 1 := by
  interval_cases j <;> decide +kernel
theorem schedule (j : ℕ) (hj : j < 12) :
    on j = (if j < 4 then 1 else 0) ∧
    command j = (if j < 4 then ![0,forceCommand] else ![0,0]) ∧
    (∀ i, input j i = if j < 4 ∧ (i.val = 3 ∨ i.val = 4 ∨ i.val = 5)
      then inputMagnitude else 0) := by
  interval_cases j <;> decide +kernel
theorem mass_ratio_numbers (j : ℕ) (hj : j < 12) :
    (steps j).region 11 ≤ 1/5 := by
  interval_cases j <;> decide +kernel
def positionBound : ℕ → ℚ
  | 0 => (2493/50)
  | 1 => (15397/100)
  | 2 => (6351/20)
  | 3 => (54677/100)
  | 4 => (79917/100)
  | 5 => (53949/50)
  | 6 => (139107/100)
  | 7 => (17411/10)
  | 8 => (53391/25)
  | 9 => (258253/100)
  | 10 => (61813/20)
  | _ => (367031/100)
def velocityBound : ℕ → ℚ
  | 0 => (696/625)
  | 1 => (11837/5000)
  | 2 => (2367/625)
  | 3 => (6753/1250)
  | 4 => (30719/5000)
  | 5 => (8769/1250)
  | 6 => (80341/10000)
  | 7 => (92217/10000)
  | 8 => (53017/5000)
  | 9 => (15267/1250)
  | 10 => (14083/1000)
  | _ => (4063/250)
theorem norm_budgets (j : ℕ) (hj : j < 12) :
    0 ≤ positionBound j ∧ 0 ≤ velocityBound j ∧
    ApproachGate.radiusSI^2*(∑ i, positionBudget (steps j).error i^2) ≤ (positionBound j)^2 ∧
    ApproachGate.speedSquaredSI*(∑ i, velocityBudget (steps j).error i^2) ≤ (velocityBound j)^2 := by
  interval_cases j <;> decide +kernel
theorem initial_bound {θ : ℝ} (hθ : |θ| ≤ (angle : ℝ)) :
    ∀ i, |initialState θ i-curve polynomial (steps 0).coefficients θ 0 i| ≤
      ((steps 0).initialError i : ℝ) := by
  exact initial_enclosure polynomial (steps 0) initialPolynomial (initialTail true)
    (by intro i; fin_cases i <;> decide +kernel) hθ (initialState θ) (initial_polynomial_error hθ)

theorem every_motion_enclosed {θ : ℝ} (hθ : |θ| ≤ Real.pi/180)
    {w : ℕ → ℝ → Vec3}
    (hw : ∀ j < 12, ∀ t ∈ Icc (0 : ℝ) (stepDuration : ℝ), ∀ i,
      |inputLift (w j t) i| ≤ (input j i : ℝ))
    (x : Motion .rtn command on w θ) :
    ∀ j < 12, ∀ t ∈ Icc (0 : ℝ) (stepDuration : ℝ), ∀ i,
      |x.state j t i-curve polynomial (steps j).coefficients θ t i| < ((steps j).error i : ℝ) := by
  have ha := ApproachGate.one_degree_enclosed hθ
  exact motion_enclosed polynomial steps .rtn command on input valid joins
    (fun j hj => (numbers j hj).1) (fun j hj => (numbers j hj).2.1)
    input_budget ha (initial_bound ha) hw x

/-- SI error from the parameter-matched candidate, throughout burn and coast.
Display bounds round outward to 0.01 m and 0.0001 m/s. -/
theorem every_motion_error {θ : ℝ} (hθ : |θ| ≤ Real.pi/180)
    {w : ℕ → ℝ → Vec3}
    (hw : ∀ j < 12, ∀ t ∈ Icc (0 : ℝ) (stepDuration : ℝ), ∀ i,
      |inputLift (w j t) i| ≤ (input j i : ℝ))
    (x : Motion .rtn command on w θ) (j : ℕ) (hj : j < 12)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) (stepDuration : ℝ)) (phase : ℝ) :
    enorm ((ApproachGate.radiusSI : ℝ) •
      (CircularRendezvous3D.inertialPosition phase (project (x.state j t))-
       CircularRendezvous3D.inertialPosition phase
         (project (curve polynomial (steps j).coefficients θ t)))) ≤ (positionBound j : ℝ) ∧
    enorm (ApproachGate.speedSI •
      (CircularRendezvous3D.inertialVelocity phase (project (x.state j t))-
       CircularRendezvous3D.inertialVelocity phase
         (project (curve polynomial (steps j).coefficients θ t)))) ≤ (velocityBound j : ℝ) := by
  have hb := norm_budgets j hj
  exact enclosure_norms _ _ (steps j).error phase (positionBound j) (velocityBound j)
    hb.1 hb.2.1 (fun i => (every_motion_enclosed hθ hw x j hj t ht i).le) hb.2.2.1 hb.2.2.2

theorem every_motion_mass_ratio {θ : ℝ} (hθ : |θ| ≤ Real.pi/180)
    {w : ℕ → ℝ → Vec3}
    (hw : ∀ j < 12, ∀ t ∈ Icc (0 : ℝ) (stepDuration : ℝ), ∀ i,
      |inputLift (w j t) i| ≤ (input j i : ℝ))
    (x : Motion .rtn command on w θ) (j : ℕ) (hj : j < 12)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) (stepDuration : ℝ)) :
    0 < 1+x.state j t 11 ∧ 1+x.state j t 11 ≤ 6/5 := by
  have he := every_motion_enclosed hθ hw x j hj t ht
  have hr := region_of_enclosure polynomial (steps j) (field .rtn (command j) (on j)) (valid j hj)
    (by simpa only [(numbers j hj).2.1] using ApproachGate.one_degree_enclosed hθ)
    (by simpa only [(numbers j hj).1] using ht) _ (fun i => (he i).le) (11 : Fin 13)
  have hb := (Rat.cast_le (K := ℝ)).mpr (mass_ratio_numbers j hj)
  norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at hb
  constructor <;> linarith [le_abs_self (x.state j t 11), neg_abs_le (x.state j t 11)]

theorem exists_physical_enclosed {θ : ℝ} (hθ : |θ| ≤ Real.pi/180)
    (w : ℕ → ℝ → Vec3) (hwc : ∀ j < 12, Continuous (w j))
    (hw : ∀ j < 12, ∀ t ∈ Icc (0 : ℝ) (stepDuration : ℝ), ∀ i,
      |inputLift (w j t) i| ≤ (input j i : ℝ)) :
    ∃ x : Motion .rtn command on w θ, x.Physical ∧
      ∀ j < 12, ∀ t ∈ Icc (0 : ℝ) (stepDuration : ℝ), ∀ i,
        |x.state j t i-curve polynomial (steps j).coefficients θ t i| < ((steps j).error i : ℝ) := by
  have ha := ApproachGate.one_degree_enclosed hθ
  obtain ⟨x, he⟩ := exists_motion polynomial steps .rtn command on input valid joins
    (fun j hj => (numbers j hj).1) (fun j hj => (numbers j hj).2.1)
    (fun j hj => (numbers j hj).2.2.1) input_budget θ ha (initial_bound ha) w hwc hw
  have hr (j : ℕ) (hj : j < 12) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) (stepDuration : ℝ)) (i : Fin 13) :
      |x.state j t i| ≤ ((steps j).region i : ℝ) :=
    region_of_enclosure polynomial (steps j) (field .rtn (command j) (on j)) (valid j hj)
      (by simpa only [(numbers j hj).2.1] using ha)
      (by simpa only [(numbers j hj).1] using ht) _ (fun i => (he j hj t ht i).le) i
  refine ⟨x, x.physical ?_ ?_, he⟩
  · intro j hj t ht
    have hb : ((steps j).region 6 : ℝ) < 1 := by exact_mod_cast (numbers j hj).2.2.2.1
    linarith [hr j hj t ht 6, neg_abs_le (x.state j t 6)]
  · intro j hj t ht
    have hb : ((steps j).region 11 : ℝ) < 1 := by exact_mod_cast (numbers j hj).2.2.2.2
    linarith [hr j hj t ht 11, neg_abs_le (x.state j t 11)]
end GNC.MotorBurn.RTNSTT2Time6
