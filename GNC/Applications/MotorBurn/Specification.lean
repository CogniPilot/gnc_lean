import GNC.Applications.MotorBurn.Model
import GNC.Applications.ApproachGate.PhysicalInterpretation
import GNC.Applications.Orion.Propulsion

/-! Exact initial-state and propulsion inputs for the synthetic motor burn.
The reference is a 7000 km circular Earth orbit. Four 1/20-time-unit burn
steps precede eight coast steps (about 185.5 s burn and 371.1 s coast).
This is not the Artemis I RPF trajectory or its published 207.1 s burn.
The real normalized mass-flow coefficient is enclosed by a proved rational
interval; that interval is charged in the initial certificate, not discarded.
-/
namespace GNC.MotorBurn
open Matrix ParametricBox

def angle : ℚ := 11/630
def stepDuration : ℚ := 1/20
def betaUpper : ℚ := 310022069000711/1000000000000000
def betaGrid : ℚ := 1/1000000000000000
def betaSquared : ℚ := 27723500000000000000000000000000/288444881701664878115152228819169
def forceCommand : ℚ := (26700/25854)/(398600441800000/7000000^2)
def inputMagnitude : ℚ := forceCommand*(6/5)*(1/100)

def initialCircle : Fin 13 → CirclePolynomial.Coefficients :=
  ![⟨[],[]⟩,⟨[],[]⟩,⟨[],[]⟩,⟨[],[]⟩,⟨[],[]⟩,⟨[],[]⟩,⟨[],[]⟩,
    ⟨[],[[1]]⟩,⟨[[0,1]],[]⟩,⟨[[1]],[]⟩,⟨[],[]⟩,⟨[],[]⟩,⟨[[betaUpper]],[]⟩]

def initialPolynomial (i : Fin 13) : BivariatePolynomial.Coefficients :=
  if i.val = 7 then [TrigonometricPolynomial.sine]
  else if i.val = 8 then BivariatePolynomial.subtract [[1]] [TrigonometricPolynomial.cosine]
  else [[if i.val = 9 then 1 else if i.val = 12 then betaUpper else 0]]

def initialTail (polynomial : Bool) (i : Fin 13) : ℚ :=
  if i.val = 12 then betaGrid else
    if polynomial ∧ (i.val = 7 ∨ i.val = 8) then angle^17/355687428096000 else 0

noncomputable section
open Real Set

def beta : ℝ := ApproachGate.timeSI*Orion.Propulsion.thrust/
  (Orion.Propulsion.initialMass*Orion.Propulsion.exhaust)

def initialState (θ : ℝ) : Fin 13 → ℝ :=
  ![0,0,0,0,0,0,0,sin θ,1-cos θ,1,0,0,beta]

theorem beta_positive : 0 < beta := by
  unfold beta
  apply div_pos
  · exact mul_pos ApproachGate.time_positive (by norm_num [Orion.Propulsion.thrust])
  · exact mul_pos (by norm_num [Orion.Propulsion.initialMass]) Orion.Propulsion.exhaust_positive

theorem beta_square : beta^2 = (betaSquared : ℝ) := by
  have hs := Real.sq_sqrt (by norm_num [ApproachGate.speedSquaredSI] :
    (0 : ℝ) ≤ (ApproachGate.speedSquaredSI : ℝ))
  unfold beta ApproachGate.timeSI ApproachGate.speedSI
  rw [div_pow, mul_pow, div_pow, hs]
  norm_num [betaSquared, ApproachGate.radiusSI, ApproachGate.speedSquaredSI,
    Orion.Propulsion.thrust, Orion.Propulsion.initialMass, Orion.Propulsion.exhaust,
    Orion.Propulsion.specificImpulse, Orion.Propulsion.standardGravity]

theorem beta_interval : (betaUpper-betaGrid : ℚ) ≤ beta ∧ beta ≤ (betaUpper : ℝ) := by
  have hs := beta_square
  have hp := beta_positive
  have hl : ((betaUpper-betaGrid : ℚ) : ℝ)^2 ≤ (betaSquared : ℝ) := by
    norm_num [betaUpper, betaGrid, betaSquared]
  have hu : (betaSquared : ℝ) ≤ (betaUpper : ℝ)^2 := by
    norm_num [betaUpper, betaSquared]
  norm_num [betaUpper, betaGrid] at *
  constructor <;> nlinarith

theorem beta_error : |beta-(betaUpper : ℝ)| ≤ (betaGrid : ℝ) := by
  have h := beta_interval
  push_cast at h
  exact abs_le.mpr ⟨by linarith [h.1], by linarith [h.2]⟩

theorem initial_constraints (θ : ℝ) :
    inverseDefect (initialState θ) = 0 ∧ phaseDefect 0 (initialState θ) = 0 ∧
      mass Orion.Propulsion.initialMass (initialState θ) = Orion.Propulsion.initialMass := by
  norm_num [inverseDefect, phaseDefect, ApproachGate.inverseDefect, ApproachGate.phaseDefect,
    first, firstIndex, initialState, mass]
  change Orion.Propulsion.initialMass/(1+(0 : ℝ)) = Orion.Propulsion.initialMass
  simp

theorem initial_circle_error (θ : ℝ) (i : Fin 13) :
    |initialState θ i-circle.value (initialCircle i) 0 θ| ≤ (initialTail false i : ℝ) := by
  fin_cases i
  all_goals first
    | solve | norm_num [initialState, initialCircle, initialTail, circle,
        CirclePolynomial.value, BivariatePolynomial.value, BivariatePolynomial.slice,
        BivariatePolynomial.row, Planning.PolynomialKernel.evaluate]
    | skip
  simpa [initialState, initialCircle, initialTail, circle, CirclePolynomial.value,
    BivariatePolynomial.value, BivariatePolynomial.slice, BivariatePolynomial.row,
    Planning.PolynomialKernel.evaluate] using beta_error

theorem initial_polynomial_error {θ : ℝ} (hθ : |θ| ≤ (angle : ℝ)) (i : Fin 13) :
    |initialState θ i-polynomial.value (initialPolynomial i) 0 θ| ≤ (initialTail true i : ℝ) := by
  fin_cases i
  all_goals first
    | solve | norm_num [initialState, initialPolynomial, initialTail, polynomial,
        BivariatePolynomial.value, BivariatePolynomial.slice, BivariatePolynomial.row,
        Planning.PolynomialKernel.evaluate]
    | skip
  · have h := ApproachGate.initial_polynomial_error hθ (7 : Fin 11)
    simpa [ApproachGate.lift, ApproachGate.initialPolynomial, ApproachGate.initialTail,
      ParametricBox.curve, initialState, initialPolynomial, initialTail, angle,
      ApproachGate.angle] using h
  · have h := ApproachGate.initial_polynomial_error hθ (8 : Fin 11)
    simpa [ApproachGate.lift, ApproachGate.initialPolynomial, ApproachGate.initialTail,
      ParametricBox.curve, initialState, initialPolynomial, initialTail, angle,
      ApproachGate.angle] using h
  · simpa [initialState, initialPolynomial, initialTail, polynomial,
      BivariatePolynomial.value, BivariatePolynomial.slice, BivariatePolynomial.row,
      Planning.PolynomialKernel.evaluate] using beta_error

end
end GNC.MotorBurn
