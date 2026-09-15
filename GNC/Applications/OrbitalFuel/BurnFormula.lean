import GNC.Applications.OrbitalFuel.PolynomialTransition
import GNC.Dynamics.PlanarBurnObservable
import GNC.Analysis.IntegralPartition

/-! Exact normalized burn integrals for the stored solar polynomial data.
Each 1/50-unit burn intersects at most three reference cells. Empty final
pieces are allowed; all endpoint and enclosure conditions are explicit.
-/
namespace GNC.Applications.OrbitalFuel.PolynomialBurn
open GNC.PolynomialODE GNC.PolynomialOrbitTransition GNC.PolynomialIntegral
open PolynomialTransition

structure Cell where
  step : Fin 32
  lower : ℚ
  upper : ℚ
  deriving DecidableEq

def Cell.start (c : Cell) : ℚ := c.step.val*(3/160)+c.lower
def Cell.finish (c : Cell) : ℚ := c.step.val*(3/160)+c.upper
def Cell.Valid (c : Cell) : Prop := 0 ≤ c.lower ∧ c.lower ≤ c.upper ∧ c.upper ≤ 3/160
instance (c : Cell) : Decidable c.Valid := by unfold Cell.Valid; infer_instance

def observable (o : Fin 10) : Expr 25 :=
  if h : o.val < 8 then planeObservable ⟨o.val/2,by omega⟩ ⟨o.val%2,by omega⟩
  else normalObservable ⟨o.val-8,by omega⟩

def cellIntegral (c : Cell) (o : Fin 10) : ℚ :=
  integrate ((observable o).coefficients (steps c.step).coefficients) c.lower c.upper

def mean (cells : Fin 3 → Cell) (o : Fin 10) : ℚ :=
  50 * ∑ k : Fin 3, cellIntegral (cells k) o

def burnStart (j : Fin 18) : ℚ := j.val/30+1/150
def burnFinish (j : Fin 18) : ℚ := j.val/30+2/75

theorem burn_duration (j : Fin 18) : burnFinish j-burnStart j = 1/50 := by
  simp only [burnFinish, burnStart]
  ring

theorem burn_range (j : Fin 18) : 0 ≤ burnStart j ∧ burnStart j ≤ burnFinish j ∧ burnFinish j ≤ 3/5 := by
  fin_cases j <;> norm_num [burnStart, burnFinish]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem observation_errors (j : Fin 32) (o : Fin 10) :
    (observable o).differenceMajorant (steps j).region (steps j).error ≤ 1/10^14 := by
  revert j o
  decide +kernel

end GNC.Applications.OrbitalFuel.PolynomialBurn
