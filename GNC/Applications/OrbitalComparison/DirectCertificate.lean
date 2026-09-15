import GNC.Control.QuadraticTube

/-! A direct, exact-rational certificate for the 600 s inverse-square example.
The analytic response gain is connected to the actual ODE in PredictionBounds.
There is no sampled maximum, numerical integrator allowance, or radius search.
Constants are physical inputs and coefficients of a proved supersolution.
-/
namespace GNC.OrbitalComparison.Direct

/-- Mission inputs in SI units: radius, circular reference angular speed,
burn duration and pointing angle. Thrust is derived from force balance. -/
def gravityParameter : ℚ := 398600441800000
def referenceRadius : ℚ := 7000000
def angularSpeed : ℚ := 1077/1000000
def duration : ℚ := 600
def pointingAngle : ℚ := 7/20
def thrust : ℚ := gravityParameter/referenceRadius^2-angularSpeed^2*referenceRadius

def positionGain : ℚ :=
  1/2+17/480+289/288000+4913/317664000
def velocityGain : ℚ := 1+17/120+289/48000+4913/39708000
def forceBudget : ℚ := duration^2*thrust*pointingAngle
def nominalRadius : ℚ := positionGain*forceBudget
def curvature : ℚ := 360000*3*398600441800000/(7000000-2*nominalRadius)^4
def nonlinearGain : ℚ := positionGain*curvature
def tubeRadius : ℚ := nominalRadius/(1-2*nominalRadius*nonlinearGain)
def positionError : ℚ := nonlinearGain*tubeRadius^2
def velocityError : ℚ := velocityGain*curvature*tubeRadius^2/600

theorem admissible :
    0 < nominalRadius ∧ 0 ≤ nonlinearGain ∧
      4*nominalRadius*nonlinearGain < 1 ∧ 2*nominalRadius < 7000000 := by
  norm_num [nominalRadius, nonlinearGain, positionGain, forceBudget, curvature,
    duration, thrust, pointingAngle, gravityParameter, referenceRadius, angularSpeed]

theorem computation :
    QuadraticTube.closedRadius? nominalRadius nonlinearGain = some tubeRadius := by
  have hc : 0 < nominalRadius ∧ 0 ≤ nonlinearGain ∧
      4*nominalRadius*nonlinearGain < 1 :=
    ⟨admissible.1, admissible.2.1, admissible.2.2.1⟩
  simp only [QuadraticTube.closedRadius?, if_pos hc, tubeRadius]

/-- Decimal statements are outward enclosures of exact rationals. -/
theorem numerical_enclosures :
    1027374/1000 < nominalRadius ∧ nominalRadius < 1027375/1000 ∧
    1027577/1000 < tubeRadius ∧ tubeRadius < 1027578/1000 ∧
    positionError < 117/1000 ∧ velocityError < 418/1000000 := by
  norm_num [nominalRadius, positionGain, velocityGain, forceBudget, curvature,
    nonlinearGain, tubeRadius, positionError, velocityError,
    duration, thrust, pointingAngle, gravityParameter, referenceRadius, angularSpeed]

/-- The fixed validity domain costs less than 0.064 percent in the gravity
curvature coefficient relative to evaluating it at the final direct radius.
This compares those coefficients, not different physical trajectories. -/
theorem domain_conservatism :
    ((7000000-tubeRadius)/(7000000-2*nominalRadius))^4 < 100064/100000 := by
  norm_num [tubeRadius, nominalRadius, positionGain, forceBudget, nonlinearGain, curvature,
    duration, thrust, pointingAngle, gravityParameter, referenceRadius, angularSpeed]

end GNC.OrbitalComparison.Direct
