import GNC.Analysis.MonomialRational
import GNC.Analysis.LinearResponsePolynomial
import GNC.Analysis.TrigonometricPolynomial

/-! Exact rational data for the 600 s powered-circle example.
Coefficients are proposals; the consuming theorems check their residual.
The constants are dimensionless physical inputs, not fitted allowances. -/
namespace GNC.OrbitalComparison.FiniteResponseData
open LinearResponsePolynomial PolynomialBounds PolynomialTimeProfile
open Planning.PolynomialKernel

def mu : ℚ := 398600441800000 * 600^2 / 7000000^3
def thrust : ℚ := (1/10000) * 600^2 / 7000000
def speed2 : ℚ := mu-thrust
def gamma : ℚ := mu/speed2
def beta : ℚ := thrust/speed2
def theta : ℚ := 1/50
def horizon : ℚ := ((1+speed2)^2+4*speed2)/(4*(1+speed2))
def delta : ℚ := horizon^17/355687428096000

def c : List ℚ := TrigonometricPolynomial.cosine
def s : List ℚ := TrigonometricPolynomial.sine

def gradient : Coefficients 3 3 :=
  ![![scale gamma (add (scale 3 (multiply c c)) [-1]), scale (3*gamma) (multiply c s), []],
    ![scale (3*gamma) (multiply c s), scale gamma (add (scale 3 (multiply s s)) [-1]), []],
    ![[], [], [-gamma]]]

def forcing : Coefficients 3 3 :=
  ![![[], [], scale (-beta) s], ![[], [], scale beta c],
    ![scale beta s, scale (-beta) c, []]]

def coefficients : Coefficients 3 3 :=
  ![![[0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, (-12250/5978933127), 0, (9765695817850/11915880445712666043), 0, (-52132617816992508000625/284977009336971936511922825844)]],
    ![[0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, (12250/1992977709), 0, (-12207063498875/11915880445712666043), 0, (131374196899291716161575/284977009336971936511922825844), 0]],
    ![[0, 0, 0, (12250/5978933127), 0, (-2441412699775/11915880445712666043), 0, (2085304712780542320025/284977009336971936511922825844)],
    [0, 0, (-12250/1992977709), 0, (12207063498875/11915880445712666043), 0, (-14597132989463796240175/284977009336971936511922825844), 0],
    [0, 0, 0, 0, 0, 0, 0, 0]]]

def defect : Coefficients 3 3 := residual gradient coefficients forcing
def radius : ℚ := budget coefficients (fun _ => theta) horizon
def polynomialError : ℚ := budget defect (fun _ => theta) horizon
-- Reference approximation: ||q-qp|| <= 2 delta t^17.
-- Force approximation: theta beta ||q-qp||.
def trigError : ℚ := 3*gamma*(2*delta)*(2+2*delta)*radius + 2*theta*beta*delta
def error : ℚ := speed2*(polynomialError+trigError)

theorem inputs : 0<speed2 ∧ 0≤gamma ∧ 0≤beta ∧ 0≤theta ∧
    0≤horizon ∧ horizon≤1 ∧ speed2≤horizon^2 ∧ 0≤delta := by
  decide +kernel

theorem initial_zeros : ∀ i j, zeroPrefix 2 (coefficients i j) := by
  decide +kernel

theorem defect_zeros : ∀ i j, zeroPrefix 6 (defect i j) := by
  decide +kernel

theorem budgets_nonneg : 0≤radius ∧ 0≤polynomialError ∧ 0≤trigError ∧ 0≤error := by
  decide +kernel


-- These are evaluations of the proved envelope, with no residual allowance.
def responseRadius : ℚ := (theta*thrust+error)*MonomialRational.endpoint (2*mu) 0
def gain : ℚ := 2*mu/(1-2*responseRadius)^3
def F2 : ℚ := 2*mu*theta*responseRadius
def F4 : ℚ := 4*mu/(1-responseRadius)^4*responseRadius^2
def predictionBudget : ℚ := error*MonomialRational.endpoint gain 6+
  F2*MonomialRational.endpoint gain 2+F4*MonomialRational.endpoint gain 4
def reconstructionTail : ℚ := theta^2/6+theta^3/24+theta^4/120

theorem closure : 0≤responseRadius ∧ 2*responseRadius<1 ∧ 0≤gain ∧ gain<56 ∧
    (error+F2+F4)*MonomialRational.endpoint gain 0<responseRadius := by
  decide +kernel

/-- One millimeter is the stated accuracy target in meters. Every term on
its left is derived from the physical inputs and the actual coefficients. -/
theorem submillimeter : 7000000*(predictionBudget+reconstructionTail*responseRadius)<1/1000 := by
  decide +kernel

end GNC.OrbitalComparison.FiniteResponseData
