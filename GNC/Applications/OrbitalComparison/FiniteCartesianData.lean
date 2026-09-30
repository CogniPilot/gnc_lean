import GNC.Applications.OrbitalComparison.FiniteResponseData

/-! Finite Cartesian coefficient records for the same powered-circle model.
The two variants differ only in their exact or quadratic rotation features.
All radius and residual scalars are computed from their actual coefficients. -/
namespace GNC.OrbitalComparison.FiniteCartesianData
open LinearResponsePolynomial PolynomialBounds PolynomialTimeProfile
open FiniteResponseData (mu thrust speed2 gamma beta theta horizon delta c s gradient)

inductive Variant where
  | components
  | quadratic
  deriving DecidableEq, Fintype

def featureGain : Variant → ℚ
  | .components => theta
  | .quadratic => theta+theta^2/2

def featureRadii (v : Variant) : Fin 6 → ℚ :=
  ![theta^2/2, featureGain v, featureGain v, theta^2/2, featureGain v, featureGain v]

def forcing : Coefficients 3 6 :=
  ![![scale beta c, scale beta s, [], [], [], []],
    ![[], [], scale beta c, scale beta s, [], []],
    ![[], [], [], [], scale beta c, scale beta s]]

def coefficients : Coefficients 3 6 :=
  ![![[0, 0, (12250/1992977709), 0, (12207288592625/23831760891425332086), 0, (-160568283430341690804425/284977009336971936511922825844), 0, (505641195433933720841508666877375/4543622617488559512214603237083048891168)],
    [0, 0, 0, (12250/5978933127), 0, (2441457718525/23831760891425332086), 0, (-39620763905738515817975/284977009336971936511922825844), 0],
    [0, 0, 0, 0, 0, (2441427706025/2647973432380592454), 0, (-7646115143560918651550/23748084111414328042660235487), 0],
    [0, 0, 0, 0, 0, 0, (2441427706025/11915880445712666043), 0, (-14597128716230004446425/189984672891314624341281883896)],
    [0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0]],
    ![[0, 0, 0, 0, 0, (2441427706025/2647973432380592454), 0, (-13206899939455425470575/47496168222828656085320470974), 0],
    [0, 0, 0, 0, 0, 0, (2441427706025/11915880445712666043), 0, (-27108927084793597060325/379969345782629248682563767792)],
    [0, 0, (12250/1992977709), 0, (-12207063498875/11915880445712666043), 0, (189762728854205676122275/284977009336971936511922825844), 0, (-289531995172571056593597874345675/2271811308744279756107301618541524445584)],
    [0, 0, 0, (12250/5978933127), 0, (-2441412699775/11915880445712666043), 0, (43791398966290513720525/284977009336971936511922825844), 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0]],
    ![[0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, (12250/1992977709), 0, (-12207063498875/11915880445712666043), 0, (14597132989463796240175/284977009336971936511922825844), 0, (-1385330451377225127962414251325/1135905654372139878053650809270762222792)],
    [0, 0, 0, (12250/5978933127), 0, (-2441412699775/11915880445712666043), 0, (2085304712780542320025/284977009336971936511922825844), 0]]]

def defect : Coefficients 3 6 := residual gradient coefficients forcing
def radius (v : Variant) : ℚ := budget coefficients (featureRadii v) horizon
def polynomialError (v : Variant) : ℚ := budget defect (featureRadii v) horizon
def trigError (v : Variant) : ℚ :=
  3*gamma*(2*delta)*(2+2*delta)*radius v+2*featureGain v*beta*delta
def error (v : Variant) : ℚ := speed2*(polynomialError v+trigError v)

def inputError : Variant → ℚ
  | .components => 0
  | .quadratic => FiniteResponseData.reconstructionTail*theta*thrust

def responseRadius (v : Variant) : ℚ := (theta*thrust+inputError v+error v)*MonomialRational.endpoint (2*mu) 0
def gain (v : Variant) : ℚ := 2*mu/(1-2*responseRadius v)^3
def F4 (v : Variant) : ℚ := 3*mu/(1-responseRadius v)^4*responseRadius v^2
def predictionBudget (v : Variant) : ℚ := inputError v*MonomialRational.endpoint (gain v) 0+
  error v*MonomialRational.endpoint (gain v) 7+F4 v*MonomialRational.endpoint (gain v) 4

theorem initial_zeros : ∀ i j, zeroPrefix 2 (coefficients i j) := by decide +kernel

theorem defect_zeros : ∀ i j, zeroPrefix 7 (defect i j) := by decide +kernel

theorem nonnegative (v : Variant) :
    0≤featureGain v ∧ 0≤radius v ∧ 0≤error v ∧ 0 ≤ inputError v := by
  cases v <;> decide +kernel

theorem closure (v : Variant) : 0≤responseRadius v ∧ 2*responseRadius v<1 ∧
    0≤gain v ∧ gain v<56 ∧
    (inputError v+error v+F4 v)*MonomialRational.endpoint (gain v) 0<responseRadius v := by
  cases v <;> decide +kernel

theorem submillimeter (v : Variant) : 7000000*predictionBudget v<1/1000 := by
  cases v <;> decide +kernel

end GNC.OrbitalComparison.FiniteCartesianData
