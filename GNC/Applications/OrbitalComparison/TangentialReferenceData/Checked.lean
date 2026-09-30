import GNC.Applications.OrbitalComparison.TangentialReferenceData.Step0
import GNC.Applications.OrbitalComparison.TangentialReferenceData.Step1
import GNC.Applications.OrbitalComparison.TangentialReferenceData.Step2
import GNC.Applications.OrbitalComparison.TangentialReferenceData.Step3
import GNC.Applications.OrbitalComparison.TangentialReferenceData.Step4
import GNC.Applications.OrbitalComparison.TangentialReferenceData.Step5
import GNC.Applications.OrbitalComparison.TangentialReferenceData.Step6
import GNC.Applications.OrbitalComparison.TangentialReferenceData.Step7
import GNC.Applications.OrbitalComparison.TangentialReferenceData.Step8
import GNC.Applications.OrbitalComparison.TangentialReferenceData.Step9
import GNC.Applications.OrbitalComparison.TangentialReferenceData.Step10
import GNC.Applications.OrbitalComparison.TangentialReferenceData.Step11
import GNC.Applications.OrbitalComparison.TangentialReferenceData.Step12
import GNC.Applications.OrbitalComparison.TangentialReferenceData.Step13
import GNC.Applications.OrbitalComparison.TangentialReferenceData.Step14
import GNC.Applications.OrbitalComparison.TangentialReferenceData.Step15
import GNC.Applications.OrbitalComparison.TangentialReferenceData.Step16
import GNC.Applications.OrbitalComparison.TangentialReferenceData.Step17
import GNC.Applications.OrbitalComparison.TangentialReferenceData.Step18
import GNC.Applications.OrbitalComparison.TangentialReferenceData.Step19
import GNC.Applications.OrbitalComparison.TangentialReferenceData.Step20
import GNC.Applications.OrbitalComparison.TangentialReferenceData.Step21
import GNC.Applications.OrbitalComparison.TangentialReferenceData.Step22
import GNC.Applications.OrbitalComparison.TangentialReferenceData.Step23
import GNC.Applications.OrbitalComparison.TangentialReferenceData.Step24
import GNC.Applications.OrbitalComparison.TangentialReferenceData.Step25
import GNC.Applications.OrbitalComparison.TangentialReferenceData.Step26
import GNC.Applications.OrbitalComparison.TangentialReferenceData.Step27
import GNC.Applications.OrbitalComparison.TangentialReferenceData.Step28
import GNC.Applications.OrbitalComparison.TangentialReferenceData.Step29
import GNC.Applications.OrbitalComparison.TangentialReferenceData.Step30
import GNC.Applications.OrbitalComparison.TangentialReferenceData.Step31

namespace GNC.OrbitalComparison.TangentialReferenceData
open PolynomialODE PolynomialOrbit
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def steps : Fin 32 → Step 5 := ![step0, step1, step2, step3, step4, step5, step6, step7, step8, step9, step10, step11, step12, step13, step14, step15, step16, step17, step18, step19, step20, step21, step22, step23, step24, step25, step26, step27, step28, step29, step30, step31]
theorem valid (j : Fin 32) : (steps j).Valid (field alpha) := by
  fin_cases j
  · exact step0_valid
  · exact step1_valid
  · exact step2_valid
  · exact step3_valid
  · exact step4_valid
  · exact step5_valid
  · exact step6_valid
  · exact step7_valid
  · exact step8_valid
  · exact step9_valid
  · exact step10_valid
  · exact step11_valid
  · exact step12_valid
  · exact step13_valid
  · exact step14_valid
  · exact step15_valid
  · exact step16_valid
  · exact step17_valid
  · exact step18_valid
  · exact step19_valid
  · exact step20_valid
  · exact step21_valid
  · exact step22_valid
  · exact step23_valid
  · exact step24_valid
  · exact step25_valid
  · exact step26_valid
  · exact step27_valid
  · exact step28_valid
  · exact step29_valid
  · exact step30_valid
  · exact step31_valid
theorem durations : ∀ j : Fin 32, (steps j).duration=stepLength := by decide +kernel
theorem regions : ∀ j : Fin 32, (steps j).region=4/3 := by decide +kernel
theorem errors : ∀ j : Fin 32, (steps j).error≤errorBound := by decide +kernel
theorem inverse_bounds : ∀ j : Fin 32,
    PolynomialBounds.bound ((steps j).coefficients 4) stepLength+errorBound ≤ inverseBound := by decide +kernel
theorem joins : ∀ j : Fin 31, Compatible (steps j.castSucc) (steps j.succ) := by decide +kernel
def endpoint (i : Fin 5) : ℚ := Planning.PolynomialKernel.evaluate (step31.coefficients i) stepLength
theorem endpoint_checked :
    0<endpoint 0-errorBound ∧ 0<endpoint 1-errorBound ∧
    1<radialLower ∧
    radialLower^2<(endpoint 0-errorBound)^2+(endpoint 1-errorBound)^2 ∧
    (endpoint 0+errorBound)^2+(endpoint 1+errorBound)^2<radialUpper^2 ∧
    0<radialUpper := by decide +kernel
end GNC.OrbitalComparison.TangentialReferenceData
