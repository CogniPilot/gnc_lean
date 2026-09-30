import GNC.Applications.OrbitalComparison.TangentialResponseData.Step0
import GNC.Applications.OrbitalComparison.TangentialResponseData.Step1
import GNC.Applications.OrbitalComparison.TangentialResponseData.Step2
import GNC.Applications.OrbitalComparison.TangentialResponseData.Step3
import GNC.Applications.OrbitalComparison.TangentialResponseData.Step4
import GNC.Applications.OrbitalComparison.TangentialResponseData.Step5
import GNC.Applications.OrbitalComparison.TangentialResponseData.Step6
import GNC.Applications.OrbitalComparison.TangentialResponseData.Step7
import GNC.Applications.OrbitalComparison.TangentialResponseData.Step8
import GNC.Applications.OrbitalComparison.TangentialResponseData.Step9
import GNC.Applications.OrbitalComparison.TangentialResponseData.Step10
import GNC.Applications.OrbitalComparison.TangentialResponseData.Step11
import GNC.Applications.OrbitalComparison.TangentialResponseData.Step12
import GNC.Applications.OrbitalComparison.TangentialResponseData.Step13
import GNC.Applications.OrbitalComparison.TangentialResponseData.Step14
import GNC.Applications.OrbitalComparison.TangentialResponseData.Step15
import GNC.Applications.OrbitalComparison.TangentialResponseData.Step16
import GNC.Applications.OrbitalComparison.TangentialResponseData.Step17
import GNC.Applications.OrbitalComparison.TangentialResponseData.Step18
import GNC.Applications.OrbitalComparison.TangentialResponseData.Step19
import GNC.Applications.OrbitalComparison.TangentialResponseData.Step20
import GNC.Applications.OrbitalComparison.TangentialResponseData.Step21
import GNC.Applications.OrbitalComparison.TangentialResponseData.Step22
import GNC.Applications.OrbitalComparison.TangentialResponseData.Step23
import GNC.Applications.OrbitalComparison.TangentialResponseData.Step24
import GNC.Applications.OrbitalComparison.TangentialResponseData.Step25
import GNC.Applications.OrbitalComparison.TangentialResponseData.Step26
import GNC.Applications.OrbitalComparison.TangentialResponseData.Step27
import GNC.Applications.OrbitalComparison.TangentialResponseData.Step28
import GNC.Applications.OrbitalComparison.TangentialResponseData.Step29
import GNC.Applications.OrbitalComparison.TangentialResponseData.Step30
import GNC.Applications.OrbitalComparison.TangentialResponseData.Step31

namespace GNC.OrbitalComparison.TangentialResponseData
open GNC.AffinePolynomialStep
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def steps : Fin 32 → Fin 3 → Step 6 := ![step0, step1, step2, step3, step4, step5, step6, step7, step8, step9, step10, step11, step12, step13, step14, step15, step16, step17, step18, step19, step20, step21, step22, step23, step24, step25, step26, step27, step28, step29, step30, step31]
theorem valid (j : Fin 32) (i : Fin 3) : (steps j i).Valid := by
  fin_cases j
  · exact step0_valid i
  · exact step1_valid i
  · exact step2_valid i
  · exact step3_valid i
  · exact step4_valid i
  · exact step5_valid i
  · exact step6_valid i
  · exact step7_valid i
  · exact step8_valid i
  · exact step9_valid i
  · exact step10_valid i
  · exact step11_valid i
  · exact step12_valid i
  · exact step13_valid i
  · exact step14_valid i
  · exact step15_valid i
  · exact step16_valid i
  · exact step17_valid i
  · exact step18_valid i
  · exact step19_valid i
  · exact step20_valid i
  · exact step21_valid i
  · exact step22_valid i
  · exact step23_valid i
  · exact step24_valid i
  · exact step25_valid i
  · exact step26_valid i
  · exact step27_valid i
  · exact step28_valid i
  · exact step29_valid i
  · exact step30_valid i
  · exact step31_valid i
theorem durations : ∀ j : Fin 32, ∀ i : Fin 3,
    (steps j i).duration=TangentialReferenceData.stepLength := by decide +kernel
theorem errors : ∀ j : Fin 32, ∀ i : Fin 3,
    (steps j i).error≤errorBound := by decide +kernel
theorem joins : ∀ j : Fin 31, ∀ i : Fin 3,
    Compatible (steps j.castSucc i) (steps j.succ i) := by decide +kernel
theorem operators (j : Fin 32) (i : Fin 3) :
    (steps j i).operator=operator (TangentialReferenceData.steps j).coefficients := by
  fin_cases j <;> fin_cases i <;> rfl
theorem inputs (j : Fin 32) (i : Fin 3) :
    (steps j i).input=input (TangentialReferenceData.steps j).coefficients i := by
  fin_cases j <;> fin_cases i <;> rfl
theorem operatorErrors (j : Fin 32) (i : Fin 3) :
    (steps j i).operatorError=TangentialReference.gradientBudget := by
  fin_cases j <;> fin_cases i <;> rfl
theorem inputErrors (j : Fin 32) (i : Fin 3) :
    (steps j i).inputError=TangentialReference.thrustBudget := by
  fin_cases j <;> fin_cases i <;> rfl
theorem initial_values : ∀ i : Fin 3, ∀ k : Fin 6,
    GNC.Planning.PolynomialKernel.evaluate ((steps 0 i).coefficients k) 0=0 := by decide +kernel
end GNC.OrbitalComparison.TangentialResponseData
