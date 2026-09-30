import GNC.Applications.OrbitalComparison.SharedResponseData.Step0
import GNC.Applications.OrbitalComparison.SharedResponseData.Step1
import GNC.Applications.OrbitalComparison.SharedResponseData.Step2
import GNC.Applications.OrbitalComparison.SharedResponseData.Step3
import GNC.Applications.OrbitalComparison.SharedResponseData.Step4
import GNC.Applications.OrbitalComparison.SharedResponseData.Step5
import GNC.Applications.OrbitalComparison.SharedResponseData.Step6
import GNC.Applications.OrbitalComparison.SharedResponseData.Step7
import GNC.Applications.OrbitalComparison.SharedResponseData.Step8
import GNC.Applications.OrbitalComparison.SharedResponseData.Step9
import GNC.Applications.OrbitalComparison.SharedResponseData.Step10
import GNC.Applications.OrbitalComparison.SharedResponseData.Step11
import GNC.Applications.OrbitalComparison.SharedResponseData.Step12
import GNC.Applications.OrbitalComparison.SharedResponseData.Step13
import GNC.Applications.OrbitalComparison.SharedResponseData.Step14
import GNC.Applications.OrbitalComparison.SharedResponseData.Step15
import GNC.Applications.OrbitalComparison.SharedResponseData.Step16
import GNC.Applications.OrbitalComparison.SharedResponseData.Step17
import GNC.Applications.OrbitalComparison.SharedResponseData.Step18
import GNC.Applications.OrbitalComparison.SharedResponseData.Step19
import GNC.Applications.OrbitalComparison.SharedResponseData.Step20
import GNC.Applications.OrbitalComparison.SharedResponseData.Step21
import GNC.Applications.OrbitalComparison.SharedResponseData.Step22
import GNC.Applications.OrbitalComparison.SharedResponseData.Step23
import GNC.Applications.OrbitalComparison.SharedResponseData.Step24
import GNC.Applications.OrbitalComparison.SharedResponseData.Step25
import GNC.Applications.OrbitalComparison.SharedResponseData.Step26
import GNC.Applications.OrbitalComparison.SharedResponseData.Step27
import GNC.Applications.OrbitalComparison.SharedResponseData.Step28
import GNC.Applications.OrbitalComparison.SharedResponseData.Step29
import GNC.Applications.OrbitalComparison.SharedResponseData.Step30
import GNC.Applications.OrbitalComparison.SharedResponseData.Step31

namespace GNC.OrbitalComparison.SharedResponseData
open GNC.AffinePolynomialStep
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def geometricSteps : Fin 32 → Step 8 := ![geometric0, geometric1, geometric2, geometric3, geometric4, geometric5, geometric6, geometric7, geometric8, geometric9, geometric10, geometric11, geometric12, geometric13, geometric14, geometric15, geometric16, geometric17, geometric18, geometric19, geometric20, geometric21, geometric22, geometric23, geometric24, geometric25, geometric26, geometric27, geometric28, geometric29, geometric30, geometric31]
theorem geometric_valid (j : Fin 32) : (geometricSteps j).Valid := by
  fin_cases j
  · exact geometric0_valid
  · exact geometric1_valid
  · exact geometric2_valid
  · exact geometric3_valid
  · exact geometric4_valid
  · exact geometric5_valid
  · exact geometric6_valid
  · exact geometric7_valid
  · exact geometric8_valid
  · exact geometric9_valid
  · exact geometric10_valid
  · exact geometric11_valid
  · exact geometric12_valid
  · exact geometric13_valid
  · exact geometric14_valid
  · exact geometric15_valid
  · exact geometric16_valid
  · exact geometric17_valid
  · exact geometric18_valid
  · exact geometric19_valid
  · exact geometric20_valid
  · exact geometric21_valid
  · exact geometric22_valid
  · exact geometric23_valid
  · exact geometric24_valid
  · exact geometric25_valid
  · exact geometric26_valid
  · exact geometric27_valid
  · exact geometric28_valid
  · exact geometric29_valid
  · exact geometric30_valid
  · exact geometric31_valid
theorem geometric_durations : ∀ j, (geometricSteps j).duration=TangentialReferenceData.stepLength := by decide +kernel
theorem geometric_errors : ∀ j, (geometricSteps j).error≤geometricError := by decide +kernel
theorem geometric_joins : ∀ j : Fin 31, Compatible (geometricSteps j.castSucc) (geometricSteps j.succ) := by decide +kernel
theorem geometric_initial : ∀ k, GNC.Planning.PolynomialKernel.evaluate ((geometricSteps 0).coefficients k) 0=0 := by decide +kernel
theorem geometric_operators (j : Fin 32) : (geometricSteps j).operator=geometricOperator (TangentialReferenceData.steps j).coefficients := by
  fin_cases j <;> rfl
theorem geometric_inputs (j : Fin 32) : (geometricSteps j).input=geometricInput (TangentialReferenceData.steps j).coefficients := by
  fin_cases j <;> rfl
theorem geometric_operatorErrors (j : Fin 32) : (geometricSteps j).operatorError=TangentialReference.gradientBudget := by
  fin_cases j <;> rfl
theorem geometric_inputErrors (j : Fin 32) : (geometricSteps j).inputError=TangentialReference.thrustBudget := by
  fin_cases j <;> rfl

def cartesianSteps : Fin 32 → Step 20 := ![cartesian0, cartesian1, cartesian2, cartesian3, cartesian4, cartesian5, cartesian6, cartesian7, cartesian8, cartesian9, cartesian10, cartesian11, cartesian12, cartesian13, cartesian14, cartesian15, cartesian16, cartesian17, cartesian18, cartesian19, cartesian20, cartesian21, cartesian22, cartesian23, cartesian24, cartesian25, cartesian26, cartesian27, cartesian28, cartesian29, cartesian30, cartesian31]
theorem cartesian_valid (j : Fin 32) : (cartesianSteps j).Valid := by
  fin_cases j
  · exact cartesian0_valid
  · exact cartesian1_valid
  · exact cartesian2_valid
  · exact cartesian3_valid
  · exact cartesian4_valid
  · exact cartesian5_valid
  · exact cartesian6_valid
  · exact cartesian7_valid
  · exact cartesian8_valid
  · exact cartesian9_valid
  · exact cartesian10_valid
  · exact cartesian11_valid
  · exact cartesian12_valid
  · exact cartesian13_valid
  · exact cartesian14_valid
  · exact cartesian15_valid
  · exact cartesian16_valid
  · exact cartesian17_valid
  · exact cartesian18_valid
  · exact cartesian19_valid
  · exact cartesian20_valid
  · exact cartesian21_valid
  · exact cartesian22_valid
  · exact cartesian23_valid
  · exact cartesian24_valid
  · exact cartesian25_valid
  · exact cartesian26_valid
  · exact cartesian27_valid
  · exact cartesian28_valid
  · exact cartesian29_valid
  · exact cartesian30_valid
  · exact cartesian31_valid
theorem cartesian_durations : ∀ j, (cartesianSteps j).duration=TangentialReferenceData.stepLength := by decide +kernel
theorem cartesian_errors : ∀ j, (cartesianSteps j).error≤cartesianError := by decide +kernel
theorem cartesian_joins : ∀ j : Fin 31, Compatible (cartesianSteps j.castSucc) (cartesianSteps j.succ) := by decide +kernel
theorem cartesian_initial : ∀ k, GNC.Planning.PolynomialKernel.evaluate ((cartesianSteps 0).coefficients k) 0=0 := by decide +kernel
theorem cartesian_operators (j : Fin 32) : (cartesianSteps j).operator=cartesianOperator (TangentialReferenceData.steps j).coefficients := by
  fin_cases j <;> rfl
theorem cartesian_inputs (j : Fin 32) : (cartesianSteps j).input=cartesianInput (TangentialReferenceData.steps j).coefficients := by
  fin_cases j <;> rfl
theorem cartesian_operatorErrors (j : Fin 32) : (cartesianSteps j).operatorError=TangentialReference.gradientBudget := by
  fin_cases j <;> rfl
theorem cartesian_inputErrors (j : Fin 32) : (cartesianSteps j).inputError=TangentialReference.thrustBudget := by
  fin_cases j <;> rfl

end GNC.OrbitalComparison.SharedResponseData
