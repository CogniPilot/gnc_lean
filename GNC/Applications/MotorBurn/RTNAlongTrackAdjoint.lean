import GNC.Applications.MotorBurn.Data.RTNCircle2Time6Step00Adjoint1
import GNC.Applications.MotorBurn.Data.RTNCircle2Time6Step01Adjoint1
import GNC.Applications.MotorBurn.Data.RTNCircle2Time6Step02Adjoint1
import GNC.Applications.MotorBurn.Data.RTNCircle2Time6Step03Adjoint1
import GNC.Applications.MotorBurn.Data.RTNCircle2Time6Step04Adjoint1
import GNC.Applications.MotorBurn.Data.RTNCircle2Time6Step05Adjoint1
import GNC.Applications.MotorBurn.Data.RTNCircle2Time6Step06Adjoint1
import GNC.Applications.MotorBurn.Data.RTNCircle2Time6Step07Adjoint1
import GNC.Applications.MotorBurn.Data.RTNCircle2Time6Step08Adjoint1
import GNC.Applications.MotorBurn.Data.RTNCircle2Time6Step09Adjoint1
import GNC.Applications.MotorBurn.Data.RTNCircle2Time6Step10Adjoint1
import GNC.Applications.MotorBurn.Data.RTNCircle2Time6Step11Adjoint1
import GNC.Applications.MotorBurn.RTNCircle2Time6

/-! Checked differential-defect charges for a computed terminal along-track
adjoint on the synthetic motor benchmark. This collection is restricted to
zero common pointing bias. It does not assert the input support, exact row
handoffs, terminal matching, or a complete directional arrival certificate.
-/
namespace GNC.MotorBurn.RTNAlongTrackAdjoint
open ParametricBox

def ell : ℕ → Fin 13 → CirclePolynomial.Coefficients
  | 0 => Data.RTNCircle2Time6Step00Adjoint1.ell
  | 1 => Data.RTNCircle2Time6Step01Adjoint1.ell
  | 2 => Data.RTNCircle2Time6Step02Adjoint1.ell
  | 3 => Data.RTNCircle2Time6Step03Adjoint1.ell
  | 4 => Data.RTNCircle2Time6Step04Adjoint1.ell
  | 5 => Data.RTNCircle2Time6Step05Adjoint1.ell
  | 6 => Data.RTNCircle2Time6Step06Adjoint1.ell
  | 7 => Data.RTNCircle2Time6Step07Adjoint1.ell
  | 8 => Data.RTNCircle2Time6Step08Adjoint1.ell
  | 9 => Data.RTNCircle2Time6Step09Adjoint1.ell
  | 10 => Data.RTNCircle2Time6Step10Adjoint1.ell
  | _ => Data.RTNCircle2Time6Step11Adjoint1.ell

def charge : ℕ → ℚ
  | 0 => Data.RTNCircle2Time6Step00Adjoint1.charge
  | 1 => Data.RTNCircle2Time6Step01Adjoint1.charge
  | 2 => Data.RTNCircle2Time6Step02Adjoint1.charge
  | 3 => Data.RTNCircle2Time6Step03Adjoint1.charge
  | 4 => Data.RTNCircle2Time6Step04Adjoint1.charge
  | 5 => Data.RTNCircle2Time6Step05Adjoint1.charge
  | 6 => Data.RTNCircle2Time6Step06Adjoint1.charge
  | 7 => Data.RTNCircle2Time6Step07Adjoint1.charge
  | 8 => Data.RTNCircle2Time6Step08Adjoint1.charge
  | 9 => Data.RTNCircle2Time6Step09Adjoint1.charge
  | 10 => Data.RTNCircle2Time6Step10Adjoint1.charge
  | _ => Data.RTNCircle2Time6Step11Adjoint1.charge

theorem charges_checked (j : ℕ) (hj : j < 12) :
    adjointCharge circle (field .rtn (RTNCircle2Time6.command j) (RTNCircle2Time6.on j))
      (RTNCircle2Time6.steps j).coefficients (ell j)
      (RTNCircle2Time6.steps j).region (RTNCircle2Time6.steps j).error (1/20) 0 ≤ charge j := by
  interval_cases j
  · exact Data.RTNCircle2Time6Step00Adjoint1.charge_checked
  · exact Data.RTNCircle2Time6Step01Adjoint1.charge_checked
  · exact Data.RTNCircle2Time6Step02Adjoint1.charge_checked
  · exact Data.RTNCircle2Time6Step03Adjoint1.charge_checked
  · exact Data.RTNCircle2Time6Step04Adjoint1.charge_checked
  · exact Data.RTNCircle2Time6Step05Adjoint1.charge_checked
  · exact Data.RTNCircle2Time6Step06Adjoint1.charge_checked
  · exact Data.RTNCircle2Time6Step07Adjoint1.charge_checked
  · exact Data.RTNCircle2Time6Step08Adjoint1.charge_checked
  · exact Data.RTNCircle2Time6Step09Adjoint1.charge_checked
  · exact Data.RTNCircle2Time6Step10Adjoint1.charge_checked
  · exact Data.RTNCircle2Time6Step11Adjoint1.charge_checked

end GNC.MotorBurn.RTNAlongTrackAdjoint
