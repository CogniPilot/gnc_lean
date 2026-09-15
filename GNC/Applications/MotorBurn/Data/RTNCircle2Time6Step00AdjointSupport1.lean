import GNC.Applications.MotorBurn.Data.RTNCircle2Time6Step00Adjoint1
import GNC.Applications.MotorBurn.AdjointInput

/-! Exact support bounds for the stored computed adjoint. The spherical-cap
enclosure and arbitrary-history pairing theorem are proved in AdjointInput. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace GNC.MotorBurn.Data.RTNCircle2Time6Step00AdjointSupport1
open ParametricBox
def transverseLimit : ℚ := (101808263089/250000000000)
def boxInput : ℚ := (426742096195866234768495985761/316835613745122532991264245153792)
def cylinderInput : ℚ := (24714127291693301328914191815814017/39604451718140316623908030644224000000)
theorem checked :
    0 ≤ transverseLimit ∧
    circle.bound (transversePolynomial circle RTNCircle2Time6Step00Adjoint1.ell) (1/20) 0 ≤ transverseLimit^2 ∧
    (if Data.RTNCircle2Time6Step00.on = 0 then 0 else cylinderSupport circle RTNCircle2Time6Step00Adjoint1.ell (1/20) 0 transverseLimit) ≤ cylinderInput ∧
    (∑ i, circle.bound (RTNCircle2Time6Step00Adjoint1.ell i) (1/20) 0*Data.RTNCircle2Time6Step00.inputBound i) ≤ boxInput := by
  decide +kernel
end GNC.MotorBurn.Data.RTNCircle2Time6Step00AdjointSupport1
