import GNC.Applications.MotorBurn.Data.RTNCircle2Time6Step04Adjoint1
import GNC.Applications.MotorBurn.AdjointInput

/-! Exact support bounds for the stored computed adjoint. The spherical-cap
enclosure and arbitrary-history pairing theorem are proved in AdjointInput. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace GNC.MotorBurn.Data.RTNCircle2Time6Step04AdjointSupport1
open ParametricBox
def transverseLimit : ℚ := (198804113529/1000000000000)
def boxInput : ℚ := 0
def cylinderInput : ℚ := 0
theorem checked :
    0 ≤ transverseLimit ∧
    circle.bound (transversePolynomial circle RTNCircle2Time6Step04Adjoint1.ell) (1/20) 0 ≤ transverseLimit^2 ∧
    (if Data.RTNCircle2Time6Step04.on = 0 then 0 else cylinderSupport circle RTNCircle2Time6Step04Adjoint1.ell (1/20) 0 transverseLimit) ≤ cylinderInput ∧
    (∑ i, circle.bound (RTNCircle2Time6Step04Adjoint1.ell i) (1/20) 0*Data.RTNCircle2Time6Step04.inputBound i) ≤ boxInput := by
  decide +kernel
end GNC.MotorBurn.Data.RTNCircle2Time6Step04AdjointSupport1
