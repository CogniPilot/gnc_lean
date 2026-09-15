import GNC.Applications.MotorBurn.Data.RTNCircle2Time6Step03Adjoint1
import GNC.Applications.MotorBurn.AdjointInput

/-! Exact support bounds for the stored computed adjoint. The spherical-cap
enclosure and arbitrary-history pairing theorem are proved in AdjointInput. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace GNC.MotorBurn.Data.RTNCircle2Time6Step03AdjointSupport1
open ParametricBox
def transverseLimit : ℚ := (244458996769/1000000000000)
def boxInput : ℚ := (14630682733144891236870552093/14401618806596478772330192961536)
def cylinderInput : ℚ := (14876771650901173440042446082892983/39604451718140316623908030644224000000)
theorem checked :
    0 ≤ transverseLimit ∧
    circle.bound (transversePolynomial circle RTNCircle2Time6Step03Adjoint1.ell) (1/20) 0 ≤ transverseLimit^2 ∧
    (if Data.RTNCircle2Time6Step03.on = 0 then 0 else cylinderSupport circle RTNCircle2Time6Step03Adjoint1.ell (1/20) 0 transverseLimit) ≤ cylinderInput ∧
    (∑ i, circle.bound (RTNCircle2Time6Step03Adjoint1.ell i) (1/20) 0*Data.RTNCircle2Time6Step03.inputBound i) ≤ boxInput := by
  decide +kernel
end GNC.MotorBurn.Data.RTNCircle2Time6Step03AdjointSupport1
