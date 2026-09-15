import GNC.Applications.MotorBurn.Data.RTNCircle2Time6Step02Adjoint1
import GNC.Applications.MotorBurn.AdjointInput

/-! Exact support bounds for the stored computed adjoint. The spherical-cap
enclosure and arbitrary-history pairing theorem are proved in AdjointInput. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace GNC.MotorBurn.Data.RTNCircle2Time6Step02AdjointSupport1
open ParametricBox
def transverseLimit : ℚ := (58899953481/200000000000)
def boxInput : ℚ := (11528628580894157807823054621/10220503669197501064234330488832)
def cylinderInput : ℚ := (3580612812717077152835003109066267/7920890343628063324781606128844800000)
theorem checked :
    0 ≤ transverseLimit ∧
    circle.bound (transversePolynomial circle RTNCircle2Time6Step02Adjoint1.ell) (1/20) 0 ≤ transverseLimit^2 ∧
    (if Data.RTNCircle2Time6Step02.on = 0 then 0 else cylinderSupport circle RTNCircle2Time6Step02Adjoint1.ell (1/20) 0 transverseLimit) ≤ cylinderInput ∧
    (∑ i, circle.bound (RTNCircle2Time6Step02Adjoint1.ell i) (1/20) 0*Data.RTNCircle2Time6Step02.inputBound i) ≤ boxInput := by
  decide +kernel
end GNC.MotorBurn.Data.RTNCircle2Time6Step02AdjointSupport1
