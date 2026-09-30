import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! Scalar second-order FOH rotation equation to the two-component spinor ODE.
This proves the reduction from an actual scalar solution. It does not assert
that a particular numerical special-function implementation solves that ODE. -/
noncomputable section
namespace GNC.Magnus

def fohSpinorSecond (y yp : ℂ → ℂ) (δ β κ : ℂ) (t : ℂ) : ℂ :=
  (2*Complex.I*yp t-(δ+β*t)*y t)/κ

set_option maxHeartbeats 1000000 in
theorem foh_scalar_to_spinor
    (y yp : ℂ → ℂ) (δ β κ t : ℂ) (hk : κ ≠ 0)
    (hy : HasDerivAt y (yp t) t)
    (hyp : HasDerivAt yp
      (-(((δ+β*t)^2+κ^2)/4+Complex.I*β/2)*y t) t) :
    HasDerivAt y
      (-Complex.I/2*((δ+β*t)*y t+κ*fohSpinorSecond y yp δ β κ t)) t ∧
    HasDerivAt (fohSpinorSecond y yp δ β κ)
      (-Complex.I/2*(κ*y t-(δ+β*t)*fohSpinorSecond y yp δ β κ t)) t := by
  constructor
  · convert hy using 1
    dsimp [fohSpinorSecond]
    field_simp [hk]
    ring_nf
    simp [Complex.I_sq] <;> ring
  · have hd : HasDerivAt (fun u : ℂ => δ+β*u) β t := by
      simpa using ((hasDerivAt_id t).const_mul β).const_add δ
    have h := (((hyp.const_mul (2*Complex.I)).sub (hd.mul hy)).div_const κ)
    convert h using 1
    dsimp [fohSpinorSecond]
    field_simp [hk]
    ring_nf
    simp [Complex.I_sq] <;> ring

end GNC.Magnus
