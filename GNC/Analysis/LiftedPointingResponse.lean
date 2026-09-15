import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.BilinearMap

/-! Cartesian force-component responses and retained-angle responses share
the same quadratic approximation class. The inputs are independent during
coefficient propagation and restricted to the pointing circle afterwards.
These are real-arithmetic identities, not compiler or FLOP-count proofs. -/
noncomputable section
namespace GNC.LiftedPointingResponse
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

def raw (s c : ℝ) (S C SS SC CC : E) : E :=
  s • S+c • C+s^2 • SS+(s*c) • SC+c^2 • CC

def reduced (s c : ℝ) (S C SC CC : E) : E :=
  s • S+c • C+(s*c) • SC+c^2 • CC

theorem reduction (s c : ℝ) (hc : s^2=2*c-c^2) (S C SS SC CC : E) :
    raw s c S C SS SC CC = reduced s c S (C+2 • SS) SC (CC-SS) := by
  unfold raw reduced
  rw [hc]
  module

theorem angular_reduction (θ : ℝ) (S C SS SC CC : E) :
    raw (Real.sin θ) (1-Real.cos θ) S C SS SC CC =
      reduced (Real.sin θ) (1-Real.cos θ) S (C+2 • SS) SC (CC-SS) := by
  apply reduction
  nlinarith [Real.sin_sq_add_cos_sq θ]

/-- Conversely, every reduced quadratic predictor is a Cartesian quadratic
predictor. Thus this change of input is outside an angle-polynomial barrier. -/
theorem reduced_is_raw (s c : ℝ) (S C SC CC : E) :
    reduced s c S C SC CC = raw s c S C 0 SC CC := by
  simp [raw,reduced]

section Dynamics
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- First and second response equations in two independent constant force
components. `H` includes the factor one half of the physical Hessian.
No circle identity, symmetry of H, constant generator, or planar state is
assumed in propagating these coefficients. All data may vary with time. -/
theorem derivative (s c t : ℝ) (S C SS SC CC : ℝ → F)
    (A : F →L[ℝ] F) (H : F →ₗ[ℝ] F →ₗ[ℝ] F) (fS fC : F)
    (hS : HasDerivAt S (A (S t)+fS) t)
    (hC : HasDerivAt C (A (C t)+fC) t)
    (hSS : HasDerivAt SS (A (SS t)+H (S t) (S t)) t)
    (hSC : HasDerivAt SC (A (SC t)+H (S t) (C t)+H (C t) (S t)) t)
    (hCC : HasDerivAt CC (A (CC t)+H (C t) (C t)) t) :
    HasDerivAt (fun u => raw s c (S u) (C u) (SS u) (SC u) (CC u))
      (A (raw s c (S t) (C t) (SS t) (SC t) (CC t))+s • fS+c • fC+
        H (s • S t+c • C t) (s • S t+c • C t)) t := by
  have hd := ((((hS.const_smul s).add (hC.const_smul c)).add
    (hSS.const_smul (s^2))).add (hSC.const_smul (s*c))).add (hCC.const_smul (c^2))
  convert hd using 1
  simp only [raw,map_add,map_smul,LinearMap.add_apply,LinearMap.smul_apply]
  module

theorem initial (s c : ℝ) (S C SS SC CC : ℝ → F)
    (hS : S 0=0) (hC : C 0=0) (hSS : SS 0=0) (hSC : SC 0=0) (hCC : CC 0=0) :
    raw s c (S 0) (C 0) (SS 0) (SC 0) (CC 0)=0 := by
  simp [raw,hS,hC,hSS,hSC,hCC]

end Dynamics
end GNC.LiftedPointingResponse
