import GNC.Dynamics.MixedLogLinear
import GNC.Magnus.GravityFactor

/-! Exact transformations for state-dependent mixed matrix dynamics.

The constant right generator can be removed without freezing the left
coefficient. Both invariant error equations expose the remaining mismatch.
The gravity-side specialization retains an exact two-moment factor relation.
These transformations do not supply the unknown gravity history or solve the
nonlinear IVP by a prescribed matrix exponential.
-/
noncomputable section
set_option autoImplicit false
namespace GNC.StateDependentMixed
open NormedSpace
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

/-- Strip the known constant right factor; the left coefficient is still
sampled on the actual state. This is an ambient change of variables, and its
intermediate value need not belong to the physical state subgroup. -/
theorem remove_right_factor (M : A → A) (N : A) {X : ℝ → A} {t : ℝ}
    (hX : HasDerivAt X (M (X t)*X t+X t*N) t) :
    HasDerivAt (fun s => X s*exp (-(s • N)))
      (M (X t)*(X t*exp (-(t • N)))) t := by
  have hU := hasDerivAt_exp_smul_const' (-N) t
  simp only [smul_neg] at hU
  convert hX.mul hU using 1
  noncomm_ring

/-- Recover the physical state after stripping the known factor. -/
theorem reconstruction (X N : A) (t : ℝ) :
    (X*exp (-(t • N)))*exp (t • N) = X := by
  rw [mul_assoc, MixedInvariant.exp_cancel', mul_one]

/-- The actual transformed equation is nonautonomous: its coefficient must
be evaluated at Y(t) exp(tN), not at Y(t). -/
theorem transformed_equation (M : A → A) (N : A) {X : ℝ → A} {t : ℝ}
    (hX : HasDerivAt X (M (X t)*X t+X t*N) t) :
    HasDerivAt (fun s => X s*exp (-(s • N)))
      (M ((X t*exp (-(t • N)))*exp (t • N))*(X t*exp (-(t • N)))) t := by
  rw [reconstruction]
  exact remove_right_factor M N hX

/-- Shared body input cancels from the right-invariant error, even when the
left field depends on the state. The two different left coefficients remain. -/
theorem right_error_derivative (M : A → A) (N : A) (X H : ℝ → Aˣ) {t : ℝ}
    (hX : HasDerivAt (fun s => (X s).val)
      (M (X t).val*(X t).val+(X t).val*N) t)
    (hH : HasDerivAt (fun s => (H s).val)
      (M (H t).val*(H t).val+(H t).val*N) t) :
    HasDerivAt (fun s => (X s*(H s)⁻¹).val)
      (M (X t).val*(X t*(H t)⁻¹).val-(X t*(H t)⁻¹).val*M (H t).val) t := by
  have hi := (hasFDerivAt_ringInverse (𝕜 := ℝ) (H t)).comp_hasDerivAt t hH
  simp only [Function.comp_def, Ring.inverse_unit, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.mulLeftRight_apply] at hi
  convert hX.mul hi using 1
  simp only [Units.val_mul, mul_add, add_mul, mul_neg, neg_mul, mul_assoc,
    Units.mul_inv, mul_one]
  simp only [← mul_assoc, Units.inv_mul, Units.mul_inv, mul_one, one_mul]
  noncomm_ring

/-- The left-invariant error retains the exactly linear commutator part plus
one state-dependent coefficient mismatch. Equivalently the last term is
H⁻¹ (M(X)-M(H)) H E, where E=H⁻¹X. -/
theorem left_error_derivative (M : A → A) (N : A) (X H : ℝ → Aˣ) {t : ℝ}
    (hX : HasDerivAt (fun s => (X s).val)
      (M (X t).val*(X t).val+(X t).val*N) t)
    (hH : HasDerivAt (fun s => (H s).val)
      (M (H t).val*(H t).val+(H t).val*N) t) :
    HasDerivAt (fun s => ((H s)⁻¹*X s).val)
      (((H t)⁻¹*X t).val*N-N*((H t)⁻¹*X t).val+
        ((H t)⁻¹).val*(M (X t).val-M (H t).val)*(X t).val) t := by
  have hi := (hasFDerivAt_ringInverse (𝕜 := ℝ) (H t)).comp_hasDerivAt t hH
  simp only [Function.comp_def, Ring.inverse_unit, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.mulLeftRight_apply] at hi
  convert hi.mul hX using 1
  simp only [Units.val_mul, mul_add, add_mul, mul_neg, neg_mul, mul_assoc,
    Units.mul_inv, mul_one]
  simp only [← mul_assoc, Units.inv_mul, one_mul]
  noncomm_ring

end GNC.StateDependentMixed

namespace GNC.GravityFactor
open Matrix
/-- The mismatch between two gravity factors is exactly a pure translation
factor depending on their two moment differences. No small-angle, small-time,
constant-gravity or state-independence approximation is made here. -/
theorem factor_comparison (g h : ℝ → Vec3) (t : ℝ) :
    factor g t = factor h t *
      (1+Magnus.ideal (first h t-first g t) (zeroth g t-zeroth h t) 0) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [factor, Magnus.ideal, Magnus.extended, hat, kinematicC,
      Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply] <;> norm_num <;> ring
end GNC.GravityFactor
