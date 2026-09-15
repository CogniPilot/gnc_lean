import GNC.Lie.PrincipalLog
import GNC.Dynamics.MixedErrorDynamics
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-! Principal log dynamics with existence and differentiability of the log
lift proved from the physical trajectory, rather than assumed. -/
noncomputable section
open Matrix Real
open scoped Matrix Matrix.Norms.Operator ContDiff Manifold
namespace GNC

theorem matrix_curve_mdifferentiableAt {f : ℝ → SE23} {t : ℝ}
    (hf : DifferentiableAt ℝ (fun s => SE23.toMatrix (f s)) t) :
    MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, SE23.Model) f t := by
  have hr : DifferentiableAt ℝ (fun s => (f s).rot.val) t := by
    simpa only [Function.comp_def, LinearMap.coe_toContinuousLinearMap', rotationBlock_toMatrix] using
      rotationBlock.toContinuousLinearMap.differentiableAt.comp t hf
  have hv : DifferentiableAt ℝ (fun s => (f s).vel) t := by
    simpa only [Function.comp_def, LinearMap.coe_toContinuousLinearMap', velocityBlock_toMatrix] using
      velocityBlock.toContinuousLinearMap.differentiableAt.comp t hf
  have hp : DifferentiableAt ℝ (fun s => (f s).pos) t := by
    simpa only [Function.comp_def, LinearMap.coe_toContinuousLinearMap', positionBlock_toMatrix] using
      positionBlock.toContinuousLinearMap.differentiableAt.comp t hf
  rw [mdifferentiableAt_iff_target]
  refine ⟨?_, ?_⟩
  · have hrc : ContinuousAt (fun s => (f s).rot) t := by
      exact hr.continuousAt.codRestrict (fun s => (f s).rot.property)
    exact SE23.productHomeomorph.symm.continuous.continuousAt.comp
      (hrc.prodMk (hv.continuousAt.prodMk hp.continuousAt))
  · have hunit : IsUnit (((f t).rot⁻¹).val*(f t).rot.val+1).det := by
      change (f t).rot⁻¹*(f t).rot ∈ Cayley.domain
      simpa using Cayley.one_mem_domain
    have hmul : ContDiff ℝ ∞ (fun A : Cayley.Mat3 => ((f t).rot⁻¹).val*A) :=
      contDiff_const.mul contDiff_id
    have ha := (hmul.contDiffAt.differentiableAt (by simp)).comp t hr
    have hc := ((Cayley.contDiff_unskew.contDiffAt.comp _
      (Cayley.contDiffAt_ratio _ hunit)).differentiableAt (by simp)).comp t ha
    exact (hc.prodMk (hv.prodMk hp)).mdifferentiableAt

theorem principal_log_differentiableAt {f : ℝ → SE23} {t : ℝ}
    (hf : DifferentiableAt ℝ (fun s => SE23.toMatrix (f s)) t)
    (ht : f t ∈ PrincipalLog.domain) :
    DifferentiableAt ℝ (fun s => PrincipalLog.log (f s)) t :=
  (((PrincipalLog.log_contMDiffAt ht).mdifferentiableAt (by simp)).comp t
    (matrix_curve_mdifferentiableAt hf)).differentiableAt

/-- The principal coordinate trajectory is defined from the physical error. -/
def principalError (X Y : ℝ → SE23) (t : ℝ) : LogState :=
  PrincipalLog.log (SE23.error (Y t) (X t))

theorem principalError_hasDerivAt {X Y : ℝ → SE23} {a w abar wbar g gbar : Vec3} {t : ℝ}
    (hX : SpacecraftODEAt X a w g t) (hY : SpacecraftODEAt Y abar wbar gbar t)
    (hd : SE23.error (Y t) (X t) ∈ PrincipalLog.domain) :
    HasDerivAt (principalError X Y) (deriv (principalError X Y) t) t := by
  have hx := ((spacecraft_ode_iff X a w g t).mp hX).differentiableAt
  have hy := ((spacecraft_ode_iff Y abar wbar gbar t).mp hY).differentiableAt
  have hx' := matrix_curve_mdifferentiableAt hx
  have hy' := matrix_curve_mdifferentiableAt hy
  have hi := (contMDiff_inv 𝓘(ℝ, SE23.Model) ∞ (G := SE23)).mdifferentiable (by simp)
  have hm := (contMDiff_mul (I := 𝓘(ℝ, SE23.Model)) (n := ∞) (G := SE23)).mdifferentiable (by simp)
  have he := (hm ((Y t)⁻¹,X t)).comp t ((hi (Y t)).comp t hy' |>.prodMk hx')
  exact ((((PrincipalLog.log_contMDiffAt hd).mdifferentiableAt (by simp)).comp t he).differentiableAt).hasDerivAt

/-- Proposition 1 with no assumed differentiable log lift. The domain
hypothesis specifies where the principal logarithm is valid. -/
theorem principal_proposition1 {X Y : ℝ → SE23} {a w abar wbar g gbar : Vec3} {t : ℝ}
    (hX : SpacecraftODEAt X a w g t) (hY : SpacecraftODEAt Y abar wbar gbar t)
    (hd : ∀ s, SE23.error (Y s) (X s) ∈ PrincipalLog.domain) :
    deriv (principalError X Y) t = logDrift (Jacobian.controlInput a w) (principalError X Y t) +
      Jacobian.blockInverse (principalError X Y t) (Jacobian.controlInput (a-abar) (w-wbar)) +
      Jacobian.blockRightInverse (principalError X Y t) (adjoint (X t)⁻¹ (velocityOnly (g-gbar))) := by
  exact proposition1 hX hY (principalError_hasDerivAt hX hY (hd t))
    (fun s => (PrincipalLog.log_spec (hd s)).2.symm) (PrincipalLog.log_spec (hd t)).1

/-- Proposition 2 using the constructed principal logarithm of the physical
error. No separate regularity hypothesis on log coordinates is needed. -/
theorem principal_proposition2 {X Y : ℝ → SE23} {a w abar wbar : Vec3} {μ t : ℝ}
    (hX : SpacecraftODEAt X a w (Gravity.field3 μ (X t).pos) t)
    (hY : SpacecraftODEAt Y abar wbar (Gravity.field3 μ (Y t).pos) t)
    (hd : ∀ s, SE23.error (Y s) (X s) ∈ PrincipalLog.domain)
    (hq : 0 < enorm (Y t).pos) (hθ : 0 < enorm (principalError X Y t 2)) :
    deriv (principalError X Y) t =
      forcedLinear μ (Y t).rot (Y t).pos a w abar wbar (principalError X Y t) +
      Jacobian.controlInput (a-abar) (w-wbar) +
      Jacobian.controlResidual (principalError X Y t) (a-abar) (w-wbar) +
      velocityOnly (Gravity.attitudeResidual (μ/enorm (Y t).pos^3)
        (Jacobian.unitAxis (rotate (Y t).rot⁻¹ (Y t).pos))
        (Jacobian.unitAxis (principalError X Y t 2)) (enorm (principalError X Y t 2))
        (principalError X Y t 0)) +
      velocityOnly (Gravity.higherGravity μ (Y t).rot (Y t).pos
        (Jacobian.unitAxis (principalError X Y t 2)) (enorm (principalError X Y t 2))
        (principalError X Y t 0)) := by
  exact proposition2 hX hY (principalError_hasDerivAt hX hY (hd t))
    (fun s => (PrincipalLog.log_spec (hd s)).2.symm) hq hθ (PrincipalLog.log_spec (hd t)).1

end GNC
