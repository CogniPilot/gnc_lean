import GNC.Lie.SmoothExponential
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-! Local logarithms obtained from mathlib's inverse function theorem.
Invertibility of the derivative follows from the checked exponential
differential, rather than being an additional hypothesis. -/
noncomputable section
open Matrix NormedSpace Filter Set Function
open scoped Matrix Matrix.Norms.Operator ContDiff Manifold Topology
namespace GNC.LocalLog

def stateEquiv : SE23.Model ≃ₗ[ℝ] LogState where
  toFun x := ![x.2.2,x.2.1,x.1]
  invFun x := (x 2,x 1,x 0)
  left_inv _ := rfl
  right_inv x := by ext i j; fin_cases i <;> rfl
  map_add' _ _ := by ext i j; fin_cases i <;> rfl
  map_smul' _ _ := by ext i j; fin_cases i <;> rfl

def inChart (X : SE23) (z : LogState) : LogState :=
  stateEquiv (extChartAt 𝓘(ℝ, SE23.Model) X (groupExp z))

def decodeMatrix (X : SE23) (z : LogState) : Mat5 :=
  SE23.toMatrix ((extChartAt 𝓘(ℝ, SE23.Model) X).symm (stateEquiv.symm z))

theorem inChart_contDiffAt (x : LogState) : ContDiffAt ℝ ∞ (inChart (groupExp x)) x := by
  have hc := (contMDiffAt_iff_target.mp (groupExp_contMDiff x)).2.contDiffAt
  exact stateEquiv.toContinuousLinearEquiv.contDiff.contDiffAt.comp x hc

theorem decodeMatrix_contDiff (X : SE23) : ContDiff ℝ ∞ (decodeMatrix X) :=
  (chartMatrix_contDiff X).comp stateEquiv.symm.toContinuousLinearEquiv.contDiff

theorem decode_inChart (x : LogState) :
    (fun z => decodeMatrix (groupExp x) (inChart (groupExp x) z)) =ᶠ[𝓝 x]
      (fun z => exp (hat z)) := by
  have hs := groupExp_contMDiff.continuous.continuousAt.preimage_mem_nhds
    (extChartAt_source_mem_nhds (I := 𝓘(ℝ, SE23.Model)) (groupExp x))
  filter_upwards [hs] with z hz
  simp only [decodeMatrix, inChart, LinearEquiv.symm_apply_apply,
    (extChartAt 𝓘(ℝ, SE23.Model) (groupExp x)).left_inv hz, groupExp_toMatrix]

theorem inChart_fderiv_injective (x : LogState) (hx : enorm (x 2) < 2*Real.pi) :
    Injective (fderiv ℝ (inChart (groupExp x)) x) := by
  have hF := (inChart_contDiffAt x).differentiableAt (by simp)
  have hD := (decodeMatrix_contDiff (groupExp x)).differentiable (by simp)
  have hc := (hD (inChart (groupExp x) x)).hasFDerivAt.comp x hF.hasFDerivAt
  have he := (decode_inChart x).fderiv_eq (𝕜 := ℝ)
  have hder : fderiv ℝ (fun z : LogState => exp (hat z)) x =
      (fderiv ℝ (decodeMatrix (groupExp x)) (inChart (groupExp x) x)).comp
        (fderiv ℝ (inChart (groupExp x)) x) := he.symm.trans hc.fderiv
  intro u v huv
  apply matrixExp_fderiv_injective x hx
  rw [hder]
  exact congrArg (fderiv ℝ (decodeMatrix (groupExp x)) (inChart (groupExp x) x)) huv

def derivativeEquiv (x : LogState) (hx : enorm (x 2) < 2*Real.pi) : LogState ≃L[ℝ] LogState :=
  (LinearEquiv.ofInjectiveEndo (fderiv ℝ (inChart (groupExp x)) x).toLinearMap
    (inChart_fderiv_injective x hx)).toContinuousLinearEquiv

theorem derivativeEquiv_coe (x : LogState) (hx : enorm (x 2) < 2*Real.pi) :
    (derivativeEquiv x hx : LogState →L[ℝ] LogState) = fderiv ℝ (inChart (groupExp x)) x := by
  ext z i j; rfl

theorem inChart_hasFDerivAt (x : LogState) (hx : enorm (x 2) < 2*Real.pi) :
    HasFDerivAt (inChart (groupExp x)) (derivativeEquiv x hx : LogState →L[ℝ] LogState) x := by
  rw [derivativeEquiv_coe]
  exact ((inChart_contDiffAt x).differentiableAt (by simp)).hasFDerivAt

/-- Here the imported inverse function theorem constructs the local inverse. -/
def inverseChart (x : LogState) (hx : enorm (x 2) < 2*Real.pi) :
    OpenPartialHomeomorph LogState LogState :=
  (inChart_contDiffAt x).toOpenPartialHomeomorph (inChart (groupExp x))
    (inChart_hasFDerivAt x hx) (by simp)

theorem inverseChart_source (x : LogState) (hx : enorm (x 2) < 2*Real.pi) :
    x ∈ (inverseChart x hx).source :=
  (inChart_contDiffAt x).mem_toOpenPartialHomeomorph_source (inChart_hasFDerivAt x hx) (by simp)

theorem inverseChart_contDiffAt (x : LogState) (hx : enorm (x 2) < 2*Real.pi) :
    ContDiffAt ℝ ∞ (inverseChart x hx).symm (inChart (groupExp x) x) :=
  (inChart_contDiffAt x).to_localInverse (inChart_hasFDerivAt x hx) (by simp)

def near (x : LogState) (hx : enorm (x 2) < 2*Real.pi) (X : SE23) : LogState :=
  (inverseChart x hx).symm (stateEquiv (extChartAt 𝓘(ℝ, SE23.Model) (groupExp x) X))

theorem near_at_exp (x : LogState) (hx : enorm (x 2) < 2*Real.pi) : near x hx (groupExp x) = x :=
  (inverseChart x hx).left_inv (inverseChart_source x hx)

theorem near_contMDiffAt (x : LogState) (hx : enorm (x 2) < 2*Real.pi) :
    ContMDiffAt 𝓘(ℝ, SE23.Model) 𝓘(ℝ, LogState) ∞ (near x hx) (groupExp x) := by
  have hc : ContMDiffAt 𝓘(ℝ, SE23.Model) 𝓘(ℝ, LogState) ∞
      (fun X => stateEquiv (extChartAt 𝓘(ℝ, SE23.Model) (groupExp x) X)) (groupExp x) :=
    stateEquiv.toContinuousLinearEquiv.contDiff.contMDiff.contMDiffAt.comp _ contMDiffAt_extChartAt
  exact (inverseChart_contDiffAt x hx).contMDiffAt.comp (groupExp x) hc

theorem near_exp_eventually (x : LogState) (hx : enorm (x 2) < 2*Real.pi) :
    ∀ᶠ z in 𝓝 x, near x hx (groupExp z) = z :=
  (inverseChart x hx).eventually_left_inverse (inverseChart_source x hx)

/-- The constructed map is an actual local group logarithm. -/
theorem exp_near_eventually (x : LogState) (hx : enorm (x 2) < 2*Real.pi) :
    ∀ᶠ X in 𝓝 (groupExp x), groupExp (near x hx X) = X := by
  have hc : ContinuousAt (fun X => stateEquiv
      (extChartAt 𝓘(ℝ, SE23.Model) (groupExp x) X)) (groupExp x) :=
    stateEquiv.toContinuousLinearEquiv.continuous.continuousAt.comp (continuousAt_extChartAt _)
  have hi := hc.tendsto.eventually
    ((inverseChart x hx).eventually_right_inverse' (inverseChart_source x hx))
  have hn : Tendsto (near x hx) (𝓝 (groupExp x)) (𝓝 x) := by
    simpa only [near_at_exp] using (near_contMDiffAt x hx).continuousAt.tendsto
  have hs := extChartAt_source_mem_nhds (I := 𝓘(ℝ, SE23.Model)) (groupExp x)
  have hs' := (groupExp_contMDiff.continuous.continuousAt.tendsto.comp hn).eventually hs
  filter_upwards [hi, hs, hs'] with X hI hX hN
  apply (extChartAt 𝓘(ℝ, SE23.Model) (groupExp x)).injOn hN hX
  apply stateEquiv.injective
  exact hI

/-- Smooth local logarithms exist around every principal exponential,
including arbitrary translation and zero attitude. -/
theorem exists_smooth_local_log (x : LogState) (hx : enorm (x 2) < Real.pi) :
    ∃ L : SE23 → LogState, L (groupExp x) = x ∧
      ContMDiffAt 𝓘(ℝ, SE23.Model) 𝓘(ℝ, LogState) ∞ L (groupExp x) ∧
      (∀ᶠ X in 𝓝 (groupExp x), groupExp (L X) = X) := by
  have hx' : enorm (x 2) < 2*Real.pi := by linarith [Real.pi_pos]
  exact ⟨near x hx', near_at_exp x hx', near_contMDiffAt x hx', exp_near_eventually x hx'⟩

end GNC.LocalLog
