import GNC.Lie.SE23Manifold
import GNC.Lie.ZeroAttitude

/-! Smoothness and injectivity of the differential of the actual matrix
exponential as a map into the constructed SE₂(3) manifold. -/
noncomputable section
open Matrix NormedSpace
open scoped Matrix Matrix.Norms.Operator ContDiff Manifold
namespace GNC

def rotationBlock : Mat5 →ₗ[ℝ] Cayley.Mat3 where
  toFun A i j := A i.castSucc.castSucc j.castSucc.castSucc
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def velocityBlock : Mat5 →ₗ[ℝ] Vec3 where
  toFun A i := A i.castSucc.castSucc 3
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def positionBlock : Mat5 →ₗ[ℝ] Vec3 where
  toFun A i := A i.castSucc.castSucc 4
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem rotationBlock_toMatrix (X : SE23) : rotationBlock (SE23.toMatrix X) = X.rot.val := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

@[simp] theorem velocityBlock_toMatrix (X : SE23) : velocityBlock (SE23.toMatrix X) = X.vel := by
  ext i; fin_cases i <;> rfl

@[simp] theorem positionBlock_toMatrix (X : SE23) : positionBlock (SE23.toMatrix X) = X.pos := by
  ext i; fin_cases i <;> rfl

theorem matrixExp_contDiff : ContDiff ℝ ∞ (fun x : LogState => exp (hat x)) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  have h := (NormedSpace.analyticAt_exp_of_mem_ball (𝕂 := ℝ) (hat x)
    (by simp [NormedSpace.expSeries_radius_eq_top])).contDiffAt (n := ∞)
  exact h.comp x hatLinear.toContinuousLinearMap.contDiff.contDiffAt

theorem groupExp_contMDiff : ContMDiff 𝓘(ℝ, LogState) 𝓘(ℝ, SE23.Model) ∞ groupExp := by
  apply SE23.contMDiff_mk
  · apply Cayley.contMDiff_into_so3
    have h := (rotationBlock.toContinuousLinearMap.contDiff.comp matrixExp_contDiff).contMDiff
    convert h using 1
    funext x
    change (groupExp x).rot.val = rotationBlock (exp (hat x))
    rw [← groupExp_toMatrix]
    exact (rotationBlock_toMatrix _).symm
  · have h := (velocityBlock.toContinuousLinearMap.contDiff.comp matrixExp_contDiff).contMDiff
    convert h using 1
    funext x
    change (groupExp x).vel = velocityBlock (exp (hat x))
    rw [← groupExp_toMatrix]
    exact (velocityBlock_toMatrix _).symm
  · have h := (positionBlock.toContinuousLinearMap.contDiff.comp matrixExp_contDiff).contMDiff
    convert h using 1
    funext x
    change (groupExp x).pos = positionBlock (exp (hat x))
    rw [← groupExp_toMatrix]
    exact (positionBlock_toMatrix _).symm

def matrixAssembly : (Cayley.Mat3 × Vec3 × Vec3) →ₗ[ℝ] Mat5 where
  toFun x :=
    !![x.1 0 0,x.1 0 1,x.1 0 2,x.2.1 0,x.2.2 0;
       x.1 1 0,x.1 1 1,x.1 1 2,x.2.1 1,x.2.2 1;
       x.1 2 0,x.1 2 1,x.1 2 2,x.2.1 2,x.2.2 2;
       0,0,0,0,0; 0,0,0,0,0]
  map_add' x y := by ext i j; fin_cases i <;> fin_cases j <;> simp
  map_smul' c x := by ext i j; fin_cases i <;> fin_cases j <;> simp

def affineBottom : Mat5 := diagonal ![0,0,0,1,1]

theorem matrixAssembly_toMatrix (X : SE23) :
    matrixAssembly (X.rot.val,X.vel,X.pos)+affineBottom = SE23.toMatrix X := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [matrixAssembly, affineBottom, SE23.toMatrix]

theorem chartMatrix_contDiff (X : SE23) :
    ContDiff ℝ ∞ (fun z : SE23.Model => SE23.toMatrix ((extChartAt 𝓘(ℝ, SE23.Model) X).symm z)) := by
  have hc : ContDiff ℝ ∞ (fun z : SE23.Model => X.rot.val*Cayley.matrix z.1) :=
    contDiff_const.mul (Cayley.contDiff_matrix.comp contDiff_fst)
  have h := (matrixAssembly.toContinuousLinearMap.contDiff.comp (hc.prodMk contDiff_snd)).add
    (contDiff_const (c := affineBottom))
  convert h using 1
  funext z
  rw [SE23.extChartAt_symm_apply, ← matrixAssembly_toMatrix]
  rfl

theorem matrixExp_fderiv_injective (x : LogState) (hx : enorm (x 2) < 2*Real.pi) :
    Function.Injective (fderiv ℝ (fun z : LogState => exp (hat z)) x) := by
  intro y z h
  rw [matrixExp_fderiv_all, matrixExp_fderiv_all] at h
  have hc := congrArg (fun A : Mat5 => A*exp (-hat x)) h
  simp only [Matrix.mul_assoc, MixedInvariant.exp_cancel, Matrix.mul_one] at hc
  have hh := congrArg (Jacobian.blockInverse x) (hat_injective hc)
  simpa only [Jacobian.blockInverse_left_all _ _ hx] using hh

end GNC
