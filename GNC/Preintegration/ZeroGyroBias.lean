import GNC.Preintegration.SampleSensitivity
import GNC.Preintegration.SampleCovariance
import GNC.Lie.Euclidean

/-! Exact constant-bias first variation at zero nominal gyro and constant
body acceleration. The solution is identified with the actual mixed flow,
not merely postulated as a desired Jacobian. A midpoint position sensitivity
is compared only for this stated case; its covariance factor concerns the
gyro-only position contribution, not a complete estimator covariance.
-/
noncomputable section
open Matrix
open GNC.Magnus
open scoped Matrix.Norms.Operator
namespace GNC.Preintegration.Uncertainty

def zeroGyroBiasState (a bg ba : Vec3) (t : ℝ) : LogState :=
  t • inputDirection (-bg) (-ba) +
    (t^2/2) • ![-ba, a ⨯₃ bg, 0] + (t^3/6) • ![a ⨯₃ bg, 0, 0]

theorem zeroGyroBiasState_zero (a bg ba : Vec3) :
    zeroGyroBiasState a bg ba 0 = 0 := by simp [zeroGyroBiasState]

theorem zeroGyroBiasState_position (a bg ba : Vec3) (t : ℝ) :
    zeroGyroBiasState a bg ba t 0 =
      (t^3/6) • (a ⨯₃ bg) - (t^2/2) • ba := by
  simp [zeroGyroBiasState, inputDirection]
  abel

theorem zeroGyroBiasState_derivative (a bg ba : Vec3) (t : ℝ) :
    HasDerivAt (zeroGyroBiasState a bg ba)
      (errorGenerator 0 a (zeroGyroBiasState a bg ba t) + inputDirection (-bg) (-ba)) t := by
  have hd := (((hasDerivAt_id t).smul_const (inputDirection (-bg) (-ba))).add
    (((hasDerivAt_pow 2 t).div_const 2).smul_const (![-ba,a ⨯₃ bg,0] : LogState))).add
    (((hasDerivAt_pow 3 t).div_const 6).smul_const (![a ⨯₃ bg,0,0] : LogState))
  convert hd using 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [zeroGyroBiasState, errorGenerator, inputDirection, crossProduct, vecHead, vecTail] <;> ring <;> simp

theorem zeroGyroBiasState_hat_derivative (a bg ba : Vec3) (t : ℝ) :
    HasDerivAt (fun s => hat (zeroGyroBiasState a bg ba s))
      (hat (zeroGyroBiasState a bg ba t) * GNC.Magnus.extended ![0,a,0] 1 -
        GNC.Magnus.extended ![0,a,0] 1 * hat (zeroGyroBiasState a bg ba t) +
        hat (inputDirection (-bg) (-ba))) t := by
  have h := hatLinear.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t
    (zeroGyroBiasState_derivative a bg ba t)
  change HasDerivAt (fun s => hat (zeroGyroBiasState a bg ba s))
    (hat (errorGenerator 0 a (zeroGyroBiasState a bg ba t) + inputDirection (-bg) (-ba))) t at h
  have ha : hat (errorGenerator 0 a (zeroGyroBiasState a bg ba t) + inputDirection (-bg) (-ba)) =
      hat (errorGenerator 0 a (zeroGyroBiasState a bg ba t)) + hat (inputDirection (-bg) (-ba)) :=
    hatLinear.map_add _ _
  rw [ha, errorGenerator_hat] at h
  exact h

/-- Uniqueness identifies the explicit polynomial with the actual response
integral for every nominal right flow solving the stated constant generator. -/
theorem zeroGyroBias_leftResponse (a bg ba : Vec3) (U : ℝ → Mat5ˣ)
    (hU : ∀ t, HasDerivAt (fun s => (U s).val)
      ((U t).val * GNC.Magnus.extended ![0,a,0] 1) t) (T : ℝ) :
    leftResponse U (fun _ => hat (inputDirection (-bg) (-ba))) T =
      hat (zeroGyroBiasState a bg ba T) := by
  let N := GNC.Magnus.extended ![0,a,0] 1
  let B := hat (inputDirection (-bg) (-ba))
  let H : ℝ → Mat5 := fun t => leftResponse U (fun _ => B) t - hat (zeroGyroBiasState a bg ba t)
  have hd (t : ℝ) : HasDerivAt H (-N * H t + H t * N) t := by
    have h := (leftResponse_derivative U (fun _ => N) (fun _ => B) hU continuous_const t).sub
      (zeroGyroBiasState_hat_derivative a bg ba t)
    convert h using 1 <;> dsimp [H,N,B] <;> noncomm_ring
  have hz (t : ℝ) : HasDerivAt (fun _ : ℝ => (0 : Mat5)) ((-N)*0+0*N) t := by
    simpa using (hasDerivAt_const t (0 : Mat5))
  have he := GNC.Magnus.mixed_flow_unique (fun _ => -N) (fun _ => N)
    continuous_const continuous_const H (fun _ => 0) hd hz
    (by simp [H, leftResponse_zero, zeroGyroBiasState_zero];
        ext i j; fin_cases i <;> fin_cases j <;> simp [hat])
  have ht := congrFun he T
  exact sub_eq_zero.mp ht

/-- The polynomial is the derivative of the actual perturbed exponential,
expressed in the nominal left error. Constant bias is subtracted from inputs. -/
theorem zeroGyroBias_actual_left_derivative (a bg ba : Vec3) {T : ℝ} (hT : 0 ≤ T) :
    HasDerivAt (fun q : ℝ =>
      ((GNC.MixedInvariant.expUnit (T • GNC.Magnus.extended ![0,a,0] 1))⁻¹ *
        GNC.MixedInvariant.expUnit
          (T • (GNC.Magnus.extended ![0,a,0] 1 + q • hat (inputDirection (-bg) (-ba))))).val)
      (hat (zeroGyroBiasState a bg ba T)) 0 := by
  let N := GNC.Magnus.extended ![0,a,0] 1
  let B := hat (inputDirection (-bg) (-ba))
  let U : ℝ → ℝ → Mat5ˣ := fun q t => GNC.MixedInvariant.expUnit (t • (N+q • B))
  have hu (q t : ℝ) : HasDerivAt (fun s => (U q s).val) ((U q t).val*(N+q • B)) t := by
    simpa [U, GNC.MixedInvariant.expUnit] using hasDerivAt_exp_smul_const (N+q • B) t
  have h0 (q : ℝ) : U q 0 = 1 := by
    apply Units.ext; simp [U, GNC.MixedInvariant.expUnit]
  have h := actual_left_sample_derivative (fun _ => N) (fun _ => B) U
    continuous_const continuous_const hu h0 hT
  rw [zeroGyroBias_leftResponse a bg ba (U 0) (by simpa using hu 0)] at h
  simpa [U,N,B] using h

/-- Midpoint's gyro-only position column is 3/2 of the exact one in this
rotation-free, constant-acceleration case. -/
theorem midpoint_position_gyro_factor (a bg : Vec3) (T : ℝ) :
    (T^3/4) • (a ⨯₃ bg) =
      (3/2 : ℝ) • (zeroGyroBiasState a bg 0 T 0) := by
  rw [zeroGyroBiasState_position]
  simp only [smul_zero, sub_zero, smul_smul]
  congr 1
  ring

/-- This factor applies only to the gyro-bias contribution to position
covariance. Other uncertainty sources and cross terms need their own maps. -/
theorem midpoint_gyro_position_covariance_factor (a : Vec3)
    (Q : Matrix (Fin 3) (Fin 3) ℝ) (T : ℝ) :
    ((T^3/4) • skew a) * Q * (((T^3/4) • skew a)ᵀ) =
      (9/4 : ℝ) • (((T^3/6) • skew a) * Q * (((T^3/6) • skew a)ᵀ)) := by
  simp only [Matrix.transpose_smul, smul_mul_assoc, mul_smul_comm, smul_smul]
  congr 1
  ring

end GNC.Preintegration.Uncertainty
