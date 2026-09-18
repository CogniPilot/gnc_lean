import GNC.Applications.OrbitalComparison.CenteredResponsePhysicalOperators
import GNC.Applications.OrbitalComparison.JointErrorInitialState
import GNC.Dynamics.RotationCenteredError

/-! Identify the stored eight features with the actual half rotation.
The omitted (2,2) entry multiplies zero in the planar nominal force and
initial data; all three response outputs and all attitude axes remain. -/
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace GNC.OrbitalComparison.CenteredResponseData
open CartesianResponsePolynomial Matrix Set

def halfRotation (φ : Vec3) : SO3 := rotationExp ((1/2:ℝ) • φ)
def matrixFeatures (A : Matrix (Fin 3) (Fin 3) ℝ) : Fin 8 → ℝ :=
  ![A 0 0,A 0 1,A 0 2,A 1 0,A 1 1,A 1 2,A 2 0,A 2 1]
def rotationWeights (φ : Vec3) : Fin 8 → ℝ := matrixFeatures ((halfRotation φ).val-1)
def forceDifference (φ : Vec3) (t : ℝ) : E3 :=
  WithLp.toLp 2 (rotate (halfRotation φ) (JointErrorData.exactForce t)-JointErrorData.exactForce t)

theorem matrix_features_entry (A : Matrix (Fin 3) (Fin 3) ℝ) (j : Fin 8) :
    matrixFeatures A j=A (featureRow j) (featureColumn j) := by
  fin_cases j <;> rfl

theorem half_rotation_difference (φ b : Vec3) (hφ : enorm φ≤1/10) :
    enorm (rotate (halfRotation φ) b-b)≤(1/20)*enorm b := by
  have ha : enorm φ<4*Real.pi := by linarith [Real.two_le_pi]
  have h := RotationCenteredError.centered_thrust_bound φ b ha
  rw [RotationCenteredError.centered_thrust] at h
  change enorm (rotate (halfRotation φ) b-b)≤enorm φ/2*enorm b at h
  exact h.trans (mul_le_mul_of_nonneg_right (by linarith) (enorm_nonneg b))

theorem rotation_weights_bound (φ : Vec3) (hφ : enorm φ≤1/10) (j : Fin 8) :
    |rotationWeights φ j|≤1/20 := by
  let c := featureColumn j
  let e : Vec3 := Pi.single c 1
  have he : enorm e=1 := by
    change ‖(WithLp.toLp 2 (Pi.single c (1:ℝ)) : E3)‖=1
    simp
  have hm : rotationWeights φ j=(rotate (halfRotation φ) e-e) (featureRow j) := by
    rw [rotationWeights,matrix_features_entry]
    simp [rotate,e,c,Matrix.one_apply,Pi.single_apply]
  rw [hm]
  have h := (component_le_enorm (rotate (halfRotation φ) e-e) (featureRow j)).trans
    (half_rotation_difference φ e hφ)
  simpa only [he,mul_one] using h

theorem source_response_matrix (A : Matrix (Fin 3) (Fin 3) ℝ) (t : ℝ) :
    (response sources (matrixFeatures A) t).ofLp=A *ᵥ value forcePolynomial t := by
  rw [response_value]
  ext i
  change (combination sources (matrixFeatures A) t) i=_
  simp only [combination,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,source_value]
  have hz : value forcePolynomial t 2=0 := rfl
  fin_cases i <;>
    norm_num [matrixFeatures,featureRow,featureColumn,Fin.sum_univ_succ,
      Matrix.mulVec,dotProduct,Matrix.cons_val_two,vecHead,vecTail,Fin.ext_iff,hz] <;> ring
  change A 2 0 * value forcePolynomial t 0 + A 2 1 * value forcePolynomial t 1 =
    value forcePolynomial t 0 * A 2 0 + value forcePolynomial t 1 * A 2 1
  ring

theorem source_response_rotation (φ : Vec3) (t : ℝ) :
    response sources (rotationWeights φ) t=
      WithLp.toLp 2 (rotate (halfRotation φ) (value forcePolynomial t)-value forcePolynomial t) := by
  have h := source_response_matrix ((halfRotation φ).val-1) t
  rw [Matrix.sub_mulVec,Matrix.one_mulVec] at h
  exact congrArg (WithLp.toLp 2) h

theorem rotation_force_mismatch (φ : Vec3) (hφ : enorm φ≤1/10)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ‖forceDifference φ t-response sources (rotationWeights φ) t‖≤
      (1/20)*(forceFactor:ℝ)*(phaseError:ℝ) := by
  rw [source_response_rotation]
  have he : forceDifference φ t-
      WithLp.toLp 2 (rotate (halfRotation φ) (value forcePolynomial t)-value forcePolynomial t)=
      WithLp.toLp 2 (rotate (halfRotation φ)
        (JointErrorData.exactForce t-value forcePolynomial t)-
        (JointErrorData.exactForce t-value forcePolynomial t)) := by
    simp only [forceDifference,rotate_sub,WithLp.toLp_sub]
    module
  rw [he]
  change enorm (_ - _)≤_
  calc
    _≤(1/20)*enorm (JointErrorData.exactForce t-value forcePolynomial t) :=
      half_rotation_difference φ _ hφ
    _≤(1/20)*((forceFactor:ℝ)*(phaseError:ℝ)) :=
      mul_le_mul_of_nonneg_left (force_transfer ht) (by norm_num)
    _=_ := by ring

theorem rotation_force_bound (φ : Vec3) (hφ : enorm φ≤1/10)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ‖forceDifference φ t‖≤(1/20)*(forceFactor:ℝ) := by
  exact (half_rotation_difference φ _ hφ).trans
    (mul_le_mul_of_nonneg_left (exact_force_bound ht) (by norm_num))

theorem first_rotation_defect (φ : Vec3) (hφ : enorm φ≤1/10)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ‖firstAcceleration (rotationWeights φ) t-
      (Gravity.gradient (K:ℝ) (nominal t) (firstResponse (rotationWeights φ) t)+forceDifference φ t)‖≤
      (firstDefect:ℝ) :=
  first_physical_operator_defect (rotationWeights φ) (rotation_weights_bound φ hφ)
    (forceDifference φ t) ht (rotation_force_mismatch φ hφ ht)

theorem second_rotation_defect (φ : Vec3) (hφ : enorm φ≤1/10)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ‖secondAcceleration (rotationWeights φ) t-
      (Gravity.gradient (K:ℝ) (nominal t) (secondResponse (rotationWeights φ) t)+
        (1/2:ℝ) • Gravity.hessian (K:ℝ) (nominal t)
          (firstResponse (rotationWeights φ) t) (firstResponse (rotationWeights φ) t))‖≤
      (secondDefect:ℝ) :=
  second_physical_operator_defect (rotationWeights φ) (rotation_weights_bound φ hφ) ht

end GNC.OrbitalComparison.CenteredResponseData
