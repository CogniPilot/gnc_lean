import GNC.Applications.OrbitalComparison.CenteredResponseGeometry

/-! The actual stored initial coefficient data reconstruct the same
correlated midpoint state as the Lie predictor. Half-rotation centering
preserves its quadratic angular size, rather than using an independent
box bound on the eight rotation entries for the initial response. -/
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace GNC.OrbitalComparison.CenteredResponseData
open CartesianResponsePolynomial Matrix Set

def firstVelocity (w : Fin 8 → ℝ) (t : ℝ) : E3 :=
  response (fun j => derivative (first j)) w t
def secondVelocity (w : Fin 8 → ℝ) (t : ℝ) : E3 :=
  response (fun j => derivative (second j)) (productWeights w) t

theorem polynomial_at_zero (p : List ℚ) : PolynomialOrder.value p 0=(p.headD 0:ℝ) := by
  cases p <;> simp [PolynomialOrder.value,Planning.PolynomialKernel.evaluate]

theorem first_curve_initial (j : Fin 8) :
    curve (first j) 0=WithLp.toLp 2 (fun i => (initialFirst j i:ℝ)) := by
  ext i
  change PolynomialOrder.value (first j i) 0=_
  rw [polynomial_at_zero,(first_initial j i).1]

theorem first_curve_velocity_initial (j : Fin 8) :
    curve (derivative (first j)) 0=WithLp.toLp 2 (fun i => (initialVelocity j i:ℝ)) := by
  ext i
  change PolynomialOrder.value (derivative (first j) i) 0=_
  rw [polynomial_at_zero,(first_initial j i).2]

theorem first_initial_value (w : Fin 8 → ℝ) :
    firstResponse w 0=SpatialBurn.pack (w 0) ((w 1+w 3)/2) ((w 2+w 6)/2) := by
  rw [first_response_value]
  simp only [response,first_curve_initial]
  rw [SpatialBurn.pack_eq]
  ext i
  fin_cases i <;>
    norm_num [initialFirst,Fin.sum_univ_succ,Matrix.cons_val_two,vecHead,vecTail] <;> ring_nf <;> rfl

theorem first_initial_velocity_value (w : Fin 8 → ℝ) :
    firstVelocity w 0=SpatialBurn.pack ((3231/50000)*(w 1+w 3))
      ((3231/25000)*w 4) ((3231/50000)*(w 5+w 7)) := by
  simp only [firstVelocity,response,first_curve_velocity_initial]
  rw [SpatialBurn.pack_eq]
  ext i
  fin_cases i <;>
    norm_num [initialVelocity,Fin.sum_univ_succ,Matrix.cons_val_two,vecHead,vecTail] <;> ring_nf <;> rfl

theorem second_curve_initial (j : Fin 36) : curve (second j) 0=0 := by
  ext i
  change PolynomialOrder.value (second j i) 0=0
  rw [polynomial_at_zero,(second_initial j i).1,Rat.cast_zero]

theorem second_curve_velocity_initial (j : Fin 36) : curve (derivative (second j)) 0=0 := by
  ext i
  change PolynomialOrder.value (derivative (second j) i) 0=0
  rw [polynomial_at_zero,(second_initial j i).2,Rat.cast_zero]

theorem second_initial_value (w : Fin 8 → ℝ) : secondResponse w 0=0 := by
  rw [second_response_value]
  simp only [response,second_curve_initial,smul_zero,Finset.sum_const_zero]

theorem second_initial_velocity_value (w : Fin 8 → ℝ) : secondVelocity w 0=0 := by
  simp only [secondVelocity,response,second_curve_velocity_initial,smul_zero,Finset.sum_const_zero]

theorem inverse_rotation_matrix (S : SO3) : S⁻¹.val=S.val.transpose := rfl

theorem first_initial_centered (φ : Vec3) :
    firstResponse (rotationWeights φ) 0=WithLp.toLp 2
      (RotationCenteredError.centered φ JointErrorData.initialReferencePosition) := by
  rw [first_initial_value,SpatialBurn.pack_eq,RotationCenteredError.centered_symmetrized]
  change WithLp.toLp 2 _=WithLp.toLp 2 ((1/2:ℝ) •
    (rotate (halfRotation φ)⁻¹ JointErrorData.initialReferencePosition+
      rotate (halfRotation φ) JointErrorData.initialReferencePosition)-
        JointErrorData.initialReferencePosition)
  ext i
  fin_cases i <;>
    norm_num [rotationWeights,matrixFeatures,rotate,inverse_rotation_matrix,
      JointErrorData.initialReferencePosition,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      Matrix.cons_val_succ',Matrix.cons_val_zero',vecHead,vecTail,Matrix.one_apply,Fin.ext_iff] <;>
      ring_nf <;> rfl

theorem first_velocity_initial_centered (φ : Vec3) :
    firstVelocity (rotationWeights φ) 0=WithLp.toLp 2
      (RotationCenteredError.centered φ JointErrorData.initialReferenceVelocity) := by
  rw [first_initial_velocity_value,SpatialBurn.pack_eq,RotationCenteredError.centered_symmetrized]
  change WithLp.toLp 2 _=WithLp.toLp 2 ((1/2:ℝ) •
    (rotate (halfRotation φ)⁻¹ JointErrorData.initialReferenceVelocity+
      rotate (halfRotation φ) JointErrorData.initialReferenceVelocity)-
        JointErrorData.initialReferenceVelocity)
  ext i
  fin_cases i <;>
    norm_num [rotationWeights,matrixFeatures,rotate,inverse_rotation_matrix,
      JointErrorData.initialReferenceVelocity,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      Matrix.cons_val_succ',Matrix.cons_val_zero',vecHead,vecTail,Matrix.one_apply,Fin.ext_iff] <;>
      ring_nf <;> rfl

theorem first_initial_bound (φ : Vec3) (hφ : enorm φ≤1/10) :
    ‖firstResponse (rotationWeights φ) 0‖≤1/800 := by
  rw [first_initial_centered]
  have h := RotationCenteredError.centered_bound φ JointErrorData.initialReferencePosition
    (by linarith [Real.two_le_pi])
  have hn : enorm JointErrorData.initialReferencePosition=1 := by
    rw [←JointErrorData.reference_initial_position]
    exact JointErrorData.exactReference_norm 0
  rw [hn,mul_one] at h
  have hs := pow_le_pow_left₀ (enorm_nonneg φ) hφ 2
  change enorm _≤_
  nlinarith

theorem initial_reference_velocity_norm : enorm JointErrorData.initialReferenceVelocity=3231/25000 := by
  have hs := enorm_sq JointErrorData.initialReferenceVelocity
  change enorm JointErrorData.initialReferenceVelocity^2=0^2+(3231/25000)^2+0^2 at hs
  nlinarith [enorm_nonneg JointErrorData.initialReferenceVelocity]

theorem first_velocity_initial_bound (φ : Vec3) (hφ : enorm φ≤1/10) :
    ‖firstVelocity (rotationWeights φ) 0‖≤3231/20000000 := by
  rw [first_velocity_initial_centered]
  have h := RotationCenteredError.centered_bound φ JointErrorData.initialReferenceVelocity
    (by linarith [Real.two_le_pi])
  rw [initial_reference_velocity_norm] at h
  have hs := pow_le_pow_left₀ (enorm_nonneg φ) hφ 2
  change enorm _≤_
  nlinarith

end GNC.OrbitalComparison.CenteredResponseData
