import GNC.Dynamics.LogDynamics

noncomputable section
open Matrix NormedSpace
open scoped Matrix Matrix.Norms.Operator
namespace GNC

theorem matrix_inverse (X : SE23) : Ring.inverse (SE23.toMatrix X) = SE23.toMatrix X⁻¹ := by
  change Ring.inverse (SE23.matrixUnits X : Mat5) = (SE23.matrixUnits X⁻¹ : Mat5)
  rw [map_inv, Ring.inverse_unit]

theorem matrix_inverse_derivative {X : ℝ → SE23} {D : Mat5} {t : ℝ}
    (hX : HasDerivAt (fun s => SE23.toMatrix (X s)) D t) :
    HasDerivAt (fun s => SE23.toMatrix (X s)⁻¹)
      (-(SE23.toMatrix (X t)⁻¹*D*SE23.toMatrix (X t)⁻¹)) t := by
  have h := (hasFDerivAt_ringInverse (𝕜 := ℝ) (SE23.matrixUnits (X t))).comp_hasDerivAt t hX
  change HasDerivAt (fun s => Ring.inverse (SE23.toMatrix (X s))) _ t at h
  simp only [matrix_inverse] at h
  convert h using 1

theorem matrix_inv_mul (X : SE23) : SE23.toMatrix X⁻¹*SE23.toMatrix X = 1 := by
  rw [← SE23.toMatrix_mul, inv_mul_cancel, SE23.toMatrix_one]

theorem matrix_mul_inv (X : SE23) : SE23.toMatrix X*SE23.toMatrix X⁻¹ = 1 := by
  rw [← SE23.toMatrix_mul, mul_inv_cancel, SE23.toMatrix_one]

theorem gravity_intertwine (X : SE23) (g : Vec3) :
    SE23.toMatrix X*hat (velocityOnly g) =
      hat (velocityOnly (rotate X.rot g))*SE23.toMatrix X := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [SE23.toMatrix, hat, velocityOnly, rotate, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ] <;> ring

def spacecraftDerivative (X : SE23) (ν : LogState) (g : Vec3) : Mat5 :=
  (hat (velocityOnly g)-kinematicC)*SE23.toMatrix X +
    SE23.toMatrix X*(hat ν+kinematicC)

theorem matrix_error_derivative {X Y : ℝ → SE23} {ν νbar : LogState} {g gbar : Vec3} {t : ℝ}
    (hX : HasDerivAt (fun s => SE23.toMatrix (X s)) (spacecraftDerivative (X t) ν g) t)
    (hY : HasDerivAt (fun s => SE23.toMatrix (Y s)) (spacecraftDerivative (Y t) νbar gbar) t) :
    HasDerivAt (fun s => SE23.toMatrix (SE23.error (Y s) (X s)))
      (SE23.toMatrix (SE23.error (Y t) (X t))*(hat ν+kinematicC)-
        (hat ν+kinematicC)*SE23.toMatrix (SE23.error (Y t) (X t))+
        hat (ν-νbar+velocityOnly (rotate (Y t).rot⁻¹ (g-gbar)))*
          SE23.toMatrix (SE23.error (Y t) (X t))) t := by
  have h := (matrix_inverse_derivative hY).mul hX
  simp only [SE23.error, SE23.toMatrix_mul]
  convert h using 1
  unfold spacecraftDerivative
  change _ = _
  have hgrav (a : Vec3) : SE23.toMatrix (Y t)⁻¹*hat (velocityOnly a) =
      hat (velocityOnly (rotate (Y t).rot⁻¹ a))*SE23.toMatrix (Y t)⁻¹ :=
    gravity_intertwine (Y t)⁻¹ a
  have hv : hat (ν-νbar+velocityOnly (rotate (Y t).rot⁻¹ (g-gbar))) =
      hat ν-hat νbar+hat (velocityOnly (rotate (Y t).rot⁻¹ g))-
        hat (velocityOnly (rotate (Y t).rot⁻¹ gbar)) := by
    change hatLinear _ = _
    rw [map_add, map_sub, rotate_sub]
    have he : velocityOnly (rotate (Y t).rot⁻¹ g-rotate (Y t).rot⁻¹ gbar) =
        velocityOnly (rotate (Y t).rot⁻¹ g)-velocityOnly (rotate (Y t).rot⁻¹ gbar) := by
      ext i j; fin_cases i <;> simp [velocityOnly]
    rw [he, map_sub]
    change hat ν-hat νbar+(hat (velocityOnly (rotate (Y t).rot⁻¹ g))-
      hat (velocityOnly (rotate (Y t).rot⁻¹ gbar))) = _
    abel
  rw [hv]
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub,
    Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc, matrix_mul_inv, Matrix.mul_one,
    ← Matrix.mul_assoc, matrix_inv_mul, Matrix.one_mul, hgrav]
  noncomm_ring
  have hy (Z : Mat5) : SE23.toMatrix (Y t)*(SE23.toMatrix (Y t)⁻¹*Z) = Z := by
    rw [← Matrix.mul_assoc, matrix_mul_inv, Matrix.one_mul]
  simp only [hy]
  simp only [neg_one_smul]
  abel

/-- Proposition 1 in the equivalent reference-frame gravity form. The input
trajectories satisfy the actual matrix equations (5); x is any differentiable
principal log lift of their group error. -/
theorem spacecraft_log_equation {X Y : ℝ → SE23} {x : ℝ → LogState}
    {dx ν νbar : LogState} {g gbar : Vec3} {t : ℝ}
    (hX : HasDerivAt (fun s => SE23.toMatrix (X s)) (spacecraftDerivative (X t) ν g) t)
    (hY : HasDerivAt (fun s => SE23.toMatrix (Y s)) (spacecraftDerivative (Y t) νbar gbar) t)
    (hx : HasDerivAt x dx t) (he : ∀ s, SE23.error (Y s) (X s) = groupExp (x s))
    (hqπ : enorm (x t 2) < Real.pi) :
    dx = logDrift ν (x t)+Jacobian.blockInverse (x t)
      (ν-νbar+velocityOnly (rotate (Y t).rot⁻¹ (g-gbar))) := by
  have h := matrix_error_derivative hX hY
  simp_rw [he, groupExp_toMatrix] at h
  exact log_error_equation hx (by linarith [Real.pi_pos]) h

end GNC
