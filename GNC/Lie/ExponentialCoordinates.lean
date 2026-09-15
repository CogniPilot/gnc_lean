import GNC.Lie.Exponential

/-! Injectivity of the exponential coordinates on the principal rotation
ball, and the exact impulse map of Lemma 5. -/
noncomputable section
open Matrix Real NormedSpace
open scoped Matrix Matrix.Norms.Operator
namespace GNC

theorem rotationExp_formula (q : Vec3) : (rotationExp q).val =
    1 + (sin (enorm q)/enorm q) • skew q +
      ((1-cos (enorm q))/enorm q^2) • skew q^2 := by
  by_cases hq : enorm q = 0
  · rw [(enorm_eq_zero_iff q).mp hq]
    simp [rotationExp, skew_zero]
  · simpa [rotationExp, Preintegration.rodrigues, Preintegration.f₁] using
      Preintegration.exp_rodrigues (skew q) (enorm q) 1 hq (skew_cube q)

theorem rotationExp_antisymmetric (q : Vec3) :
    (rotationExp q).val - (rotationExp q).valᵀ =
      (2*sin (enorm q)/enorm q) • skew q := by
  rw [rotationExp_formula]
  simp only [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one,
    Matrix.transpose_pow, skew_transpose, neg_sq]
  module

theorem rotationExp_trace (q : Vec3) : (rotationExp q).val.trace = 1+2*cos (enorm q) := by
  rw [rotationExp_formula]
  have hS : (skew q).trace = 0 := by simp [Matrix.trace, skew, Fin.sum_univ_succ]
  have hS2 : (skew q^2).trace = -2*enorm q^2 := by
    rw [enorm_sq]
    simp [Matrix.trace, skew, pow_two, Fin.sum_univ_succ, lengthSq]
    ring
  simp only [Matrix.trace_add, Matrix.trace_smul, smul_eq_mul, hS, hS2,
    mul_zero, add_zero, Matrix.trace_one, Fintype.card_fin]
  by_cases hq : enorm q = 0
  · norm_num [hq]
  · field_simp; ring

theorem skew_injective : Function.Injective skew := by
  intro u v h
  ext i; fin_cases i
  · exact congrFun (congrFun h 2) 1
  · exact congrFun (congrFun h 0) 2
  · exact congrFun (congrFun h 1) 0

/-- Rotation vectors of length less than π are unique. -/
theorem rotationExp_injective {q r : Vec3} (hq : enorm q < π) (hr : enorm r < π)
    (h : rotationExp q = rotationExp r) : q = r := by
  have hR := congrArg Subtype.val h
  have hc := congrArg Matrix.trace hR
  rw [rotationExp_trace, rotationExp_trace] at hc
  have hn : enorm q = enorm r := injOn_cos ⟨enorm_nonneg q,hq.le⟩
    ⟨enorm_nonneg r,hr.le⟩ (by linarith)
  by_cases hz : enorm q = 0
  · rw [(enorm_eq_zero_iff q).mp hz, (enorm_eq_zero_iff r).mp (hn.symm.trans hz)]
  · have hp : 0 < enorm q := lt_of_le_of_ne (enorm_nonneg q) (Ne.symm hz)
    have hs : 2*sin (enorm q)/enorm q ≠ 0 :=
      div_ne_zero (mul_ne_zero (by norm_num) (sin_pos_of_pos_of_lt_pi hp hq).ne') hz
    have he := congrArg (fun R : Matrix (Fin 3) (Fin 3) ℝ => R-Rᵀ) hR
    dsimp only at he
    rw [rotationExp_antisymmetric, rotationExp_antisymmetric, ← hn] at he
    apply skew_injective
    exact (smul_right_injective _ hs) he

namespace Jacobian

theorem inverseAt_leftAt_all (q v : Vec3) (hq : enorm q < 2*π) :
    inverseAt q (leftAt q v) = v := by
  by_cases hz : enorm q = 0
  · rw [(enorm_eq_zero_iff q).mp hz]; simp [inverseAt, leftAt]
  · exact inverseAt_leftAt q v (lt_of_le_of_ne (enorm_nonneg q) (Ne.symm hz)) hq

theorem leftAt_inverseAt_all (q v : Vec3) (hq : enorm q < 2*π) :
    leftAt q (inverseAt q v) = v := by
  by_cases hz : enorm q = 0
  · rw [(enorm_eq_zero_iff q).mp hz]; simp [inverseAt, leftAt]
  · exact leftAt_inverseAt q v (lt_of_le_of_ne (enorm_nonneg q) (Ne.symm hz)) hq

end Jacobian

/-- Principal SE₂(3) coordinates are injective, including zero attitude. -/
theorem groupExp_injective {x y : LogState} (hx : enorm (x 2) < π) (hy : enorm (y 2) < π)
    (h : groupExp x = groupExp y) : x = y := by
  have hq : x 2 = y 2 := rotationExp_injective hx hy (congrArg SE23.rot h)
  have hv := congrArg SE23.vel h
  have hp := congrArg SE23.pos h
  change Jacobian.leftAt (x 2) (x 1) = Jacobian.leftAt (y 2) (y 1) at hv
  change Jacobian.leftAt (x 2) (x 0) = Jacobian.leftAt (y 2) (y 0) at hp
  rw [← hq] at hv hp
  have hi (u v : Vec3) (he : Jacobian.leftAt (x 2) u = Jacobian.leftAt (x 2) v) : u = v := by
    have he' := congrArg (Jacobian.inverseAt (x 2)) he
    simpa only [Jacobian.inverseAt_leftAt_all (x 2) _ (by linarith [pi_pos])] using he'
  funext i
  fin_cases i
  · exact hi _ _ hp
  · exact hi _ _ hv
  · exact hq

def impulseCoordinates (x : LogState) (dv : Vec3) : LogState := ![x 0,x 1+dv,x 2]

def physicalImpulse (R : SO3) (q dv : Vec3) : Vec3 := rotate R (Jacobian.leftAt q dv)

/-- The inertial increment and log-coordinate increment are exact inverses. -/
theorem impulse_map_inverse (R : SO3) (q dv : Vec3) (hq : enorm q < 2*π) :
    physicalImpulse R q (Jacobian.inverseAt q (rotate R⁻¹ dv)) = dv := by
  rw [physicalImpulse, Jacobian.leftAt_inverseAt_all q _ hq, ← rotate_mul]
  simp

/-- Lemma 5: the proposed post-impulse coordinates exponentiate to the actual
post-impulse error. No differential approximation is used. -/
theorem impulse_coordinates (chief deputy : SE23) (x : LogState) (dv : Vec3)
    (hx : enorm (x 2) < π) (he : SE23.error chief deputy = groupExp x) :
    SE23.error chief (SE23.impulse deputy dv) =
      groupExp (impulseCoordinates x (Jacobian.inverseAt (x 2) (rotate chief.rot⁻¹ dv))) := by
  have h := SE23.impulse_error chief deputy dv
  apply SE23.ext
  · simpa [he, groupExp, impulseCoordinates] using h.2.1
  · rw [h.2.2, he]
    simp [groupExp, impulseCoordinates, Jacobian.leftAt_add,
      Jacobian.leftAt_inverseAt_all (x 2) _ (by linarith [pi_pos])]
  · simpa [he, groupExp, impulseCoordinates] using h.1

/-- The post-impulse coordinate formula is unique within the principal ball. -/
theorem impulse_coordinates_unique (chief deputy : SE23) (x y : LogState) (dv : Vec3)
    (hx : enorm (x 2) < π) (hy : enorm (y 2) < π)
    (he : SE23.error chief deputy = groupExp x)
    (he' : SE23.error chief (SE23.impulse deputy dv) = groupExp y) :
    y = impulseCoordinates x (Jacobian.inverseAt (x 2) (rotate chief.rot⁻¹ dv)) := by
  apply groupExp_injective hy (by simpa [impulseCoordinates])
  rw [← he']
  exact impulse_coordinates chief deputy x dv hx he

/-- Equation (83), with the actual rotation and Jacobian map. -/
theorem physicalImpulse_bounds (R : SO3) (k dv : Vec3) (hk : k ⬝ᵥ k = 1)
    (t : ℝ) (ht : 0 < t) (htπ : t < 2*π) :
    Jacobian.contraction t*enorm dv ≤ enorm (physicalImpulse R (t • k) dv) ∧
      enorm (physicalImpulse R (t • k) dv) ≤ enorm dv := by
  rw [physicalImpulse, rotate_enorm, Jacobian.leftAt_axis k dv hk t ht]
  exact Jacobian.left_bounds k dv hk t ht htπ

end GNC
