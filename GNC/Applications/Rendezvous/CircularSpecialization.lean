import GNC.Applications.Rendezvous.HCW
import GNC.Applications.Rendezvous.Propagation
import GNC.Applications.Rendezvous.HCWCoordinates

/-! The circular-reference specialization of the actual retained operator,
including its radial tensor and the resulting second-order HCW equations. -/
noncomputable section
open Matrix Real
open scoped Matrix
namespace GNC

def circularMeanMotion (μ r : ℝ) : ℝ := √(μ/r^3)

theorem circularMeanMotion_sq (μ r : ℝ) (hμ : 0 ≤ μ) (hr : 0 < r) :
    (circularMeanMotion μ r)^2 = μ/r^3 := Real.sq_sqrt (div_nonneg hμ (by positivity))

theorem radial_tensor_circular (n : ℝ) (p : Vec3) :
    Gravity.radialMap (n^2) ![1,0,0] p = ![2*n^2*p 0,-n^2*p 1,-n^2*p 2] := by
  ext i; fin_cases i <;>
    simp [Gravity.radialMap, dotProduct, Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail] <;> ring

theorem forced_circular_field (μ n : ℝ) (R : SO3) (q : Vec3)
    (hn : μ/enorm q^3 = n^2) (hrad : Jacobian.unitAxis (rotate R⁻¹ q) = ![1,0,0])
    (x : LogState) :
    forcedLinear μ R q 0 ![0,0,n] 0 ![0,0,n] x =
      ![![x 1 0+n*x 0 1,x 1 1-n*x 0 0,x 1 2],
        ![2*n^2*x 0 0+n*x 1 1,-n^2*x 0 1-n*x 1 0,-n^2*x 0 2],
        -![0,0,n] ⨯₃ x 2] := by
  have hmean (w : Vec3) : (1/2:ℝ) • (w+w) = w := by module
  simp only [forcedLinear, hn, hrad, radial_tensor_circular, hmean, add_zero,
    smul_zero, map_zero, LinearMap.zero_apply, sub_zero]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [cross_apply, Matrix.vecHead, Matrix.vecTail] <;> ring

/-- Theorem 2 begins with (72) under the physical circular assumptions (35).
The radial tensor and component equations (39) are derived here. -/
theorem circular_specialization (μ r : ℝ) (hμ : 0 ≤ μ) (hr : 0 < r)
    (R : ℝ → SO3) (chief : ℝ → Vec3) (x : ℝ → LogState)
    (hradius : ∀ t, enorm (chief t) = r)
    (hradial : ∀ t, Jacobian.unitAxis (rotate (R t)⁻¹ (chief t)) = ![1,0,0])
    (hx : ∀ t, HasDerivAt x (forcedLinear μ (R t) (chief t)
      0 ![0,0,circularMeanMotion μ r] 0 ![0,0,circularMeanMotion μ r] (x t)) t)
    (t₀ : ℝ) (hzero : x t₀ 2 = 0) :
    (∀ t, x t 2 = 0) ∧ CircularLogODE (circularMeanMotion μ r) (fun t => x t 0) (fun t => x t 1) := by
  let n := circularMeanMotion μ r
  have hfield (t : ℝ) := forced_circular_field μ n (R t) (chief t)
    (by rw [hradius, circularMeanMotion_sq μ r hμ hr]) (hradial t) (x t)
  have hd (t : ℝ) := hx t
  have hatt (t : ℝ) (i : Fin 3) : HasDerivAt (fun s => x s 2 i) (-(![0,0,n] ⨯₃ x t 2) i) t := by
    have h := hasDerivAt_pi.mp (hasDerivAt_pi.mp (hd t) 2) i
    rw [hfield] at h
    change HasDerivAt (fun s => x s 2 i) ((-![0,0,n] ⨯₃ x t 2) i) t at h
    rw [map_neg, LinearMap.neg_apply] at h
    exact h
  refine ⟨fun t => zero_attitude_invariant (fun _ => ![0,0,n]) (fun s => x s 2) hatt t₀ hzero t,?_⟩
  intro t
  have h := hd t
  rw [hfield] at h
  exact ⟨hasDerivAt_pi.mp (hasDerivAt_pi.mp h 0) 0,
    hasDerivAt_pi.mp (hasDerivAt_pi.mp h 0) 1,
    hasDerivAt_pi.mp (hasDerivAt_pi.mp h 0) 2,
    hasDerivAt_pi.mp (hasDerivAt_pi.mp h 1) 0,
    hasDerivAt_pi.mp (hasDerivAt_pi.mp h 1) 1,
    hasDerivAt_pi.mp (hasDerivAt_pi.mp h 1) 2⟩

theorem circular_hcw (μ r : ℝ) (hμ : 0 ≤ μ) (hr : 0 < r)
    (R : ℝ → SO3) (chief : ℝ → Vec3) (x : ℝ → LogState)
    (hradius : ∀ t, enorm (chief t) = r)
    (hradial : ∀ t, Jacobian.unitAxis (rotate (R t)⁻¹ (chief t)) = ![1,0,0])
    (hx : ∀ t, HasDerivAt x (forcedLinear μ (R t) (chief t)
      0 ![0,0,circularMeanMotion μ r] 0 ![0,0,circularMeanMotion μ r] (x t)) t)
    (t₀ : ℝ) (hzero : x t₀ 2 = 0) (t : ℝ) :
    HasDerivAt (fun s => deriv (fun τ => x τ 0 0) s)
      (3*(circularMeanMotion μ r)^2*x t 0 0+2*circularMeanMotion μ r*deriv (fun s => x s 0 1) t) t ∧
    HasDerivAt (fun s => deriv (fun τ => x τ 0 1) s)
      (-2*circularMeanMotion μ r*deriv (fun s => x s 0 0) t) t ∧
    HasDerivAt (fun s => deriv (fun τ => x τ 0 2) s)
      (-(circularMeanMotion μ r)^2*x t 0 2) t :=
  hcw_recovery _ _ _ (circular_specialization μ r hμ hr R chief x hradius hradial hx t₀ hzero).2 t

/-- Remark 2: at zero attitude error, the exact gravity term differs from
the retained linear term only by the ordinary gravity Taylor remainder. -/
theorem zero_attitude_gravity_remainder (μ : ℝ) (chief deputy : SE23) (x : LogState)
    (he : SE23.error chief deputy = groupExp x) (hx : x 2 = 0) (hq : 0 < enorm chief.pos) :
    Jacobian.blockRightInverse x
      (adjoint deputy⁻¹ (velocityOnly (Gravity.field3 μ deputy.pos-Gravity.field3 μ chief.pos))) =
    velocityOnly (Gravity.radialMap (μ/enorm chief.pos^3)
      (Jacobian.unitAxis (rotate chief.rot⁻¹ chief.pos)) (x 0)) +
    velocityOnly (rotate chief.rot⁻¹ (Gravity.remainder3 μ chief.pos (rotate chief.rot (x 0)))) := by
  have hθ : enorm (x 2) < 2*π := by rw [hx]; simpa [enorm] using (mul_pos (by norm_num : (0:ℝ)<2) pi_pos)
  rw [gravity_right_transport chief deputy x _ he hθ, Jacobian.blockInverse_velocityOnly, hx]
  simp only [Jacobian.inverseAt, enorm, WithLp.toLp_zero, norm_zero, zero_div,
    map_zero, LinearMap.zero_apply, smul_zero, sub_zero, add_zero]
  have hpos : deputy.pos = chief.pos+rotate chief.rot (x 0) := by
    rw [physical_separation chief deputy x he, hx]
    simp [physicalImpulse, Jacobian.leftAt]
  have hg : Gravity.field3 μ deputy.pos-Gravity.field3 μ chief.pos =
      Gravity.gradient3 μ chief.pos (rotate chief.rot (x 0))+
        Gravity.remainder3 μ chief.pos (rotate chief.rot (x 0)) := by
    rw [hpos]
    unfold Gravity.remainder3
    abel
  rw [hg, rotate_add, Gravity.gradient3_body μ chief.rot chief.pos (x 0) hq, velocityOnly_add]
  rfl

end GNC
