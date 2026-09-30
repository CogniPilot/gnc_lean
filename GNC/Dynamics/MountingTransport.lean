import GNC.Dynamics.MountingErrorCoordinates
import GNC.Dynamics.OrbitalNearAffine

/-! The extra transport defect for a body-fixed thruster mounting error.
Its dependence on omega cross phi gives an exact commuting-axis case and
a quadratic remainder for the augmented translation/mounting coordinates.
The one-radian chart agrees with the existing orbital remainder theorem.
-/
noncomputable section
namespace GNC.MountingTransport
open Matrix Real
open MountingErrorCoordinates (transport)

def commutator (φ ω x : Vec3) : Vec3 :=
  ω ⨯₃ Jacobian.leftAt φ x-Jacobian.leftAt φ (ω ⨯₃ x)

def defect (φ ω x : Vec3) : Vec3 := transport φ ω x-ω ⨯₃ x

/-- This exposes the axis-dependent term; replacing it by a generic
rotation-rate allowance would lose its exact zeros. -/
theorem commutator_formula (φ ω x : Vec3) :
    commutator φ ω x=
      ((1-cos (enorm φ))/enorm φ^2) • ((ω ⨯₃ φ) ⨯₃ x)+
      ((enorm φ-sin (enorm φ))/enorm φ^3) •
        ((ω ⨯₃ φ) ⨯₃ (φ ⨯₃ x)+φ ⨯₃ ((ω ⨯₃ φ) ⨯₃ x)) := by
  ext i
  fin_cases i <;> simp [commutator, Jacobian.leftAt, cross_apply,
    Matrix.vecHead, Matrix.vecTail] <;> ring

theorem defect_formula (φ ω x : Vec3) (hφ : enorm φ<2*π) :
    defect φ ω x=Jacobian.inverseAt φ (commutator φ ω x) := by
  rw [commutator, Jacobian.inverseAt_sub', Jacobian.inverseAt_leftAt_all φ _ hφ]
  rfl

/-- A fixed mounting offset is transported without an additional defect
when its axis commutes with the frame rotation. Includes zero rate/angle. -/
theorem defect_zero_of_cross_zero (φ ω x : Vec3) (hφ : enorm φ<2*π)
    (hc : ω ⨯₃ φ=0) : defect φ ω x=0 := by
  rw [defect_formula φ ω x hφ, commutator_formula, hc]
  simp

theorem coefficients {θ : ℝ} (hθ : 0<θ) (hθ1 : θ≤1) :
    0≤(1-cos θ)/θ^2 ∧ (1-cos θ)/θ^2≤1/2 ∧
    0≤(θ-sin θ)/θ^3 ∧ (θ-sin θ)/θ^3≤1/4 := by
  have hs0 : 0≤sin (θ/2) := (sin_pos_of_pos_of_lt_pi (by linarith)
    (by linarith [pi_gt_three])).le
  have hs := sin_le (show 0≤θ/2 by linarith)
  have hc : 1-cos θ≤θ^2/2 := by
    rw [Jacobian.half_cos]
    nlinarith
  refine ⟨div_nonneg (sub_nonneg.mpr (cos_le_one _)) (sq_nonneg _),?_,
    div_nonneg (sub_nonneg.mpr (sin_le hθ.le)) (by positivity),?_⟩
  · apply (div_le_iff₀ (sq_pos_of_pos hθ)).mpr
    nlinarith
  · apply (div_le_iff₀ (pow_pos hθ 3)).mpr
    linarith [sin_gt_sub_cube hθ hθ1]

theorem commutator_bound (φ ω x : Vec3) (hφ : enorm φ≤1) :
    enorm (commutator φ ω x)≤
      ((1+enorm φ)/2)*enorm (ω ⨯₃ φ)*enorm x := by
  by_cases hz : φ=0
  · simp [hz, commutator, Jacobian.leftAt, enorm]
  have hp : 0<enorm φ := lt_of_le_of_ne (enorm_nonneg _) (Ne.symm
    (fun h => hz ((enorm_eq_zero_iff _).mp h)))
  obtain ⟨ha0,ha,hb0,hb⟩ := coefficients hp hφ
  have hd := cross_enorm_le (ω ⨯₃ φ) x
  have h1 := (cross_enorm_le (ω ⨯₃ φ) (φ ⨯₃ x)).trans
    (mul_le_mul_of_nonneg_left (cross_enorm_le φ x) (enorm_nonneg _))
  have h2 := (cross_enorm_le φ ((ω ⨯₃ φ) ⨯₃ x)).trans
    (mul_le_mul_of_nonneg_left hd (enorm_nonneg _))
  have h12 := (enorm_add_le ((ω ⨯₃ φ) ⨯₃ (φ ⨯₃ x))
    (φ ⨯₃ ((ω ⨯₃ φ) ⨯₃ x))).trans (add_le_add h1 h2)
  rw [commutator_formula]
  apply (enorm_add_le _ _).trans
  rw [enorm_smul, enorm_smul, abs_of_nonneg ha0, abs_of_nonneg hb0]
  have hfirst := mul_le_mul ha hd (enorm_nonneg _) (by norm_num : (0:ℝ)≤1/2)
  have hsecond := mul_le_mul hb h12 (enorm_nonneg _) (by norm_num : (0:ℝ)≤1/4)
  convert add_le_add hfirst hsecond using 1 <;> ring

/-- Explicit angular-rate/mounting-axis dependence. The constant comes
from the proved inverse-Jacobian gain and elementary coefficient bounds. -/
theorem defect_bound (φ ω x : Vec3) (hφ : enorm φ≤1) :
    enorm (defect φ ω x)≤
      ((2/3:ℝ)*(1+enorm φ))*enorm (ω ⨯₃ φ)*enorm x := by
  by_cases hz : φ=0
  · simp [hz, defect, transport, Jacobian.inverseAt, Jacobian.leftAt, enorm]
  have hp : 0<enorm φ := lt_of_le_of_ne (enorm_nonneg _) (Ne.symm
    (fun h => hz ((enorm_eq_zero_iff _).mp h)))
  have hchart : enorm φ<2*π := by linarith [pi_gt_three]
  rw [defect_formula φ ω x hchart, Jacobian.inverseAt_eq φ _ hp]
  have hi := Jacobian.leftInv_bound (Jacobian.unitAxis φ) (commutator φ ω x)
    (Jacobian.unitAxis_unit φ hp) (enorm φ) hp hchart
  have hg := OrbitalNearAffine.inverse_gain hp hφ
  have hb := commutator_bound φ ω x hφ
  exact hi.trans ((mul_le_mul hg hb (enorm_nonneg _) (by norm_num : (0:ℝ)≤4/3)).trans_eq (by ring))

/-- A convenient uniform quadratic majorant, still retaining the exact
cross-axis cancellation rather than just the magnitude of angular rate. -/
theorem defect_uniform (φ ω x : Vec3) (hφ : enorm φ≤1) :
    enorm (defect φ ω x)≤(4/3:ℝ)*enorm (ω ⨯₃ φ)*enorm x := by
  apply (defect_bound φ ω x hφ).trans
  have hc : (2/3:ℝ)*(1+enorm φ)≤4/3 := by linarith
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hc (enorm_nonneg _)) (enorm_nonneg _)

end GNC.MountingTransport
