import GNC.Dynamics.MountingTransport
import GNC.Lie.RotationKinematics

/-! Exact finite transport for a fixed mounting angle. The Jacobian-conjugated
rotation is an isometry in the pulled-back physical norm and is uniformly
bounded in Euclidean norm independently of elapsed time and angular rate.
This concerns frame transport only, not gravity or total orbital growth.
-/
noncomputable section
namespace GNC.MountingTransportFlow
open Matrix Real MountingErrorCoordinates

def flow (φ : Vec3) (R S : SO3) (x : Vec3) : Vec3 :=
  Jacobian.inverseAt φ (rotate R⁻¹ (rotate S (Jacobian.leftAt φ x)))

def physicalNorm (φ x : Vec3) : ℝ := enorm (Jacobian.leftAt φ x)

theorem reconstruction (φ : Vec3) (hφ : enorm φ<2*π) (R S : SO3) (x : Vec3) :
    Jacobian.leftAt φ (flow φ R S x)=
      rotate R⁻¹ (rotate S (Jacobian.leftAt φ x)) :=
  Jacobian.leftAt_inverseAt_all φ _ hφ

theorem same_frame (φ : Vec3) (hφ : enorm φ<2*π) (R : SO3) (x : Vec3) :
    flow φ R R x=x := by
  simp only [flow, ←rotate_mul, inv_mul_cancel, rotate_one,
    Jacobian.inverseAt_leftAt_all φ _ hφ]

/-- Composition follows actual frame orientations. No constant-rate or
commuting-rate assumption is used. -/
theorem compose (φ : Vec3) (hφ : enorm φ<2*π) (R S U : SO3) (x : Vec3) :
    flow φ R S (flow φ S U x)=flow φ R U x := by
  unfold flow
  rw [Jacobian.leftAt_inverseAt_all φ _ hφ]
  simp only [←rotate_mul, ←mul_assoc, mul_inv_cancel_right]

theorem physical_isometry (φ : Vec3) (hφ : enorm φ<2*π) (R S : SO3) (x : Vec3) :
    physicalNorm φ (flow φ R S x)=physicalNorm φ x := by
  unfold physicalNorm
  rw [reconstruction φ hφ R S x, rotate_enorm, rotate_enorm]

theorem inverse_bound (φ x : Vec3) (hφ : enorm φ≤1) :
    enorm (Jacobian.inverseAt φ x)≤(4/3:ℝ)*enorm x := by
  by_cases hz : φ=0
  · simp only [hz, Jacobian.inverseAt]
    simp
    nlinarith [enorm_nonneg x]
  have hp : 0<enorm φ := lt_of_le_of_ne (enorm_nonneg _) (Ne.symm
    (fun h => hz ((enorm_eq_zero_iff _).mp h)))
  have hchart : enorm φ<2*π := by linarith [pi_gt_three]
  rw [Jacobian.inverseAt_eq φ _ hp]
  exact (Jacobian.leftInv_bound (Jacobian.unitAxis φ) x
    (Jacobian.unitAxis_unit φ hp) (enorm φ) hp hchart).trans
    (mul_le_mul_of_nonneg_right (OrbitalNearAffine.inverse_gain hp hφ) (enorm_nonneg x))

/-- Pure transport cannot create unbounded growth, regardless of spin rate
or number of revolutions. This constant is uniform over the one-radian ball. -/
theorem uniform_bound (φ : Vec3) (hφ : enorm φ≤1) (R S : SO3) (x : Vec3) :
    enorm (flow φ R S x)≤(4/3:ℝ)*enorm x := by
  have hchart : enorm φ<2*π := by linarith [pi_gt_three]
  have hb := inverse_bound φ (rotate R⁻¹ (rotate S (Jacobian.leftAt φ x))) hφ
  rw [rotate_enorm, rotate_enorm] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left (leftAt_nonexpansive φ x hchart)
    (by norm_num))

/-- Angle-resolved conditioning, sharper than the uniform one-radian bound.
The zero-angle flow is a rotation and is covered by `physical_isometry`. -/
theorem angle_bound (φ : Vec3) (hpos : 0<enorm φ) (hφ : enorm φ<2*π)
    (R S : SO3) (x : Vec3) :
    enorm (flow φ R S x)≤((enorm φ/2)/sin (enorm φ/2))*enorm x := by
  unfold flow
  rw [Jacobian.inverseAt_eq φ _ hpos]
  have hb := Jacobian.leftInv_bound (Jacobian.unitAxis φ)
    (rotate R⁻¹ (rotate S (Jacobian.leftAt φ x)))
    (Jacobian.unitAxis_unit φ hpos) (enorm φ) hpos hφ
  rw [rotate_enorm, rotate_enorm] at hb
  have hs : 0<sin (enorm φ/2) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  exact hb.trans (mul_le_mul_of_nonneg_left (leftAt_nonexpansive φ x hφ)
    (div_nonneg (by linarith) hs.le))

/-- The closed flow solves the nonautonomous conjugated transport ODE.
The rate can vary without any Magnus truncation. -/
theorem derivative (φ : Vec3) (hφ : enorm φ<2*π) (S : SO3) (x : Vec3)
    {R : ℝ → SO3} {ω : Vec3} {t : ℝ}
    (hR : HasDerivAt (fun s => (R s).val) ((R t).val*skew ω) t) :
    HasDerivAt (fun s => flow φ (R s) S x)
      (-transport φ ω (flow φ (R t) S x)) t := by
  have hd := RotationKinematics.inverse_rotate_derivative hR
    (hasDerivAt_const t (rotate S (Jacobian.leftAt φ x)))
  have hi := inverseAt_fixed_derivative φ hd
  convert hi using 1
  rw [transport, reconstruction φ hφ (R t) S x]
  simp only [rotate_zero, zero_sub]
  simp only [Jacobian.inverseAt, map_neg]
  module

end GNC.MountingTransportFlow
