import GNC.Magnus.FohRotationSensitivity

/-! An exact reusable bias-sensitivity identity for any continuous angular rate.

The spatial gyro-bias sensitivity and velocity accelerometer-bias sensitivity
use the same integrated rotation. The actual parameter derivatives are derived
from the original time ODEs. No held-input assumption or supplied Jacobian is
needed. This does not identify a derivative of a projected finite approximation.
-/
noncomputable section
namespace GNC.Preintegration
open Matrix
open scoped Matrix Matrix.Norms.Operator

/-- The common integrated-rotation column. -/
def biasRotationMoment (R : ℝ → SO3) (b : Vec3) (T : ℝ) : Vec3 :=
  ∫ t in (0 : ℝ)..T, rotate (R t) b

theorem biasRotationMoment_derivative (R : ℝ → SO3)
    (hR : Continuous (fun t => (R t).val)) (b : Vec3) (T : ℝ) :
    HasDerivAt (biasRotationMoment R b) (rotate (R T) b) T := by
  have hc : Continuous (fun t => rotate (R t) b) := hR.matrix_mulVec continuous_const
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 T)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

/-- Identify every accelerometer-bias trajectory from its physical time ODE. -/
theorem accel_bias_velocity_response (R : ℝ → SO3)
    (hR : Continuous (fun t => (R t).val))
    (a : ℝ → Vec3) (b : Vec3) (V : ℝ → ℝ → Vec3)
    (hV : ∀ q t, HasDerivAt (V q) (rotate (R t) (a t-q • b)) t)
    (hV0 : ∀ q, V q 0 = 0) (q T : ℝ) :
    V q T = V 0 T-q • biasRotationMoment R b T := by
  let H : ℝ → Vec3 := fun t => V q t-V 0 t+q • biasRotationMoment R b t
  have hd (t : ℝ) : HasDerivAt H 0 t := by
    have hi := biasRotationMoment_derivative R hR b t
    convert ((hV q t).sub (hV 0 t)).add (hi.const_smul q) using 1
    simp [rotate, Matrix.mulVec_sub, Matrix.mulVec_smul]
  have hz := is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt)
    (fun t => (hd t).deriv) T 0
  have he : V q T-V 0 T+q • biasRotationMoment R b T = 0 := by
    simpa [H, hV0, biasRotationMoment] using hz
  calc
    V q T = (V q T-V 0 T+q • biasRotationMoment R b T)+
        (V 0 T-q • biasRotationMoment R b T) := by abel
    _ = V 0 T-q • biasRotationMoment R b T := by rw [he, zero_add]

/-- This is a derivative of the actual velocity family, not a proposed column. -/
theorem accel_bias_velocity_hasDerivAt (R : ℝ → SO3)
    (hR : Continuous (fun t => (R t).val))
    (a : ℝ → Vec3) (b : Vec3) (V : ℝ → ℝ → Vec3)
    (hV : ∀ q t, HasDerivAt (V q) (rotate (R t) (a t-q • b)) t)
    (hV0 : ∀ q, V q 0 = 0) (T : ℝ) :
    HasDerivAt (fun q => V q T) (-biasRotationMoment R b T) 0 := by
  have he : (fun q => V q T) =
      (fun q => V 0 T-q • biasRotationMoment R b T) := by
    funext q
    exact accel_bias_velocity_response R hR a b V hV hV0 q T
  rw [he]
  simpa using (hasDerivAt_const (0 : ℝ) (V 0 T)).sub
    ((hasDerivAt_id (0 : ℝ)).smul_const (biasRotationMoment R b T))

/-- The genuine spatial gyro-bias derivative uses that same moment. -/
theorem gyro_bias_spatial_hasDerivAt (R : ℝ → ℝ → SO3)
    (w : ℝ → Vec3) (hw : Continuous w) (b : Vec3)
    (hR : ∀ q t, HasDerivAt (fun s => (R q s).val)
      ((R q t).val * skew (w t-q • b)) t)
    (hR0 : ∀ q, R q 0 = 1) {T : ℝ} (hT : 0 ≤ T) :
    HasDerivAt (fun q => (R q T).val * ((R 0 T)⁻¹).val)
      (skew (-biasRotationMoment (R 0) b T)) 0 := by
  have hr : ∀ q t, HasDerivAt (fun s => (R q s).val)
      ((R q t).val * skew (w t+q • (fun _ : ℝ => -b) t)) t := by
    intro q t
    simpa only [smul_neg, sub_eq_add_neg] using hR q t
  have h := Magnus.foh_rotation_trivialized_parameter_hasDerivAt R w
    (fun _ => -b) hw continuous_const hr hR0 hT
  simpa only [rotate_neg, intervalIntegral.integral_neg, biasRotationMoment] using h

/-- Exact sharing rule: spatial attitude and velocity sensitivities coincide
for the same constant body-axis bias direction. Their physical units differ. -/
theorem gyro_accel_bias_spatial_identity (R : ℝ → ℝ → SO3)
    (w a : ℝ → Vec3) (hw : Continuous w) (b : Vec3) (V : ℝ → ℝ → Vec3)
    (hR : ∀ q t, HasDerivAt (fun s => (R q s).val)
      ((R q t).val * skew (w t-q • b)) t)
    (hR0 : ∀ q, R q 0 = 1)
    (hV : ∀ q t, HasDerivAt (V q) (rotate (R 0 t) (a t-q • b)) t)
    (hV0 : ∀ q, V q 0 = 0) {T : ℝ} (hT : 0 ≤ T) :
    deriv (fun q => (R q T).val * ((R 0 T)⁻¹).val) 0 =
      skew (deriv (fun q => V q T) 0) := by
  have hc : Continuous (fun t => (R 0 t).val) :=
    continuous_iff_continuousAt.mpr (fun t => (hR 0 t).continuousAt)
  rw [(gyro_bias_spatial_hasDerivAt R w hw b hR hR0 hT).deriv,
    (accel_bias_velocity_hasDerivAt (R 0) hc a b V hV hV0 T).deriv]

end GNC.Preintegration
