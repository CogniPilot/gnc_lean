import GNC.Magnus.FohParameterSensitivity
import GNC.Lie.RotationKinematics
import GNC.Lie.CayleyChart

/-! The genuine parameter derivative of an SO(3) ODE equals an integrated
rotated vector after right trivialization. Constant and linear rate
perturbations therefore recover the zeroth and first rotation moments. -/
noncomputable section
open Matrix Set
open scoped Matrix Matrix.Norms.Operator
namespace GNC.Magnus

def fohRotationSensitivity (R : ℝ → SO3) (b : ℝ → Vec3) (t : ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  skew (∫ s in (0 : ℝ)..t, rotate (R s) (b s)) * (R t).val

theorem foh_rotationSensitivity_derivative
    (R : ℝ → SO3) (w b : ℝ → Vec3)
    (hR : ∀ t, HasDerivAt (fun s => (R s).val) ((R t).val * skew (w t)) t)
    (hb : Continuous b) (t : ℝ) :
    HasDerivAt (fohRotationSensitivity R b)
      (fohRotationSensitivity R b t * skew (w t) + (R t).val * skew (b t)) t := by
  have hcR : Continuous (fun t => (R t).val) :=
    continuous_iff_continuousAt.mpr (fun t => (hR t).continuousAt)
  have hc : Continuous (fun t => rotate (R t) (b t)) := hcR.matrix_mulVec hb
  have hp := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have hs := Cayley.skewLinear.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hp
  change HasDerivAt (fun z => skew (∫ s in (0 : ℝ)..z, rotate (R s) (b s)))
    (skew (rotate (R t) (b t))) t at hs
  convert hs.mul (hR t) using 1
  simp only [fohRotationSensitivity, skew_rotate, mul_assoc]
  exact add_comm _ _

/-- This theorem differentiates the actual parameterized rotation family.
Its only derivative hypothesis is the original time ODE. -/
theorem foh_rotation_parameter_hasDerivAt
    (R : ℝ → ℝ → SO3) (w b : ℝ → Vec3) (hw : Continuous w) (hb : Continuous b)
    (hR : ∀ q t, HasDerivAt (fun s => (R q s).val)
      ((R q t).val * skew (w t + q • b t)) t)
    (hR0 : ∀ q, R q 0 = 1) {T : ℝ} (hT : 0 ≤ T) :
    HasDerivAt (fun q => (R q T).val)
      (skew (∫ t in (0 : ℝ)..T, rotate (R 0 t) (b t)) * (R 0 T).val) 0 := by
  have hu : ∀ t, HasDerivAt (fun s => (R 0 s).val) ((R 0 t).val * skew (w t)) t := by
    intro t
    simpa only [zero_smul, add_zero] using hR 0 t
  exact foh_parameter_hasDerivAt (fun t => skew (w t)) (fun t => skew (b t))
    (fun q t => (R q t).val) (fohRotationSensitivity (R 0) b) hT
    (Cayley.skewLinear.toContinuousLinearMap.continuous.comp hw).continuousOn
    (Cayley.skewLinear.toContinuousLinearMap.continuous.comp hb).continuousOn
    (fun q t _ => by simpa only [skew_add, skew_smul] using hR q t)
    (fun q => by simp [hR0]) (by
      simp only [fohRotationSensitivity, intervalIntegral.integral_same]
      change Cayley.skewLinear 0 * _ = 0
      rw [map_zero, zero_mul])
    (fun t _ => foh_rotationSensitivity_derivative (R 0) w b hu hb t)

/-- The right-trivialized parameter derivative is the skew matrix of the
integrated rotated perturbation, an exact SO(3) identity. -/
theorem foh_rotation_trivialized_parameter_hasDerivAt
    (R : ℝ → ℝ → SO3) (w b : ℝ → Vec3) (hw : Continuous w) (hb : Continuous b)
    (hR : ∀ q t, HasDerivAt (fun s => (R q s).val)
      ((R q t).val * skew (w t + q • b t)) t)
    (hR0 : ∀ q, R q 0 = 1) {T : ℝ} (hT : 0 ≤ T) :
    HasDerivAt (fun q => (R q T).val * ((R 0 T)⁻¹).val)
      (skew (∫ t in (0 : ℝ)..T, rotate (R 0 t) (b t))) 0 := by
  have h := (foh_rotation_parameter_hasDerivAt R w b hw hb hR hR0 hT).mul_const
    ((R 0 T)⁻¹).val
  convert h using 1
  rw [mul_assoc]
  have hi : (R 0 T).val * ((R 0 T)⁻¹).val = 1 := by
    change ((R 0 T) * (R 0 T)⁻¹).val = 1
    simp
  rw [hi, mul_one]

/-- Perturbing the constant FOH angular rate recovers its zeroth rotation
moment as the right-trivialized parameter derivative. -/
theorem foh_constant_rate_sensitivity
    (R : ℝ → ℝ → SO3) (w s x : Vec3)
    (hR : ∀ q t, HasDerivAt (fun u => (R q u).val)
      ((R q t).val * skew (w + t • s + q • x)) t)
    (hR0 : ∀ q, R q 0 = 1) {T : ℝ} (hT : 0 ≤ T) :
    HasDerivAt (fun q => (R q T).val * ((R 0 T)⁻¹).val)
      (skew (∫ t in (0 : ℝ)..T, rotate (R 0 t) x)) 0 :=
  foh_rotation_trivialized_parameter_hasDerivAt R (fun t => w + t • s) (fun _ => x)
    (continuous_const.add (continuous_id.smul continuous_const)) continuous_const hR hR0 hT

/-- Perturbing the FOH angular acceleration recovers its first rotation
moment; no differentiation under an assumed solution map is used. -/
theorem foh_linear_rate_sensitivity
    (R : ℝ → ℝ → SO3) (w s x : Vec3)
    (hR : ∀ q t, HasDerivAt (fun u => (R q u).val)
      ((R q t).val * skew (w + t • (s + q • x))) t)
    (hR0 : ∀ q, R q 0 = 1) {T : ℝ} (hT : 0 ≤ T) :
    HasDerivAt (fun q => (R q T).val * ((R 0 T)⁻¹).val)
      (skew (∫ t in (0 : ℝ)..T, t • rotate (R 0 t) x)) 0 := by
  have hr : ∀ q t, HasDerivAt (fun u => (R q u).val)
      ((R q t).val * skew ((w + t • s) + q • (t • x))) t := by
    intro q t
    have he : w + t • (s + q • x) = (w + t • s) + q • (t • x) := by module
    simpa only [he] using hR q t
  have h := foh_rotation_trivialized_parameter_hasDerivAt R
    (fun t => w + t • s) (fun t => t • x)
    (continuous_const.add (continuous_id.smul continuous_const))
    (continuous_id.smul continuous_const) hr hR0 hT
  simpa only [rotate, Matrix.mulVec_smul] using h

end GNC.Magnus
