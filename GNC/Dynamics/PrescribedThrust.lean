import GNC.Control.DecoupledPlanning
import GNC.Control.ConstantBurn
import GNC.Lie.SpatialPointing

/-! Exact scope of attitude elimination from translation.

An inertially constant pointing command need not be accurately known. The
translation field depends on the actual inertial acceleration `rotate R a`.
Equality of that acceleration, not zero angular rate, permits elimination of
attitude. The field `g` can retain nonlinear gravity without approximation.

The endpoint counterexample uses a double integrator explicitly; it is not an
inverse-square rendezvous certificate. It also describes the propulsive part
of the velocity and position moments before adding differential gravity.
-/
noncomputable section
set_option autoImplicit false
namespace GNC.PrescribedThrust
open Set Matrix
open scoped Matrix.Norms.Operator

abbrev Translation := Vec3 × Vec3

def bodyField (g : ℝ → Vec3 → Vec3) (t : ℝ) (z : Translation)
    (R : SO3) (a : Vec3) : Translation :=
  (z.2, g t z.1 + rotate R a)

def inertialField (g : ℝ → Vec3 → Vec3) (t : ℝ) (z : Translation)
    (u : Vec3) : Translation :=
  (z.2, g t z.1 + u)

/-- At the same translational state, the exact criterion is equality of
delivered inertial acceleration. Attitude itself may differ, for example by
a rotation about the thrust axis. -/
theorem field_eq_iff (g : ℝ → Vec3 → Vec3) (t : ℝ) (z : Translation)
    (R S : SO3) (a b : Vec3) :
    bodyField g t z R a = bodyField g t z S b ↔ rotate R a = rotate S b := by
  simp [bodyField]

/-- An ideal body command realizing a prescribed inertial acceleration.
This identity alone imposes no actuator or attitude-estimation guarantees. -/
theorem inertial_realization (g : ℝ → Vec3 → Vec3) (t : ℝ) (z : Translation)
    (R : SO3) (u : Vec3) :
    bodyField g t z R (R.valᵀ *ᵥ u) = inertialField g t z u := by
  simp only [bodyField, inertialField, (DecoupledPlanning.inertial_command_realization R u).1]

/-- The realized physical field satisfies the library's exact decoupling
predicate, so its existing projection and uniqueness results apply. -/
theorem realized_field_decoupled (g : ℝ → Vec3 → Vec3) :
    DecoupledPlanning.decoupled
      (fun t z R u => bodyField g t z R (R.valᵀ *ᵥ u)) (inertialField g) :=
  inertial_realization g

/-- Under a common actual inertial thrust history, nonlinear gravity is the
only remaining acceleration difference. No gravity linearization is used. -/
theorem same_thrust_error (g : ℝ → Vec3 → Vec3) (t : ℝ) (p q : Vec3)
    (R S : SO3) (a b : Vec3) (hu : rotate R a = rotate S b) :
    (g t p + rotate R a) - (g t q + rotate S b) = g t p - g t q := by
  rw [hu]
  abel

/-- Equal delivered thrust histories and initial translations give identical
translations on a common Lipschitz region. The attitude histories and body
commands may differ. Uniqueness is supplied by released mathlib. -/
theorem trajectory_eq_of_same_thrust
    (g : ℝ → Vec3 → Vec3) (R S : ℝ → SO3) (a b u : ℝ → Vec3)
    (x y : ℝ → Translation) (region : ℝ → Set Translation)
    {t₀ t₁ : ℝ} (K : NNReal)
    (hR : ∀ t ∈ Ico t₀ t₁, rotate (R t) (a t) = u t)
    (hS : ∀ t ∈ Ico t₀ t₁, rotate (S t) (b t) = u t)
    (hlip : ∀ t ∈ Ico t₀ t₁,
      LipschitzOnWith K (fun z => inertialField g t z (u t)) (region t))
    (hx : ContinuousOn x (Icc t₀ t₁)) (hy : ContinuousOn y (Icc t₀ t₁))
    (hdx : ∀ t ∈ Ico t₀ t₁,
      HasDerivWithinAt x (bodyField g t (x t) (R t) (a t)) (Ici t) t)
    (hdy : ∀ t ∈ Ico t₀ t₁,
      HasDerivWithinAt y (bodyField g t (y t) (S t) (b t)) (Ici t) t)
    (hrx : ∀ t ∈ Ico t₀ t₁, x t ∈ region t)
    (hry : ∀ t ∈ Ico t₀ t₁, y t ∈ region t) (hinit : x t₀ = y t₀) :
    EqOn x y (Icc t₀ t₁) := by
  apply ODE_solution_unique_of_mem_Icc_right hlip hx ?_ hrx hy ?_ hry hinit
  · intro t ht
    simpa only [bodyField, inertialField, hR t ht] using hdx t ht
  · intro t ht
    simpa only [bodyField, inertialField, hS t ht] using hdy t ht

/-- Every constant attitude has zero body angular rate, whether or not its
thrust direction agrees with the nominal. -/
theorem fixed_attitude_rate (R : SO3) (t : ℝ) :
    HasDerivAt (fun _ : ℝ => R.val) (R.val * skew (0 : Vec3)) t := by
  simpa [skew_zero] using hasDerivAt_const t R.val

/-- Exact constant-acceleration endpoint, connected to actual derivatives.
For an error trajectory, `u` must be the complete acceleration difference. -/
theorem constant_acceleration_endpoint (p v : ℝ → Vec3) (u : Vec3)
    {T : ℝ} (hT : 0 ≤ T)
    (hp : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt p (v t) t)
    (hv : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt v u t) :
    v T - v 0 = T • u ∧ p T - p 0 - T • v 0 = (T^2/2) • u := by
  obtain ⟨hvel, hpos⟩ :=
    ConstantBurn.double_integrator_endpoint p v (fun _ => u) continuous_const hT hp hv
  simp only [intervalIntegral.integral_const, sub_zero] at hvel
  refine ⟨hvel, ?_⟩
  rw [hpos, ConstantBurn.position_decomposition _ continuous_const,
    ConstantBurn.centered_constant, sub_zero, intervalIntegral.integral_const, sub_zero,
    smul_smul]
  congr 1
  ring

/-- Fixed out-of-plane pointing produces a nonzero normal impulse, even with
zero angular rate. This is also the exact total error for a double integrator
with zero initial error; differential orbital gravity is not discarded silently. -/
theorem fixed_pointing_normal_endpoint (p v : ℝ → Vec3) (α β : ℝ)
    {T : ℝ} (hT : 0 ≤ T) (hp₀ : p 0 = 0) (hv₀ : v 0 = 0)
    (hp : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt p (v t) t)
    (hv : ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivAt v (α • (SpatialPointing.direction 0 β - ![1,0,0])) t) :
    (v T) 2 = T * α * Real.sin β ∧
      (p T) 2 = T^2/2 * α * Real.sin β := by
  obtain ⟨hvel, hpos⟩ := constant_acceleration_endpoint p v
    (α • (SpatialPointing.direction 0 β - ![1,0,0])) hT hp hv
  simp only [hp₀, hv₀, sub_zero, smul_zero] at hvel hpos
  rw [hvel, hpos, SpatialPointing.direction_components]
  constructor <;> change _ * (α * (Real.sin β - 0)) = _ <;> ring

/-- The normal error can be nonzero for arbitrarily small nonzero elevation;
zero angular rate is not a sufficient decoupling condition. -/
theorem fixed_pointing_normal_ne_zero {T α β : ℝ}
    (hT : T ≠ 0) (hα : α ≠ 0) (hβ : Real.sin β ≠ 0) :
    T * α * Real.sin β ≠ 0 := mul_ne_zero (mul_ne_zero hT hα) hβ

namespace RotatingFrame

/-- The pointing-induced force difference expressed in the reference frame.
Both directions are fixed in that frame; the example is planar but uses SO(3). -/
def pointingError (α θ : ℝ) : Vec3 :=
  α • (SpatialPointing.direction θ 0 - ![1,0,0])

/-- Error introduced by freezing this reference-frame force difference at
its initial inertial direction instead of retaining the known phase rotation. -/
def frozenDefect (α θ φ : ℝ) : Vec3 :=
  rotate (AxisRotation.zRotation φ) (pointingError α θ) - pointingError α θ

/-- This is the physical acceleration error for two RTN-fixed directions,
before adding the difference of their gravitational accelerations. -/
theorem physical_force_error (α θ φ : ℝ) :
    rotate (AxisRotation.zRotation φ) (α • SpatialPointing.direction θ 0) -
      rotate (AxisRotation.zRotation φ) (α • ![1,0,0]) =
        rotate (AxisRotation.zRotation φ) (pointingError α θ) := by
  rw [pointingError, smul_sub, rotate_sub]

theorem planar_rotation_defect_sq (φ : ℝ) (q : Vec3) (hq : q 2 = 0) :
    enorm (rotate (AxisRotation.zRotation φ) q - q)^2 =
      2 * (1 - Real.cos φ) * enorm q^2 := by
  simp [enorm_sq, lengthSq, rotate, AxisRotation.zRotation, AxisRotation.zMatrix,
    dotProduct, Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail, hq]
  linear_combination (q 0^2 + q 1^2) * (Real.sin_sq_add_cos_sq φ)

/-- A precise additional error of freezing RTN rotation. This compares
representations of the forcing, not complete orbital predictors or CPU costs.
A Cartesian algorithm retaining the same rotation has no such defect either. -/
theorem frozen_defect_sq (α θ φ : ℝ) :
    enorm (frozenDefect α θ φ)^2 =
      4 * α^2 * (1 - Real.cos θ) * (1 - Real.cos φ) := by
  have hp : (pointingError α θ) 2 = 0 := by
    simp [pointingError, SpatialPointing.direction_components]
  rw [frozenDefect, planar_rotation_defect_sq φ _ hp, pointingError, enorm_smul,
    mul_pow, sq_abs, SpatialPointing.force_error_sq]
  simp only [Real.cos_zero, mul_one]
  ring

/-- A fixed inertial frame has exactly zero freezing defect, even if the
fixed pointing error itself is nonzero. -/
theorem inertial_frozen_defect (α θ : ℝ) : frozenDefect α θ 0 = 0 := by
  simp [frozenDefect]

/-- A nontrivial reference rotation creates a strictly positive forcing
defect for this comparator and nontrivial planar pointing error. -/
theorem frozen_defect_ne_zero {α θ φ : ℝ} (hα : α ≠ 0)
    (hθ : Real.cos θ < 1) (hφ : Real.cos φ < 1) : frozenDefect α θ φ ≠ 0 := by
  intro hzero
  have h := frozen_defect_sq α θ φ
  have hz : enorm (0 : Vec3)^2 = 0 := by simp [enorm_sq, lengthSq]
  rw [hzero, hz] at h
  have : 0 < 4 * α^2 * (1 - Real.cos θ) * (1 - Real.cos φ) :=
    mul_pos (mul_pos (mul_pos (by norm_num) (sq_pos_of_ne_zero hα))
      (sub_pos.mpr hθ)) (sub_pos.mpr hφ)
  linarith

end RotatingFrame

end GNC.PrescribedThrust
