import GNC.Dynamics.LieErrorReconstruction
import GNC.Dynamics.OrbitalSymmetry
import GNC.Dynamics.GravityRemainderBall

/-! Center a correlated orbit/attitude family at a rotation, before applying
a local Cartesian or Lie approximation. For the arithmetic midpoint of a
vector and its full rotation, the half rotation leaves a quadratic, rather
than linear, angular displacement. The full inverse-square gravity Taylor
remainder at that centered displacement is therefore fourth order in angle.

These are pointwise geometry and gravity statements, not a finite-burn error
certificate or a claim that an arbitrary initial population has this form.
The same center is available to a Cartesian response method.
-/
noncomputable section
namespace GNC.RotationCenteredError
open Matrix Real
open scoped Matrix Matrix.Norms.Operator

def midpoint (Q : SO3) (q : Vec3) : Vec3 := (1/2:ℝ) • (q+rotate Q q)

theorem midpoint_identity (S : SO3) (q : Vec3) :
    midpoint (S*S) q-rotate S q =
      (1/2:ℝ) • (rotate S (rotate S q-q)-(rotate S q-q)) := by
  rw [midpoint, rotate_mul, rotate_sub]
  module

theorem rotation_difference_bound (φ q : Vec3) (hφ : enorm φ<2*π) :
    enorm (rotate (rotationExp φ) q-q) ≤ enorm φ*enorm q := by
  rw [←leftAt_cross_rotation]
  exact (leftAt_nonexpansive φ _ hφ).trans (cross_enorm_le φ q)

theorem half_square (φ : Vec3) :
    rotationExp ((1/2:ℝ) • φ)*rotationExp ((1/2:ℝ) • φ)=rotationExp φ := by
  apply Subtype.ext
  change NormedSpace.exp (skew ((1/2:ℝ) • φ))*NormedSpace.exp (skew ((1/2:ℝ) • φ)) = _
  rw [←NormedSpace.exp_add_of_commute (Commute.refl _),skew_smul]
  congr 1
  module

def centered (φ q : Vec3) : Vec3 :=
  rotate (rotationExp ((1/2:ℝ) • φ))⁻¹ (midpoint (rotationExp φ) q)-q

/-- The midpoint's local initial displacement is linear in entries of the
half rotation and its transpose. This is the exact input reduction used by
the centered Cartesian comparator, before its numerical coefficients exist. -/
theorem centered_symmetrized (φ q : Vec3) :
    centered φ q = (1/2:ℝ) •
      (rotate (rotationExp ((1/2:ℝ) • φ))⁻¹ q+
       rotate (rotationExp ((1/2:ℝ) • φ)) q)-q := by
  rw [centered,midpoint,rotate_smul,rotate_add,←half_square φ,←rotate_mul,
    inv_mul_cancel_left]

theorem centered_norm (φ q : Vec3) :
    enorm (centered φ q)=
      enorm (midpoint (rotationExp φ) q-rotate (rotationExp ((1/2:ℝ) • φ)) q) := by
  rw [centered]
  have he : rotate (rotationExp ((1/2:ℝ) • φ))⁻¹
      (midpoint (rotationExp φ) q-rotate (rotationExp ((1/2:ℝ) • φ)) q)=
      rotate (rotationExp ((1/2:ℝ) • φ))⁻¹ (midpoint (rotationExp φ) q)-q := by
    rw [rotate_sub,←rotate_mul,inv_mul_cancel,rotate_one]
  rw [←he,rotate_enorm]

/-- A global three-axis bound, including zero angle. The constant 1/8
comes from averaging and two half-angle rotation differences. -/
theorem centered_bound (φ q : Vec3) (hφ : enorm φ<4*π) :
    enorm (centered φ q) ≤ (enorm φ)^2/8*enorm q := by
  have hn : enorm ((1/2:ℝ) • φ)=enorm φ/2 := by
    rw [enorm_smul]
    norm_num
    ring
  have hh : enorm ((1/2:ℝ) • φ)<2*π := by rw [hn]; linarith
  rw [centered_norm,←half_square φ,midpoint_identity,enorm_smul]
  have h1 := rotation_difference_bound ((1/2:ℝ) • φ) q hh
  have h2 := rotation_difference_bound ((1/2:ℝ) • φ)
    (rotate (rotationExp ((1/2:ℝ) • φ)) q-q) hh
  rw [hn] at h1 h2
  rw [rotate_sub] at h2
  norm_num
  nlinarith [enorm_nonneg φ,enorm_nonneg q,
    mul_le_mul_of_nonneg_left h1 (div_nonneg (enorm_nonneg φ) (by norm_num : (0:ℝ)≤2))]

/-- In the centered axes the full-rotation thrust becomes a half rotation.
This transformation is exact; it does not discard thrust misalignment. -/
theorem centered_thrust (φ b : Vec3) :
    rotate (rotationExp ((1/2:ℝ) • φ))⁻¹ (rotate (rotationExp φ) b)=
      rotate (rotationExp ((1/2:ℝ) • φ)) b := by
  rw [←half_square φ,←rotate_mul,inv_mul_cancel_left]

theorem centered_thrust_bound (φ b : Vec3) (hφ : enorm φ<4*π) :
    enorm (rotate (rotationExp ((1/2:ℝ) • φ))⁻¹ (rotate (rotationExp φ) b)-b)
      ≤ enorm φ/2*enorm b := by
  rw [centered_thrust]
  have hn : enorm ((1/2:ℝ) • φ)=enorm φ/2 := by
    rw [enorm_smul]
    norm_num
    ring
  simpa only [hn] using rotation_difference_bound ((1/2:ℝ) • φ) b (by rw [hn]; linarith)

/-- The centered full-gravity Taylor remainder has a quartic angular
budget. The positive radius floor is explicit. This is a pointwise bound,
not a bound on an unknown propagated tube. -/
theorem centered_gravity_remainder (μ : ℝ) (hμ : 0≤μ) (φ q : Vec3)
    (hφ : enorm φ<4*π) (r : ℝ) (hr : 0<r)
    (hq : r+(enorm φ)^2/8*enorm q≤enorm q) :
    let x : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 q
    let d : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 (centered φ q)
    ‖Gravity.field μ (x+d)-Gravity.field μ x-Gravity.gradient μ x d‖ ≤
      (3*μ/r^4)*((enorm φ)^4/64)*(enorm q)^2 := by
  dsimp only
  have hd := centered_bound φ q hφ
  have hD : 0≤(enorm φ)^2/8*enorm q :=
    mul_nonneg (div_nonneg (sq_nonneg _) (by norm_num)) (enorm_nonneg q)
  have hb := Gravity.remainder_quadratic μ hμ
    (WithLp.toLp 2 q : EuclideanSpace ℝ (Fin 3))
    (WithLp.toLp 2 (centered φ q) : EuclideanSpace ℝ (Fin 3))
    (r := r+(enorm φ)^2/8*enorm q) (D := (enorm φ)^2/8*enorm q)
    (by linarith) hq hd
  simp only [add_sub_cancel_right] at hb
  have hs := pow_le_pow_left₀ (enorm_nonneg (centered φ q)) hd 2
  have ht := mul_le_mul_of_nonneg_left hs (by positivity : 0≤3*μ/r^4)
  change _ ≤ (3*μ/r^4)*((enorm φ)^4/64)*(enorm q)^2
  apply hb.trans
  convert ht using 1 <;> dsimp [enorm] <;> ring

end GNC.RotationCenteredError
