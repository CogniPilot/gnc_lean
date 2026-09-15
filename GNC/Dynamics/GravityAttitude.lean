import GNC.Lie.Jacobian
import GNC.Dynamics.GravityField
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic

/-! The attitude/gravity commutators in Appendix B and Theorem 1. -/
noncomputable section
open Matrix Real
open scoped Matrix
namespace GNC.Gravity

/-- The body-frame gravity gradient, with λ=μ/r³ and a radial unit vector r. -/
def radialMap (l : ℝ) (r v : Vec3) : Vec3 := l • ((3*(r ⬝ᵥ v)) • r - v)

def commutator₁ (l : ℝ) (r k v : Vec3) : Vec3 :=
  radialMap l r (k ⨯₃ v) - k ⨯₃ radialMap l r v

def commutator₂ (l : ℝ) (r k v : Vec3) : Vec3 :=
  radialMap l r (k ⨯₃ (k ⨯₃ v)) - k ⨯₃ (k ⨯₃ radialMap l r v)

theorem commutator₁_formula (l : ℝ) (r k v : Vec3) :
    commutator₁ l r k v = (-3*l) •
      (((k ⨯₃ r) ⬝ᵥ v) • r + (r ⬝ᵥ v) • (k ⨯₃ r)) := by
  ext i; fin_cases i <;>
    simp [commutator₁, radialMap, cross_apply, dotProduct, Fin.sum_univ_succ,
      Matrix.vecHead, Matrix.vecTail] <;> ring

theorem commutator₂_formula (l : ℝ) (r k v : Vec3) :
    commutator₂ l r k v = (3*l*(k ⬝ᵥ r)) •
      ((k ⬝ᵥ v) • r - (r ⬝ᵥ v) • k) := by
  simp only [commutator₂, cross_cross_eq_smul_sub_smul']
  ext i
  simp [radialMap, dotProduct_comm r k]
  ring

theorem commutator₁_bound (l : ℝ) (hl : 0 ≤ l) (r k v : Vec3) (hr : r ⬝ᵥ r = 1) :
    enorm (commutator₁ l r k v) ≤ 3*l*enorm (k ⨯₃ r)*enorm v := by
  have horth : r ⬝ᵥ (k ⨯₃ r) = 0 := dot_cross_self k r
  rw [commutator₁_formula, enorm_smul, abs_mul, abs_of_nonneg hl]
  norm_num
  have h := mul_le_mul_of_nonneg_left (orthogonal_pair_bound r (k ⨯₃ r) v hr horth)
    (show 0 ≤ 3*l by positivity)
  simpa only [mul_assoc] using h

theorem commutator₂_bound (l : ℝ) (hl : 0 ≤ l) (r k v : Vec3) :
    enorm (commutator₂ l r k v) ≤ 3*l*|k ⬝ᵥ r| * enorm (k ⨯₃ r)*enorm v := by
  rw [commutator₂_formula, ← cross_cross_eq_smul_sub_smul, enorm_smul]
  have ha : |3*l*(k ⬝ᵥ r)| = 3*l*|k ⬝ᵥ r| := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
  rw [ha]
  have h := mul_le_mul_of_nonneg_left (cross_enorm_le (k ⨯₃ r) v)
    (show 0 ≤ 3*l*|k ⬝ᵥ r| by positivity)
  simpa only [mul_assoc] using h

def separationAngle (k r : Vec3) : ℝ :=
  InnerProductGeometry.angle (WithLp.toLp 2 k : Jacobian.E3) (WithLp.toLp 2 r)

theorem inner_toLp (u v : Vec3) :
    inner ℝ (WithLp.toLp 2 u : Jacobian.E3) (WithLp.toLp 2 v) = u ⬝ᵥ v := by
  change (∑ i, v i * u i) = ∑ i, u i * v i
  simp only [mul_comm]

theorem unit_enorm (k : Vec3) (hk : k ⬝ᵥ k = 1) : enorm k = 1 := by
  have h : enorm k ^ 2 = 1 := by rw [enorm_sq, ← dot_self_lengthSq, hk]
  nlinarith [enorm_nonneg k]

theorem separationAngle_cos (k r : Vec3) (hk : k ⬝ᵥ k = 1) (hr : r ⬝ᵥ r = 1) :
    cos (separationAngle k r) = k ⬝ᵥ r := by
  rw [separationAngle, InnerProductGeometry.cos_angle, inner_toLp]
  change (k ⬝ᵥ r)/(enorm k * enorm r) = _
  rw [unit_enorm k hk, unit_enorm r hr]; ring

theorem separationAngle_sin (k r : Vec3) (hk : k ⬝ᵥ k = 1) (hr : r ⬝ᵥ r = 1) :
    sin (separationAngle k r) = enorm (k ⨯₃ r) := by
  have hc := separationAngle_cos k r hk hr
  have hn := InnerProductGeometry.sin_angle_nonneg
    (WithLp.toLp 2 k : Jacobian.E3) (WithLp.toLp 2 r)
  have hs := sin_sq_add_cos_sq (separationAngle k r)
  have he : enorm (k ⨯₃ r)^2 = 1 - (k ⬝ᵥ r)^2 := by
    rw [enorm_sq, Axis.cross_lengthSq k r hk, ← dot_self_lengthSq, hr]
  rw [hc] at hs
  change 0 ≤ sin (separationAngle k r) at hn
  nlinarith [enorm_nonneg (k ⨯₃ r)]

/-- Appendix B's trigonometric factors for the actual angle between axes. -/
theorem commutator_bounds_angle (l : ℝ) (hl : 0 ≤ l) (r k v : Vec3)
    (hr : r ⬝ᵥ r = 1) (hk : k ⬝ᵥ k = 1) :
    enorm (commutator₁ l r k v) ≤ 3*l*sin (separationAngle k r)*enorm v ∧
    enorm (commutator₂ l r k v) ≤ (3*l/2)*|sin (2*separationAngle k r)| * enorm v := by
  constructor
  · simpa [separationAngle_sin k r hk hr] using commutator₁_bound l hl r k v hr
  · have h := commutator₂_bound l hl r k v
    rw [sin_two_mul, abs_mul, abs_mul, separationAngle_sin k r hk hr,
      separationAngle_cos k r hk hr, abs_of_nonneg (enorm_nonneg _)]
    norm_num
    convert h using 1 <;> ring

def attitudeResidual (l : ℝ) (r k : Vec3) (t : ℝ) (v : Vec3) : Vec3 :=
  Jacobian.leftInv k t (radialMap l r (Jacobian.left k t v)) - radialMap l r v

theorem jacobian_commutator (l : ℝ) (r k v : Vec3) (hk : k ⬝ᵥ k = 1)
    (t : ℝ) (ht : t ≠ 0) :
    radialMap l r (Jacobian.left k t v) - Jacobian.left k t (radialMap l r v) =
      ((1-cos t)/t) • commutator₁ l r k v + ((t-sin t)/t) • commutator₂ l r k v := by
  rw [Jacobian.left_axis_polynomial k v hk t ht,
    Jacobian.left_axis_polynomial k (radialMap l r v) hk t ht]
  ext i
  simp [radialMap, commutator₁, commutator₂]
  ring

/-- Exact conjugation/commutator identity (29), for the concrete Jacobian. -/
theorem attitudeResidual_formula (l : ℝ) (r k v : Vec3) (hk : k ⬝ᵥ k = 1)
    (t : ℝ) (ht : 0 < t) (htπ : t < 2*π) :
    attitudeResidual l r k t v = Jacobian.leftInv k t
      (((1-cos t)/t) • commutator₁ l r k v + ((t-sin t)/t) • commutator₂ l r k v) := by
  rw [← jacobian_commutator l r k v hk t ht.ne', Jacobian.leftInv_sub,
    Jacobian.leftInv_left k (radialMap l r v) hk t ht htπ]
  rfl

/-- The attitude residual bound (25) of Theorem 1, with no unproved
operator-norm hypotheses. Set l=μ/r³ to obtain the displayed physical units. -/
theorem attitudeResidual_bound (l : ℝ) (hl : 0 ≤ l) (r k v : Vec3)
    (hr : r ⬝ᵥ r = 1) (hk : k ⬝ᵥ k = 1) (t : ℝ) (ht : 0 < t) (htπ : t < π) :
    enorm (attitudeResidual l r k t v) ≤
      3*l*(sin (t/2)*sin (separationAngle k r) +
        (t-sin t)/(4*sin (t/2))*|sin (2*separationAngle k r)|) * enorm v := by
  have hs : 0 < sin (t/2) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have ha : 0 ≤ (1-cos t)/t := div_nonneg (sub_nonneg.mpr (cos_le_one t)) ht.le
  have hb : 0 ≤ (t-sin t)/t := div_nonneg (sub_nonneg.mpr (sin_le ht.le)) ht.le
  have hK : 0 ≤ (t/2)/sin (t/2) := by positivity
  obtain ⟨h1,h2⟩ := commutator_bounds_angle l hl r k v hr hk
  have h1' := mul_le_mul_of_nonneg_left h1 ha
  have h2' := mul_le_mul_of_nonneg_left h2 hb
  have hsum : enorm (((1-cos t)/t) • commutator₁ l r k v +
      ((t-sin t)/t) • commutator₂ l r k v) ≤
      ((1-cos t)/t)*(3*l*sin (separationAngle k r)*enorm v) +
      ((t-sin t)/t)*((3*l/2)*|sin (2*separationAngle k r)| * enorm v) := by
    calc
      _ ≤ _ := enorm_add_le _ _
      _ ≤ _ := by
        rw [enorm_smul, enorm_smul, abs_of_nonneg ha, abs_of_nonneg hb]
        exact add_le_add h1' h2'
  rw [attitudeResidual_formula l r k v hk t ht (by linarith)]
  calc
    _ ≤ _ := Jacobian.leftInv_bound k _ hk t ht (by linarith)
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum hK
    _ = _ := by
      rw [Jacobian.half_cos t]
      field_simp
      ring

end GNC.Gravity
