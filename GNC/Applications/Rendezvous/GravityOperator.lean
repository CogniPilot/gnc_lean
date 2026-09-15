import GNC.Dynamics.GravityAttitude

/-! Exact Euclidean operator norms in Appendix B, not just action bounds. -/
noncomputable section
open Matrix Real
open scoped Matrix
namespace GNC.Gravity

def radialLinear (l : ℝ) (r : Vec3) : Vec3 →ₗ[ℝ] Vec3 where
  toFun := radialMap l r
  map_add' v w := by simp [radialMap, dotProduct_add]; module
  map_smul' c v := by simp [radialMap, smul_sub, smul_smul]; module

def euclideanCLM (f : Vec3 →ₗ[ℝ] Vec3) : Jacobian.E3 →L[ℝ] Jacobian.E3 :=
  (((WithLp.linearEquiv 2 ℝ Vec3).symm.toLinearMap.comp f).comp
    (WithLp.linearEquiv 2 ℝ Vec3).toLinearMap).toContinuousLinearMap

def commutator₁CLM (l : ℝ) (r k : Vec3) : Jacobian.E3 →L[ℝ] Jacobian.E3 :=
  euclideanCLM ((radialLinear l r).comp (crossProduct k) - (crossProduct k).comp (radialLinear l r))

def commutator₂CLM (l : ℝ) (r k : Vec3) : Jacobian.E3 →L[ℝ] Jacobian.E3 :=
  euclideanCLM ((radialLinear l r).comp ((crossProduct k).comp (crossProduct k)) -
    ((crossProduct k).comp (crossProduct k)).comp (radialLinear l r))

theorem commutator₁_radial_norm (l : ℝ) (hl : 0 ≤ l) (r k : Vec3) (hr : r ⬝ᵥ r = 1) :
    enorm (commutator₁ l r k r) = 3*l*enorm (k ⨯₃ r) := by
  rw [commutator₁_formula, dotProduct_comm (k ⨯₃ r) r, dot_cross_self, hr]
  simp only [zero_smul, one_smul, zero_add, enorm_smul, abs_mul, abs_neg,
    abs_of_nonneg hl, abs_of_nonneg (show (0:ℝ) ≤ 3 by norm_num)]

theorem transverse_enorm_cross (r k : Vec3) (hr : r ⬝ᵥ r = 1) :
    enorm (Axis.transverse r k) = enorm (k ⨯₃ r) := by
  have h : enorm (Axis.transverse r k)^2 = enorm (r ⨯₃ k)^2 := by
    rw [enorm_sq, enorm_sq, Axis.transverse_sq r k hr, Axis.cross_lengthSq r k hr]
  rw [← cross_anticomm k r, enorm_neg] at h
  nlinarith [enorm_nonneg (Axis.transverse r k), enorm_nonneg (k ⨯₃ r)]

theorem commutator₂_radial_norm (l : ℝ) (hl : 0 ≤ l) (r k : Vec3) (hr : r ⬝ᵥ r = 1) :
    enorm (commutator₂ l r k r) = 3*l*|k ⬝ᵥ r| *enorm (k ⨯₃ r) := by
  rw [commutator₂_formula, hr, one_smul]
  have h : (k ⬝ᵥ r) • r-k = -Axis.transverse r k := by
    rw [Axis.transverse, Axis.axial, dotProduct_comm k r]; module
  rw [h, enorm_smul, enorm_neg, transverse_enorm_cross r k hr, abs_mul,
    abs_of_nonneg (show 0 ≤ 3*l by positivity)]

theorem commutator₁CLM_norm (l : ℝ) (hl : 0 ≤ l) (r k : Vec3) (hr : r ⬝ᵥ r = 1) :
    ‖commutator₁CLM l r k‖ = 3*l*enorm (k ⨯₃ r) := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (by positivity) (enorm_nonneg _))
    intro v
    exact commutator₁_bound l hl r k (WithLp.ofLp v) hr
  · have h := (commutator₁CLM l r k).le_opNorm (WithLp.toLp 2 r)
    change enorm (commutator₁ l r k r) ≤ ‖commutator₁CLM l r k‖*enorm r at h
    simpa only [commutator₁_radial_norm l hl r k hr, unit_enorm r hr, mul_one] using h

theorem commutator₂CLM_norm (l : ℝ) (hl : 0 ≤ l) (r k : Vec3) (hr : r ⬝ᵥ r = 1) :
    ‖commutator₂CLM l r k‖ = 3*l*|k ⬝ᵥ r| *enorm (k ⨯₃ r) := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (by positivity) (enorm_nonneg _))
    intro v
    exact commutator₂_bound l hl r k (WithLp.ofLp v)
  · have h := (commutator₂CLM l r k).le_opNorm (WithLp.toLp 2 r)
    change enorm (commutator₂ l r k r) ≤ ‖commutator₂CLM l r k‖*enorm r at h
    simpa only [commutator₂_radial_norm l hl r k hr, unit_enorm r hr, mul_one] using h

/-- Both exact norms in equation (30), for S = [θ k]×. The radial unit
vector attains each norm, including the zero-commutator cases. -/
theorem commutator_norms_angle (l θ : ℝ) (hl : 0 ≤ l) (hθ : 0 ≤ θ) (r k : Vec3)
    (hr : r ⬝ᵥ r = 1) (hk : k ⬝ᵥ k = 1) :
    ‖commutator₁CLM l r (θ • k)‖ = 3*l*θ*sin (separationAngle k r) ∧
    ‖commutator₂CLM l r (θ • k)‖ = (3*l/2)*θ^2*|sin (2*separationAngle k r)| := by
  rw [commutator₁CLM_norm l hl r _ hr, commutator₂CLM_norm l hl r _ hr]
  simp only [map_smul, LinearMap.smul_apply, enorm_smul, smul_dotProduct, smul_eq_mul,
    abs_mul, abs_of_nonneg hθ]
  rw [sin_two_mul, abs_mul, abs_mul, separationAngle_sin k r hk hr,
    separationAngle_cos k r hk hr, abs_of_nonneg (enorm_nonneg _)]
  norm_num
  constructor <;> ring

end GNC.Gravity
