import GNC.Lie.Euclidean
import GNC.Analysis.Coefficients
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! SO(3) Jacobians in axis-angle coordinates. All lengths and operator norms
in this file are Euclidean. The connection to the derivative of the Lie-group
exponential is a separate obligation. -/
noncomputable section
open Matrix Real
open scoped Matrix
namespace GNC.Jacobian
open Axis

/-- Identity on the axis, complex multiplication by a+ib on its plane. -/
def planeMap (k : Vec3) (a b : ℝ) (v : Vec3) : Vec3 :=
  axial k v + a • transverse k v + b • (k ⨯₃ v)

theorem planeMap_sq (k v : Vec3) (hk : k ⬝ᵥ k = 1) (a b : ℝ) :
    lengthSq (planeMap k a b v) =
      (k ⬝ᵥ v)^2 + (a^2+b^2)*(lengthSq v - (k ⬝ᵥ v)^2) :=
  combination_lengthSq k v hk a b

theorem planeMap_dot (k v : Vec3) (hk : k ⬝ᵥ k = 1) (a b : ℝ) :
    k ⬝ᵥ planeMap k a b v = k ⬝ᵥ v := by
  simp [planeMap, axial, dot_transverse k v hk, hk]

theorem planeMap_cross (k v : Vec3) (hk : k ⬝ᵥ k = 1) (a b : ℝ) :
    k ⨯₃ planeMap k a b v = a • (k ⨯₃ v) - b • transverse k v := by
  simp [planeMap, cross_axial, cross_sq k v hk, transverse, sub_eq_add_neg]

theorem planeMap_comp (k v : Vec3) (hk : k ⬝ᵥ k = 1) (a b c d : ℝ) :
    planeMap k a b (planeMap k c d v) =
      planeMap k (a*c-b*d) (a*d+b*c) v := by
  unfold planeMap at *
  rw [show axial k (axial k v + c • transverse k v + d • (k ⨯₃ v)) = axial k v by
    unfold axial
    exact congrArg (fun z : ℝ => z • k) (planeMap_dot k v hk c d)]
  rw [show k ⨯₃ (axial k v + c • transverse k v + d • (k ⨯₃ v)) =
    c • (k ⨯₃ v) - d • transverse k v from planeMap_cross k v hk c d]
  unfold transverse
  rw [show axial k (axial k v + c • (v - axial k v) + d • (k ⨯₃ v)) = axial k v by
    unfold axial
    exact congrArg (fun z : ℝ => z • k) (planeMap_dot k v hk c d)]
  ext i; simp; ring

theorem planeMap_one (k v : Vec3) : planeMap k 1 0 v = v := by
  simp [planeMap, transverse]

theorem planeMap_axis (k : Vec3) (hk : k ⬝ᵥ k = 1) (a b : ℝ) :
    planeMap k a b k = k := by simp [planeMap, transverse, axial, hk]

def left (k : Vec3) (t : ℝ) : Vec3 → Vec3 :=
  planeMap k (sin t / t) ((1 - cos t) / t)

def leftInv (k : Vec3) (t : ℝ) : Vec3 → Vec3 :=
  planeMap k ((t/2) * (cos (t/2) / sin (t/2))) (-t/2)

def contraction (t : ℝ) : ℝ := 2 * sin (t/2) / t

theorem half_sin (t : ℝ) : sin t = 2*sin (t/2)*cos (t/2) := by
  convert sin_two_mul (t/2) using 1; congr 1; ring

theorem half_cos (t : ℝ) : cos t = 1 - 2*sin (t/2)^2 := by
  convert cos_two_mul_eq_one_sub (t/2) using 1; congr 1; ring

theorem contraction_pos (t : ℝ) (ht : 0 < t) (htπ : t < 2*π) :
    0 < contraction t := by
  exact div_pos (mul_pos (by norm_num)
    (sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))) ht

theorem contraction_le_one (t : ℝ) (ht : 0 < t) : contraction t ≤ 1 := by
  apply (div_le_one ht).mpr
  have h := sin_le (show 0 ≤ t/2 by linarith); linarith

theorem coefficients_sq (t : ℝ) :
    (sin t / t)^2 + ((1-cos t)/t)^2 = contraction t ^ 2 := by
  rw [half_sin t, half_cos t]
  unfold contraction
  have h := sin_sq_add_cos_sq (t/2)
  by_cases ht : t = 0
  · simp [ht]
  · field_simp
    nlinarith [sq_nonneg (sin (t/2)),
      congrArg (fun z : ℝ => 4*sin (t/2)^2*z) h]

/-- Appendix A's singular values, expressed intrinsically as the exact
quadratic form on the orthogonal axis and its two-dimensional plane. -/
theorem left_lengthSq (k v : Vec3) (hk : k ⬝ᵥ k = 1) (t : ℝ) :
    lengthSq (left k t v) = (k ⬝ᵥ v)^2 +
      contraction t ^ 2 * (lengthSq v - (k ⬝ᵥ v)^2) := by
  rw [left, planeMap_sq k v hk, coefficients_sq]

theorem left_bounds (k v : Vec3) (hk : k ⬝ᵥ k = 1)
    (t : ℝ) (ht : 0 < t) (htπ : t < 2*π) :
    contraction t * enorm v ≤ enorm (left k t v) ∧
      enorm (left k t v) ≤ enorm v := by
  have hs := contraction_pos t ht htπ
  have hs1 := contraction_le_one t ht
  have hd := dot_sq_le k v hk
  have he := left_lengthSq k v hk t
  have hs2 : 0 ≤ 1 - contraction t ^ 2 := by nlinarith
  have hlow := mul_nonneg hs2 (sq_nonneg (k ⬝ᵥ v))
  have hupp := mul_nonneg hs2 (sub_nonneg.mpr hd)
  simp only [← enorm_sq] at he hd hupp
  constructor
  · have hn := enorm_nonneg (left k t v)
    have hn' := enorm_nonneg v
    nlinarith [sq_nonneg (enorm (left k t v) - contraction t * enorm v)]
  · nlinarith [enorm_nonneg (left k t v), enorm_nonneg v]

/-- The closed polynomial formula for J_l in Lemma 2. -/
theorem left_closed (k v : Vec3) (hk : k ⬝ᵥ k = 1) (t : ℝ) (ht : t ≠ 0) :
    left k t v = v + ((1-cos t)/t^2) • ((t • k) ⨯₃ v) +
      ((t-sin t)/t^3) • ((t • k) ⨯₃ ((t • k) ⨯₃ v)) := by
  simp only [map_smul, LinearMap.smul_apply, smul_smul, cross_sq k v hk]
  ext i
  simp [left, planeMap, transverse]
  field_simp; ring

/-- The closed polynomial formula for the inverse in Theorem 3. -/
theorem leftInv_closed (k v : Vec3) (hk : k ⬝ᵥ k = 1) (t : ℝ) (ht : t ≠ 0) :
    leftInv k t v = v - (1/2 : ℝ) • ((t • k) ⨯₃ v) +
      (Coefficients.beta t/t^2) • ((t • k) ⨯₃ ((t • k) ⨯₃ v)) := by
  simp only [map_smul, LinearMap.smul_apply, smul_smul, cross_sq k v hk]
  ext i
  simp [leftInv, planeMap, transverse, Coefficients.beta]
  field_simp; ring

theorem inverse_coefficients (t : ℝ) (ht : t ≠ 0) (hs : sin (t/2) ≠ 0) :
    (t/2*(cos (t/2)/sin (t/2)))*(sin t/t) - (-t/2)*((1-cos t)/t) = 1 ∧
    (t/2*(cos (t/2)/sin (t/2)))*((1-cos t)/t) + (-t/2)*(sin t/t) = 0 := by
  rw [half_sin t, half_cos t]
  constructor <;> field_simp
  · nlinarith [sin_sq_add_cos_sq (t/2)]
  · ring

theorem leftInv_left (k v : Vec3) (hk : k ⬝ᵥ k = 1)
    (t : ℝ) (ht : 0 < t) (htπ : t < 2*π) : leftInv k t (left k t v) = v := by
  have hs := (sin_pos_of_pos_of_lt_pi (by linarith : 0 < t/2) (by linarith : t/2 < π)).ne'
  rw [leftInv, left, planeMap_comp k v hk,
    (inverse_coefficients t ht.ne' hs).1, (inverse_coefficients t ht.ne' hs).2,
    planeMap_one]

theorem left_leftInv (k v : Vec3) (hk : k ⬝ᵥ k = 1)
    (t : ℝ) (ht : 0 < t) (htπ : t < 2*π) : left k t (leftInv k t v) = v := by
  have hs := (sin_pos_of_pos_of_lt_pi (by linarith : 0 < t/2) (by linarith : t/2 < π)).ne'
  have h := inverse_coefficients t ht.ne' hs
  rw [left, leftInv, planeMap_comp k v hk]
  rw [show sin t/t*(t/2*(cos (t/2)/sin (t/2))) - (1-cos t)/t*(-t/2) = 1 by
    nlinarith [h.1]]
  rw [show sin t/t*(-t/2) + (1-cos t)/t*(t/2*(cos (t/2)/sin (t/2))) = 0 by
    nlinarith [h.2]]
  exact planeMap_one k v

theorem leftInv_bound (k v : Vec3) (hk : k ⬝ᵥ k = 1)
    (t : ℝ) (ht : 0 < t) (htπ : t < 2*π) :
    enorm (leftInv k t v) ≤ ((t/2)/sin (t/2)) * enorm v := by
  have h := (left_bounds k (leftInv k t v) hk t ht htπ).1
  rw [left_leftInv k v hk t ht htπ] at h
  have hs := contraction_pos t ht htπ
  have hi : (contraction t)⁻¹ = (t/2)/sin (t/2) := by
    simp [contraction]; ring
  rw [← hi]
  exact (le_inv_mul_iff₀ hs).mpr h

abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- Realization as a continuous linear map on mathlib's Euclidean space. -/
def planeLinear (k : Vec3) (a b : ℝ) : E3 →ₗ[ℝ] E3 where
  toFun v := WithLp.toLp 2 (planeMap k a b (WithLp.ofLp v))
  map_add' u v := by
    ext i
    fin_cases i <;> simp [planeMap, axial, transverse, cross_apply,
      Matrix.vecHead, Matrix.vecTail] <;> ring
  map_smul' c v := by
    ext i
    fin_cases i <;> simp [planeMap, axial, transverse, cross_apply,
      Matrix.vecHead, Matrix.vecTail] <;> ring

def leftCLM (k : Vec3) (t : ℝ) : E3 →L[ℝ] E3 :=
  (planeLinear k (sin t/t) ((1-cos t)/t)).toContinuousLinearMap

def leftInvCLM (k : Vec3) (t : ℝ) : E3 →L[ℝ] E3 :=
  (planeLinear k (t/2*(cos (t/2)/sin (t/2))) (-t/2)).toContinuousLinearMap

theorem left_add (k u v : Vec3) (t : ℝ) : left k t (u+v) = left k t u + left k t v :=
  congrArg WithLp.ofLp ((leftCLM k t).map_add (WithLp.toLp 2 u) (WithLp.toLp 2 v))

theorem left_smul (k v : Vec3) (t a : ℝ) : left k t (a • v) = a • left k t v :=
  congrArg WithLp.ofLp ((leftCLM k t).map_smul a (WithLp.toLp 2 v))

theorem leftInv_sub (k u v : Vec3) (t : ℝ) :
    leftInv k t (u-v) = leftInv k t u - leftInv k t v :=
  congrArg WithLp.ofLp ((leftInvCLM k t).map_sub (WithLp.toLp 2 u) (WithLp.toLp 2 v))

theorem left_axis_polynomial (k v : Vec3) (hk : k ⬝ᵥ k = 1) (t : ℝ) (ht : t ≠ 0) :
    left k t v = v + ((1-cos t)/t) • (k ⨯₃ v) + ((t-sin t)/t) • (k ⨯₃ (k ⨯₃ v)) := by
  rw [Axis.cross_sq k v hk]
  ext i
  simp [left, planeMap, Axis.transverse]
  field_simp; ring

theorem left_operatorNorm (k : Vec3) (hk : k ⬝ᵥ k = 1)
    (t : ℝ) (ht : 0 < t) (htπ : t < 2*π) : ‖leftCLM k t‖ = 1 := by
  have hklen : enorm k = 1 := by
    have he : enorm k ^ 2 = 1 := by rw [enorm_sq, ← dot_self_lengthSq, hk]
    nlinarith [enorm_nonneg k]
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro v
    simpa only [one_mul] using (left_bounds k (WithLp.ofLp v) hk t ht htπ).2
  · have h := (leftCLM k t).le_opNorm (WithLp.toLp 2 k)
    change enorm (left k t k) ≤ ‖leftCLM k t‖ * enorm k at h
    rw [left, planeMap_axis k hk, hklen, mul_one] at h
    exact h

theorem exists_perpendicular (k : Vec3) : ∃ v : Vec3, v ≠ 0 ∧ k ⬝ᵥ v = 0 := by
  by_cases h0 : k 0 = 0
  · refine ⟨![1,0,0], ?_, ?_⟩
    · intro h; have hh := congrFun h 0; norm_num at hh
    · simp [dotProduct, Fin.sum_univ_succ, h0]
  · refine ⟨![-k 1,k 0,0], ?_, ?_⟩
    · intro h; have hh := congrFun h 1; simp at hh; exact h0 hh
    · simp [dotProduct, Fin.sum_univ_succ]; ring

theorem left_perpendicular_length (k v : Vec3) (hk : k ⬝ᵥ k = 1)
    (hv : k ⬝ᵥ v = 0) (t : ℝ) (ht : 0 < t) (htπ : t < 2*π) :
    enorm (left k t v) = contraction t * enorm v := by
  have he := left_lengthSq k v hk t
  rw [hv] at he
  simp only [← enorm_sq] at he
  have hs := mul_nonneg (contraction_pos t ht htπ).le (enorm_nonneg v)
  nlinarith [enorm_nonneg (left k t v)]

theorem leftInv_operatorNorm (k : Vec3) (hk : k ⬝ᵥ k = 1)
    (t : ℝ) (ht : 0 < t) (htπ : t < 2*π) :
    ‖leftInvCLM k t‖ = (t/2)/sin (t/2) := by
  have hs := contraction_pos t ht htπ
  have hi : (contraction t)⁻¹ = (t/2)/sin (t/2) := by simp [contraction]; ring
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (by rw [← hi]; positivity)
    intro v
    exact leftInv_bound k (WithLp.ofLp v) hk t ht htπ
  · obtain ⟨v, hv, hkv⟩ := exists_perpendicular k
    have hvlen : 0 < enorm v := lt_of_le_of_ne (enorm_nonneg v)
      (Ne.symm (mt (enorm_eq_zero_iff v).mp hv))
    have h := (leftInvCLM k t).le_opNorm (WithLp.toLp 2 (left k t v))
    change enorm (leftInv k t (left k t v)) ≤ ‖leftInvCLM k t‖ * enorm (left k t v) at h
    rw [leftInv_left k v hk t ht htπ, left_perpendicular_length k v hk hkv t ht htπ] at h
    have hh : 1 ≤ ‖leftInvCLM k t‖ * contraction t := by
      apply (mul_le_mul_iff_left₀ hvlen).mp
      nlinarith [h]
    rw [← hi]
    exact (inv_le_iff_one_le_mul₀ hs).mpr (by simpa [mul_comm] using hh)

end GNC.Jacobian
