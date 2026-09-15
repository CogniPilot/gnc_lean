import GNC.Lie.ExponentialCoordinates
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.OpenPartialHomeomorph.Defs

/-! Rational coordinates on SO(3). These supply the algebraic part of a
chart, including both inverse identities on its actual open domain. -/
noncomputable section
open Matrix
open scoped Matrix Matrix.Norms.Operator ContDiff
namespace GNC.Cayley

abbrev Mat3 := Matrix (Fin 3) (Fin 3) ℝ

def minus (q : Vec3) : Mat3 := 1-skew q
def plus (q : Vec3) : Mat3 := 1+skew q
def matrix (q : Vec3) : Mat3 := plus q*(minus q)⁻¹

theorem det_minus (q : Vec3) : (minus q).det = 1+lengthSq q := by
  simp [minus, skew, det_fin_three, lengthSq]; ring

theorem det_plus (q : Vec3) : (plus q).det = 1+lengthSq q := by
  simp [plus, skew, det_fin_three, lengthSq]; ring

theorem minus_unit (q : Vec3) : IsUnit (minus q).det := by
  rw [isUnit_iff_ne_zero, det_minus]
  linarith [lengthSq_nonneg q]

theorem plus_unit (q : Vec3) : IsUnit (plus q).det := by
  rw [isUnit_iff_ne_zero, det_plus]
  linarith [lengthSq_nonneg q]

theorem plus_minus (q : Vec3) : plus q*minus q = minus q*plus q := by
  unfold plus minus; noncomm_ring

theorem matrix_denominator (q : Vec3) : matrix q*minus q = plus q := by
  rw [matrix, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (minus_unit q), Matrix.mul_one]

theorem transpose_minus (q : Vec3) : (minus q)ᵀ = plus q := by
  simp [minus, plus, skew_transpose]

theorem transpose_plus (q : Vec3) : (plus q)ᵀ = minus q := by
  simp [minus, plus, skew_transpose, sub_eq_add_neg]

theorem matrix_orthogonal (q : Vec3) : (matrix q)ᵀ*matrix q = 1 := by
  rw [matrix, transpose_mul, transpose_nonsing_inv, transpose_minus, transpose_plus]
  rw [← Matrix.mul_assoc, Matrix.mul_assoc (plus q)⁻¹, ← plus_minus,
    ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (plus_unit q), Matrix.one_mul,
    Matrix.mul_nonsing_inv _ (minus_unit q)]

theorem matrix_det (q : Vec3) : (matrix q).det = 1 := by
  rw [matrix, det_mul, det_nonsing_inv, det_plus, det_minus]
  simpa only [Ring.inverse_eq_inv] using
    mul_inv_cancel₀ (show (1+lengthSq q : ℝ) ≠ 0 by linarith [lengthSq_nonneg q])

def rotation (q : Vec3) : SO3 := ⟨matrix q,
  (Matrix.mem_specialOrthogonalGroup_iff).mpr
    ⟨(Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mpr (matrix_orthogonal q), matrix_det q⟩⟩

def ratio (A : Mat3) : Mat3 := (A-1)*(A+1)⁻¹

theorem ratio_mul (A : Mat3) (hA : IsUnit (A+1).det) : ratio A*(A+1) = A-1 := by
  simp [ratio, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hA]

theorem mul_ratio (A : Mat3) (hA : IsUnit (A+1).det) : (A+1)*ratio A = A-1 := by
  have hc : (A+1)*(A-1) = (A-1)*(A+1) := by noncomm_ring
  rw [ratio, ← Matrix.mul_assoc, hc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hA,
    Matrix.mul_one]

theorem ratio_skew (A : Mat3) (ho : Aᵀ*A = 1) (hA : IsUnit (A+1).det) :
    (ratio A)ᵀ = -ratio A := by
  have ht : (A+1)ᵀ*(ratio A)ᵀ = (A-1)ᵀ := by
    simpa only [transpose_mul] using congrArg Matrix.transpose (ratio_mul A hA)
  have hs : (A+1)ᵀ*((ratio A)ᵀ+ratio A)*(A+1) = 0 := by
    rw [Matrix.mul_add (A+1)ᵀ, Matrix.add_mul, ht, Matrix.mul_assoc, ratio_mul A hA]
    simp only [transpose_sub, transpose_add, transpose_one]
    noncomm_ring [ho]
  have h := congrArg (fun Z : Mat3 => ((A+1)ᵀ)⁻¹*Z*(A+1)⁻¹) hs
  simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (Matrix.isUnit_det_transpose _ hA),
    Matrix.one_mul, Matrix.zero_mul, Matrix.mul_zero] at h
  rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hA, Matrix.mul_one] at h
  exact eq_neg_of_add_eq_zero_left h

def unskew (A : Mat3) : Vec3 := ![A 2 1,A 0 2,A 1 0]

@[simp] theorem unskew_skew (q : Vec3) : unskew (skew q) = q := by
  ext i; fin_cases i <;> rfl

theorem skew_unskew (A : Mat3) (hA : Aᵀ = -A) : skew (unskew A) = A := by
  have h (i j : Fin 3) : A j i = -A i j := congrFun (congrFun hA i) j
  ext i j; fin_cases i <;> fin_cases j <;> simp [skew, unskew] <;>
    first | linarith [h 0 0] | linarith [h 1 1] | linarith [h 2 2] |
      linarith [h 0 1] | linarith [h 0 2] | linarith [h 1 2]

def coordinates (R : SO3) : Vec3 := unskew (ratio R.val)
def domain : Set SO3 := {R | IsUnit (R.val+1).det}

theorem matrix_plus_unit (q : Vec3) : IsUnit (matrix q+1).det := by
  apply Matrix.isUnit_det_of_right_inverse
  show (matrix q+1)*((1/2:ℝ) • minus q) = 1
  rw [Matrix.mul_smul, Matrix.add_mul, matrix_denominator, Matrix.one_mul]
  have h : plus q+minus q = (2:ℝ) • (1:Mat3) := by unfold plus minus; module
  rw [h, smul_smul]
  norm_num

theorem ratio_matrix (q : Vec3) : ratio (matrix q) = skew q := by
  have hd := matrix_denominator q
  have hs : (matrix q+1)*skew q = matrix q-1 := by
    dsimp [minus, plus] at hd
    linear_combination (norm := noncomm_ring) -hd
  have he := (mul_ratio (matrix q) (matrix_plus_unit q)).trans hs.symm
  have h := congrArg (fun Z : Mat3 => (matrix q+1)⁻¹*Z) he
  simpa only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (matrix_plus_unit q),
    Matrix.one_mul] using h

@[simp] theorem coordinates_rotation (q : Vec3) : coordinates (rotation q) = q := by
  simp [coordinates, rotation, ratio_matrix]

theorem rotation_mem_domain (q : Vec3) : rotation q ∈ domain := matrix_plus_unit q

theorem rotation_coordinates (R : SO3) (hR : R ∈ domain) : rotation (coordinates R) = R := by
  have ho := (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp R.property.1
  have hs : skew (coordinates R) = ratio R.val := skew_unskew _ (ratio_skew R.val ho hR)
  apply Subtype.ext
  change matrix (coordinates R) = R.val
  have hd := matrix_denominator (coordinates R)
  have hr := mul_ratio R.val hR
  have hh : R.val*minus (coordinates R) = plus (coordinates R) := by
    dsimp [minus, plus]
    rw [hs]
    linear_combination (norm := noncomm_ring) -hr
  have he := congrArg (fun Z : Mat3 => Z*(minus (coordinates R))⁻¹) (hd.trans hh.symm)
  simpa only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (minus_unit _), Matrix.mul_one] using he

def skewLinear : Vec3 →ₗ[ℝ] Mat3 where
  toFun := skew
  map_add' u v := by ext i j; fin_cases i <;> fin_cases j <;> simp [skew] <;> ring
  map_smul' c v := skew_smul c v

def unskewLinear : Mat3 →ₗ[ℝ] Vec3 where
  toFun := unskew
  map_add' A B := by ext i; fin_cases i <;> rfl
  map_smul' c A := by ext i; fin_cases i <;> rfl

theorem contDiff_skew : ContDiff ℝ ∞ skew := skewLinear.toContinuousLinearMap.contDiff

theorem contDiff_unskew : ContDiff ℝ ∞ unskew := unskewLinear.toContinuousLinearMap.contDiff

/-- Smoothness of matrix inversion is imported from mathlib's theorem for
units of a complete normed algebra. -/
theorem contDiffAt_matrix_inverse (A : Mat3) (hA : IsUnit A.det) :
    ContDiffAt ℝ ∞ (fun B : Mat3 => B⁻¹) A := by
  obtain ⟨U, rfl⟩ := (Matrix.isUnit_iff_isUnit_det A).mpr hA
  simpa only [Matrix.nonsing_inv_eq_ringInverse] using contDiffAt_ringInverse ℝ U

theorem contDiff_matrix : ContDiff ℝ ∞ matrix := by
  rw [contDiff_iff_contDiffAt]
  intro q
  have hp : ContDiff ℝ ∞ plus := contDiff_const.add contDiff_skew
  have hm : ContDiff ℝ ∞ minus := contDiff_const.sub contDiff_skew
  exact hp.contDiffAt.mul ((contDiffAt_matrix_inverse (minus q) (minus_unit q)).comp q hm.contDiffAt)

theorem contDiffAt_ratio (A : Mat3) (hA : IsUnit (A+1).det) : ContDiffAt ℝ ∞ ratio A := by
  exact (contDiffAt_id.sub contDiffAt_const).mul
    ((contDiffAt_matrix_inverse (A+1) hA).comp A (contDiffAt_id.add contDiffAt_const))

theorem continuous_rotation : Continuous rotation :=
  contDiff_matrix.continuous.subtype_mk _

theorem continuousOn_coordinates : ContinuousOn coordinates domain := by
  intro R hR
  exact (((contDiff_unskew.contDiffAt.comp R.val (contDiffAt_ratio R.val hR)).continuousAt).comp
    continuous_subtype_val.continuousAt).continuousWithinAt

theorem isOpen_domain : IsOpen domain := by
  have hc : Continuous (fun R : SO3 => (R.val+1).det) :=
    (continuous_subtype_val.add continuous_const).matrix_det
  simpa [domain, isUnit_iff_ne_zero] using
    (isOpen_ne : IsOpen {x : ℝ | x ≠ 0}).preimage hc

/-- The Cayley chart is a homeomorphism from the rotations without a -1
eigenvalue onto all of ℝ³, with smooth ambient matrix formulas in both directions. -/
def chart : OpenPartialHomeomorph SO3 Vec3 where
  toFun := coordinates
  invFun := rotation
  source := domain
  target := Set.univ
  map_source' _ _ := Set.mem_univ _
  map_target' q _ := rotation_mem_domain q
  left_inv' := rotation_coordinates
  right_inv' q _ := coordinates_rotation q
  open_source := isOpen_domain
  open_target := isOpen_univ
  continuousOn_toFun := continuousOn_coordinates
  continuousOn_invFun := continuous_rotation.continuousOn

@[simp] theorem rotation_zero : rotation 0 = 1 := by
  apply Subtype.ext
  simp [rotation, matrix, plus, minus, skew_zero]

theorem one_mem_domain : (1 : SO3) ∈ domain := by
  simpa using rotation_mem_domain (0 : Vec3)

end GNC.Cayley
