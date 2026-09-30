import GNC.Lie.RotationTaylorBound
import GNC.Lie.JacobianAffine
import GNC.Dynamics.RotationCenteredError
import GNC.Analysis.EuclideanBox

/-! Matched exact and quadratic Cartesian rotation features. The diagonal
entries start at second order, so a feature-box certificate need not pay a
first-order bound for every entry. All results include the zero rotation. -/
noncomputable section
namespace GNC.RotationFeatureBounds
open Matrix

def exactMatrix (φ : Vec3) : Matrix (Fin 3) (Fin 3) ℝ := (rotationExp φ).val-1
def quadraticMatrix (φ : Vec3) : Matrix (Fin 3) (Fin 3) ℝ :=
  skew φ+(1/2:ℝ) • (skew φ*skew φ)

theorem exact_apply (φ v : Vec3) : exactMatrix φ *ᵥ v=rotate (rotationExp φ) v-v := by
  simp [exactMatrix, sub_mulVec, rotate]

theorem quadratic_apply (φ v : Vec3) :
    quadraticMatrix φ *ᵥ v=φ ⨯₃ v+(1/2:ℝ) • (φ ⨯₃ (φ ⨯₃ v)) := by
  simp [quadraticMatrix, add_mulVec, smul_mulVec, ←mulVec_mulVec, skew_mulVec]

theorem basis_norm (i : Fin 3) : enorm (Pi.single i (1:ℝ))=1 := by
  unfold enorm
  rw [PiLp.toLp_single, PiLp.norm_single]
  norm_num

theorem basis_cross_diagonal (φ : Vec3) (i : Fin 3) : (φ ⨯₃ Pi.single i 1) i=0 := by
  fin_cases i <;> simp [cross_apply]

theorem exact_norm (φ v : Vec3) {θ : ℝ} (hφ : enorm φ≤θ) (hθ : θ<2*Real.pi) :
    enorm (exactMatrix φ *ᵥ v)≤θ*enorm v := by
  rw [exact_apply]
  exact (RotationCenteredError.rotation_difference_bound φ v (hφ.trans_lt hθ)).trans
    (mul_le_mul_of_nonneg_right hφ (enorm_nonneg v))

theorem quadratic_norm (φ v : Vec3) {θ : ℝ} (hφ : enorm φ≤θ) :
    enorm (quadraticMatrix φ *ᵥ v)≤(θ+θ^2/2)*enorm v := by
  have hnφ := enorm_nonneg φ
  have hθ := hnφ.trans hφ
  have htθ := JacobianAffine.tail_nonneg hθ
  have h1 := (cross_enorm_le φ v).trans (mul_le_mul_of_nonneg_right hφ (enorm_nonneg v))
  have h2 := (cross_enorm_le φ (φ ⨯₃ v)).trans (mul_le_mul hφ h1 (enorm_nonneg _) hθ)
  rw [quadratic_apply]
  apply (enorm_add_le _ _).trans
  rw [enorm_smul, abs_of_pos (by norm_num : (0:ℝ)<1/2)]
  calc
    _ ≤ θ*enorm v+(1/2)*(θ*(θ*enorm v)) :=
      add_le_add h1 (mul_le_mul_of_nonneg_left h2 (by norm_num))
    _ = _ := by ring

theorem exact_entry (φ : Vec3) (i j : Fin 3) {θ : ℝ}
    (hφ : enorm φ≤θ) (hθ : θ<2*Real.pi) : |exactMatrix φ i j|≤θ := by
  have h := (component_le_enorm (exactMatrix φ *ᵥ Pi.single j 1) i).trans
    (exact_norm φ (Pi.single j 1) hφ hθ)
  simpa [basis_norm] using h

theorem quadratic_entry (φ : Vec3) (i j : Fin 3) {θ : ℝ}
    (hφ : enorm φ≤θ) : |quadraticMatrix φ i j|≤θ+θ^2/2 := by
  have h := (component_le_enorm (quadraticMatrix φ *ᵥ Pi.single j 1) i).trans
    (quadratic_norm φ (Pi.single j 1) hφ)
  simpa [basis_norm] using h

theorem exact_diagonal (φ : Vec3) (i : Fin 3) {θ : ℝ}
    (hφ : enorm φ≤θ) : |exactMatrix φ i i|≤θ^2/2 := by
  have hnφ := enorm_nonneg φ
  have hθ := hnφ.trans hφ
  have htθ := JacobianAffine.tail_nonneg hθ
  have hb := RotationTaylorBound.bound φ (Pi.single i 1)
  have he := (component_le_enorm
    (rotate (rotationExp φ) (Pi.single i 1)-Pi.single i 1-φ ⨯₃ Pi.single i 1) i).trans hb
  have hh : |exactMatrix φ i i|≤enorm φ^2/2 := by
    simpa [←exact_apply, basis_cross_diagonal, basis_norm] using he
  exact hh.trans (by gcongr)

theorem quadratic_diagonal (φ : Vec3) (i : Fin 3) {θ : ℝ}
    (hφ : enorm φ≤θ) : |quadraticMatrix φ i i|≤θ^2/2 := by
  have hnφ := enorm_nonneg φ
  have hθ := hnφ.trans hφ
  have htθ := JacobianAffine.tail_nonneg hθ
  have hn := (cross_enorm_le φ (φ ⨯₃ Pi.single i 1)).trans
    (mul_le_mul_of_nonneg_left (cross_enorm_le φ (Pi.single i 1)) (enorm_nonneg φ))
  have he := (component_le_enorm (φ ⨯₃ (φ ⨯₃ Pi.single i 1)) i).trans hn
  have hi : quadraticMatrix φ i i=(1/2:ℝ)*(φ ⨯₃ (φ ⨯₃ Pi.single i 1)) i := by
    have hh := congrFun (quadratic_apply φ (Pi.single i 1)) i
    simpa [basis_cross_diagonal] using hh
  rw [hi, abs_mul, abs_of_pos (by norm_num : (0:ℝ)<1/2)]
  calc
    _ ≤ (1/2)*(enorm φ*(enorm φ*1)) :=
      mul_le_mul_of_nonneg_left (by simpa only [basis_norm] using he) (by norm_num)
    _ ≤ θ^2/2 := by nlinarith [sq_nonneg (θ-enorm φ)]

/-- Output-force error of the quadratic feature approximation. -/
theorem quadratic_remainder (φ v : Vec3) {θ : ℝ} (hφ : enorm φ≤θ) :
    enorm ((exactMatrix φ-quadraticMatrix φ) *ᵥ v)≤JacobianAffine.tail θ*θ*enorm v := by
  rw [sub_mulVec, exact_apply, quadratic_apply]
  have hnφ := enorm_nonneg φ
  have hθ := hnφ.trans hφ
  have htθ := JacobianAffine.tail_nonneg hθ
  exact (JacobianAffine.rotation_quadratic_bound φ v).trans (by
    gcongr
    all_goals first | exact enorm_nonneg _ | exact JacobianAffine.tail_nonneg (enorm_nonneg φ) | exact JacobianAffine.tail_mono (enorm_nonneg φ) hφ)

end GNC.RotationFeatureBounds
