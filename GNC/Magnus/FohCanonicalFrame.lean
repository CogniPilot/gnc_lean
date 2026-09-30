import GNC.Magnus.FohWeberFlow

/-! Construction of the canonical SO(3) frame from two noncollinear angular
rate vectors. This removes the frame premise from the Weber solution formula. -/
noncomputable section
open Matrix
open scoped Matrix Matrix.Norms.Operator
namespace GNC.Magnus

def fohFrameMatrix (x z : Vec3) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.transpose (![x, z ⨯₃ x, z] : Matrix (Fin 3) (Fin 3) ℝ)

theorem foh_frame_orthogonal (x z : Vec3) (hx : x ⬝ᵥ x = 1)
    (hz : z ⬝ᵥ z = 1) (hxz : x ⬝ᵥ z = 0) :
    (fohFrameMatrix x z).transpose * fohFrameMatrix x z = 1 := by
  have hzx : z ⬝ᵥ x = 0 := by rw [dotProduct_comm]; exact hxz
  have hyy : (z ⨯₃ x) ⬝ᵥ (z ⨯₃ x) = 1 := by
    rw [cross_dot_cross, hx, hz, hxz, hzx]; norm_num
  have hxy : x ⬝ᵥ (z ⨯₃ x) = 0 := dot_cross_self z x
  have hzy : z ⬝ᵥ (z ⨯₃ x) = 0 := dot_self_cross z x
  have hyx : (z ⨯₃ x) ⬝ᵥ x = 0 := by rw [dotProduct_comm]; exact hxy
  have hyz : (z ⨯₃ x) ⬝ᵥ z = 0 := by rw [dotProduct_comm]; exact hzy
  ext i j
  change (![x, z ⨯₃ x, z] i ⬝ᵥ ![x, z ⨯₃ x, z] j) = (1 : Matrix (Fin 3) (Fin 3) ℝ) i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.one_apply,
      hx, hz, hxz, hzx, hyy, hxy, hzy, hyx, hyz]

theorem foh_frame_det (x z : Vec3) (hx : x ⬝ᵥ x = 1)
    (hz : z ⬝ᵥ z = 1) (hxz : x ⬝ᵥ z = 0) : (fohFrameMatrix x z).det = 1 := by
  rw [fohFrameMatrix, det_transpose, ← triple_product_eq_det,
    cross_cross_eq_smul_sub_smul, hz, one_smul]
  simp [hxz, hx, dotProduct_comm z x]

def fohFrame (x z : Vec3) (hx : x ⬝ᵥ x = 1)
    (hz : z ⬝ᵥ z = 1) (hxz : x ⬝ᵥ z = 0) : SO3 :=
  ⟨fohFrameMatrix x z,
    (mem_orthogonalGroup_iff' (Fin 3) ℝ).mpr (foh_frame_orthogonal x z hx hz hxz),
    foh_frame_det x z hx hz hxz⟩

theorem foh_frame_rotate (x z : Vec3) (hx : x ⬝ᵥ x = 1)
    (hz : z ⬝ᵥ z = 1) (hxz : x ⬝ᵥ z = 0) (a b c : ℝ) :
    rotate (fohFrame x z hx hz hxz) ![a, b, c] = a • x + b • (z ⨯₃ x) + c • z := by
  ext i
  simp [rotate, fohFrame, fohFrameMatrix, mulVec, dotProduct, Fin.sum_univ_succ]
  ring

theorem foh_normalized_dot (v : Vec3) (hv : v ≠ 0) :
    ((enorm v)⁻¹ • v) ⬝ᵥ ((enorm v)⁻¹ • v) = 1 := by
  have hn : enorm v ≠ 0 := (enorm_eq_zero_iff v).not.mpr hv
  rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, dot_self_lengthSq, ← enorm_sq]
  field_simp

theorem foh_enorm_pos (v : Vec3) (hv : v ≠ 0) : 0 < enorm v :=
  lt_of_le_of_ne (enorm_nonneg v) (Ne.symm ((enorm_eq_zero_iff v).not.mpr hv))

/-- Noncollinearity constructs an orientation-preserving canonical frame,
with positive angular slope and positive transverse rate. -/
theorem foh_canonical_frame_exists (w s : Vec3) (hcross : s ⨯₃ w ≠ 0) :
    ∃ (C : SO3) (δ β κ : ℝ), 0 < β ∧ 0 < κ ∧
      w = rotate C ![κ, 0, δ] ∧ s = rotate C ![0, 0, β] := by
  have hs : s ≠ 0 := by intro h; apply hcross; simp [h]
  let β := enorm s
  have hβ : 0 < β := foh_enorm_pos s hs
  let z : Vec3 := β⁻¹ • s
  have hz : z ⬝ᵥ z = 1 := foh_normalized_dot s hs
  have hs' : β • z = s := by simp [z, smul_smul, hβ.ne']
  let u := Axis.transverse z w
  have hu : u ≠ 0 := by
    intro he
    have hzcross : z ⨯₃ w = 0 := by
      rw [← Axis.cross_transverse z w]
      change z ⨯₃ u = 0
      rw [he]
      simp
    apply hcross
    rw [← hs']
    simp [map_smul, hzcross]
  let κ := enorm u
  have hκ : 0 < κ := foh_enorm_pos u hu
  let x : Vec3 := κ⁻¹ • u
  have hx : x ⬝ᵥ x = 1 := foh_normalized_dot u hu
  have hxz : x ⬝ᵥ z = 0 := by
    dsimp [x]
    rw [smul_dotProduct, dotProduct_comm u z]
    simp [u, Axis.dot_transverse z w hz]
  let δ := z ⬝ᵥ w
  refine ⟨fohFrame x z hx hz hxz, δ, β, κ, hβ, hκ, ?_, ?_⟩
  · rw [foh_frame_rotate]
    simp only [zero_smul, add_zero]
    have hx' : κ • x = u := by simp [x, smul_smul, hκ.ne']
    rw [hx']
    dsimp [u, Axis.transverse, Axis.axial, δ]
    module
  · rw [foh_frame_rotate]
    simp only [zero_smul, zero_add]
    exact hs'.symm

/-- Every noncollinear affine angular-rate problem has the explicit Weber
solution, in a frame constructed from its own input vectors. -/
theorem foh_noncollinear_rotation_formula (R : ℝ → SO3) (w s : Vec3)
    (hcross : s ⨯₃ w ≠ 0)
    (hR : ∀ t, HasDerivAt (fun u => (R u).val) ((R t).val * skew (w + t • s)) t)
    (hR0 : R 0 = 1) :
    ∃ (C : SO3) (δ β κ : ℝ), 0 < β ∧ 0 < κ ∧
      w = rotate C ![κ, 0, δ] ∧ s = rotate C ![0, 0, β] ∧
      ∀ t, (R t).val = C.val *
        fohQuaternionMatrix (fohWeberQuaternionScalar (fohWeberAlpha β) δ β κ t)
          (fohWeberQuaternionVector (fohWeberAlpha β) δ β κ t) * C⁻¹.val := by
  obtain ⟨C, δ, β, κ, hβ, hκ, hw, hs⟩ := foh_canonical_frame_exists w s hcross
  exact ⟨C, δ, β, κ, hβ, hκ, hw, hs, fun t =>
    foh_weber_rotation_formula_in_frame R C w s δ β κ hβ hκ.ne' hw hs hR hR0 t⟩

end GNC.Magnus
