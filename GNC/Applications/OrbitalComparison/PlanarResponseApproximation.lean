import GNC.Dynamics.PlanarResponseReduction
import GNC.Lie.RotationFeatureBounds
import GNC.Applications.OrbitalComparison.LieRadiusFrame

/-! Numerical coefficient error for the sparse planar response models.
The factors 4 and 8 come from two/four active products per output row and
the proved three-dimensional norm conversion. They are not fitted margins.
These transfer lemmas do not assume a numerical solver is accurate.
-/
noncomputable section
namespace GNC.PlanarResponseReduction
open Matrix

private theorem two_products (a b c d e : ℝ) (h₁ : |a*b|≤e) (h₂ : |c*d|≤e) :
    |a*b+c*d|≤2*e := (abs_add_le _ _).trans (by linarith)

private theorem four_products (a b c d e f g h k : ℝ)
    (h₁ : |a*b|≤k) (h₂ : |c*d|≤k) (h₃ : |e*f|≤k) (h₄ : |g*h|≤k) :
    |a*b+c*d+e*f+g*h|≤4*k := by
  have h12 := two_products a b c d k h₁ h₂
  have h123 := (abs_add_le (a*b+c*d) (e*f)).trans (add_le_add h12 h₃)
  exact (abs_add_le _ _).trans (by linarith)

theorem geometric_bound (x : Fin 4 → ℝ) (φ : Vec3) {δ θ : ℝ}
    (hδ : 0≤δ) (hθ : 0≤θ) (hx : ∀ i, |x i|≤δ) (hφ : enorm φ≤θ) :
    enorm (geometric x *ᵥ φ)≤4*δ*θ := by
  have hp (i : Fin 4) (j : Fin 3) : |x i*φ j|≤δ*θ := by
    rw [abs_mul]
    exact mul_le_mul (hx i) ((component_le_enorm φ j).trans hφ) (abs_nonneg _) hδ
  have hb : ‖geometric x *ᵥ φ‖≤2*δ*θ := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    fin_cases i
    · simpa [geometric,mulVec,dotProduct,Fin.sum_univ_succ,Real.norm_eq_abs] using
        (hp 0 2).trans (by nlinarith)
    · simpa [geometric,mulVec,dotProduct,Fin.sum_univ_succ,Real.norm_eq_abs] using
        (hp 1 2).trans (by nlinarith)
    · simpa [geometric,mulVec,dotProduct,Fin.sum_univ_succ,Real.norm_eq_abs,mul_assoc] using
        two_products (x 2) (φ 0) (x 3) (φ 1) (δ*θ) (hp 2 0) (hp 3 1)
  exact (enorm_le_two_pi_norm _).trans (by nlinarith)

theorem cartesian_bound (x : Fin 10 → ℝ) (w : Fin 6 → ℝ) {δ θ : ℝ}
    (hδ : 0≤δ) (hθ : 0≤θ) (hx : ∀ i, |x i|≤δ) (hw : ∀ i, |w i|≤θ) :
    enorm (cartesian x *ᵥ w)≤8*δ*θ := by
  have hp (i : Fin 10) (j : Fin 6) : |x i*w j|≤δ*θ := by
    rw [abs_mul]
    exact mul_le_mul (hx i) (hw j) (abs_nonneg _) hδ
  have hb : ‖cartesian x *ᵥ w‖≤4*δ*θ := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    fin_cases i
    · simpa [cartesian,mulVec,dotProduct,Fin.sum_univ_succ,Real.norm_eq_abs,mul_assoc,add_assoc] using
        four_products (x 0) (w 0) (x 2) (w 1) (x 4) (w 2) (x 6) (w 3) (δ*θ)
          (hp 0 0) (hp 2 1) (hp 4 2) (hp 6 3)
    · simpa [cartesian,mulVec,dotProduct,Fin.sum_univ_succ,Real.norm_eq_abs,mul_assoc,add_assoc] using
        four_products (x 1) (w 0) (x 3) (w 1) (x 5) (w 2) (x 7) (w 3) (δ*θ)
          (hp 1 0) (hp 3 1) (hp 5 2) (hp 7 3)
    · have h := two_products (x 8) (w 4) (x 9) (w 5) (δ*θ) (hp 8 4) (hp 9 5)
      simpa [cartesian,mulVec,dotProduct,Fin.sum_univ_succ,Real.norm_eq_abs] using
        h.trans (show 2*(δ*θ)≤4*δ*θ by nlinarith)
  exact (enorm_le_two_pi_norm _).trans (by nlinarith)

theorem component_weights_bound (φ : Vec3) {θ : ℝ}
    (hφ : enorm φ≤θ) (hθ : θ<2*Real.pi) (i : Fin 6) :
    |componentWeights (rotationExp φ) i|≤θ := by
  have h := RotationFeatureBounds.exact_entry φ
  fin_cases i
  all_goals first
    | simpa [componentWeights,RotationFeatureBounds.exactMatrix] using h 0 0 hφ hθ
    | simpa [componentWeights,RotationFeatureBounds.exactMatrix] using h 0 1 hφ hθ
    | simpa [componentWeights,RotationFeatureBounds.exactMatrix] using h 1 0 hφ hθ
    | simpa [componentWeights,RotationFeatureBounds.exactMatrix] using h 1 1 hφ hθ
    | simpa [componentWeights,RotationFeatureBounds.exactMatrix] using h 2 0 hφ hθ
    | simpa [componentWeights,RotationFeatureBounds.exactMatrix] using h 2 1 hφ hθ

theorem geometric_sub (x y : Fin 4 → ℝ) : geometric (x-y)=geometric x-geometric y := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [geometric]

theorem cartesian_sub (x y : Fin 10 → ℝ) : cartesian (x-y)=cartesian x-cartesian y := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cartesian]

theorem geometric_reconstruction_error (x y : Fin 4 → ℝ) (φ : Vec3) {δ θ : ℝ}
    (hδ : 0≤δ) (hθ : 0≤θ) (hθπ : θ<2*Real.pi)
    (hxy : ∀ i, |x i-y i|≤δ) (hφ : enorm φ≤θ) :
    ‖OrbitalComparison.LieRadiusFrame.left φ (WithLp.toLp 2 (geometric x *ᵥ φ))-
      OrbitalComparison.LieRadiusFrame.left φ (WithLp.toLp 2 (geometric y *ᵥ φ))‖≤4*δ*θ := by
  rw [←map_sub]
  apply (OrbitalComparison.LieRadiusFrame.left_norm φ (hφ.trans_lt hθπ) _).trans
  change enorm (geometric x *ᵥ φ-geometric y *ᵥ φ)≤_
  rw [←sub_mulVec,←geometric_sub]
  exact geometric_bound (x-y) φ hδ hθ hxy hφ

theorem cartesian_reconstruction_error (x y : Fin 10 → ℝ) (φ : Vec3) {δ θ : ℝ}
    (hδ : 0≤δ) (hθ : 0≤θ) (hθπ : θ<2*Real.pi)
    (hxy : ∀ i, |x i-y i|≤δ) (hφ : enorm φ≤θ) :
    enorm (cartesian x *ᵥ componentWeights (rotationExp φ)-
      cartesian y *ᵥ componentWeights (rotationExp φ))≤8*δ*θ := by
  rw [←sub_mulVec,←cartesian_sub]
  exact cartesian_bound (x-y) _ hδ hθ hxy (component_weights_bound φ hφ hθπ)

end GNC.PlanarResponseReduction
