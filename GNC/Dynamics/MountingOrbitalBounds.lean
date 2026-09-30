import GNC.Dynamics.MountingOrbitalError

/-! A quadratic orbital remainder for constant body-fixed mounting error.
These are dimensionless coordinates with the library's box norm. The
factor four is a proved Euclidean/box conversion, not a fitted allowance.
Spatial gravity and noncommuting frame transport are both charged.
-/
noncomputable section
namespace GNC.MountingOrbitalError
open Matrix Real

def linearMap (μ : ℝ) (R : SO3) (q a ω : Vec3) : LogState →ₗ[ℝ] LogState where
  toFun := linearPart μ R q a ω
  map_add' x y := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [linearPart, OrbitalNearAffine.gradient, Gravity.radialMap,
        cross_apply, dotProduct, Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail] <;> ring
  map_smul' c x := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [linearPart, OrbitalNearAffine.gradient, Gravity.radialMap,
        cross_apply, dotProduct, Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail] <;> ring

def operator (μ : ℝ) (R : SO3) (q a ω : Vec3) : LogState →L[ℝ] LogState :=
  (linearMap μ R q a ω).toContinuousLinearMap

def componentCoefficient (μ r D : ℝ) (q ω : Vec3) : ℝ :=
  (4/3:ℝ)*enorm ω+2*(μ/enorm q^3)+4*μ/(r-D)^4

def coefficient (μ r D : ℝ) (q ω : Vec3) : ℝ := 4*componentCoefficient μ r D q ω

theorem coefficient_nonneg {μ r D : ℝ} (hμ : 0≤μ) (q ω : Vec3) :
    0≤coefficient μ r D q ω := by
  have := enorm_nonneg q
  have := enorm_nonneg ω
  unfold coefficient componentCoefficient
  positivity

theorem remainder_component_bound (μ : ℝ) (hμ : 0≤μ) (R : SO3) (q ω : Vec3)
    (x : LogState) {r D B : ℝ} (hD : D<r) (hq : r≤enorm q)
    (hB : 0≤B) (hBD : B≤D) (hbox : ∀ i, enorm (x i)≤B) (hφ : enorm (x 2)≤1) :
    ‖remainder μ R q ω x‖≤componentCoefficient μ r D q ω*B^2 := by
  have hq0 := enorm_nonneg q
  have hw0 := enorm_nonneg ω
  have hx0 := enorm_nonneg (x 0)
  have hx2 := enorm_nonneg (x 2)
  have ht (i : Fin 3) : enorm (MountingTransport.defect (x 2) ω (x i))≤
      ((4/3:ℝ)*enorm ω)*B^2 := by
    have hcross := (cross_enorm_le ω (x 2)).trans
      (mul_le_mul_of_nonneg_left (hbox 2) hw0)
    have h := MountingTransport.defect_uniform (x 2) ω (x i) hφ
    apply h.trans
    calc
      _ ≤ (4/3:ℝ)*(enorm ω*B)*B := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left hcross (by norm_num))
          (hbox i) (enorm_nonneg _) (by positivity)
      _ = _ := by ring
  have hg : enorm (OrbitalNearAffine.residual μ R q x)≤
      (2*(μ/enorm q^3)+4*μ/(r-D)^4)*B^2 := by
    have h := OrbitalNearAffine.residual_bound μ hμ R q x hD hq
      ((hbox 0).trans hBD) hφ
    apply h.trans
    calc
      _ ≤ 2*(μ/enorm q^3)*B*B+(4*μ/(r-D)^4)*B^2 := by
        gcongr
        · exact hbox 2
        · exact hbox 0
        · exact hbox 0
      _ = _ := by ring
  have hnon : 0≤componentCoefficient μ r D q ω*B^2 := by
    unfold componentCoefficient
    positivity
  apply (pi_norm_le_iff_of_nonneg hnon).mpr
  intro i
  fin_cases i
  · have hg0 : 0≤(2*(μ/enorm q^3)+4*μ/(r-D)^4)*B^2 := by positivity
    change ‖-MountingTransport.defect (x 2) ω (x 0)‖≤_
    rw [norm_neg]
    exact (pi_norm_le_enorm _).trans ((ht 0).trans (by unfold componentCoefficient; nlinarith))
  · change ‖OrbitalNearAffine.residual μ R q x-MountingTransport.defect (x 2) ω (x 1)‖≤_
    apply (norm_sub_le _ _).trans
    have h := add_le_add ((pi_norm_le_enorm _).trans hg) ((pi_norm_le_enorm _).trans (ht 1))
    exact h.trans_eq (by unfold componentCoefficient; ring)
  · simpa [remainder] using hnon

/-- The nonlinear remainder is second order in the combined mounting and
translation error. Its known coefficient now includes angular rate. -/
theorem remainder_quadratic (μ : ℝ) (hμ : 0≤μ) (R : SO3) (q ω : Vec3)
    (x : LogState) {r D : ℝ} (hD : D<r) (hq : r≤enorm q)
    (hpos : 2*‖x‖≤D) (hφ : enorm (x 2)≤1) :
    ‖remainder μ R q ω x‖≤coefficient μ r D q ω*‖x‖^2 := by
  have h := remainder_component_bound μ hμ R q ω x hD hq
    (show 0≤2*‖x‖ by positivity) hpos (fun i =>
      (enorm_le_two_pi_norm _).trans
        (mul_le_mul_of_nonneg_left (norm_le_pi_norm x i) (by norm_num))) hφ
  exact h.trans_eq (by unfold coefficient; ring)

end GNC.MountingOrbitalError
