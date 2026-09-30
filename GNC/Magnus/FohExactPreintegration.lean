import GNC.Magnus.FohCanonicalFrame
import GNC.Magnus.FohRotationSensitivity
import GNC.Magnus.FohForceMoments
import GNC.Magnus.FohRotationSolution

/-! Exact noncollinear FOH preintegration. Rotation is the proved Weber
solution; actual force moments are defined by integrals, and their parameter
representation follows from genuine differentiation of the rotation ODE. -/
noncomputable section
open Matrix Set
open scoped Matrix Matrix.Norms.Operator
namespace GNC.Magnus

def fohRotationMap (R : ℝ → SO3) (t : ℝ) : Vec3 →ₗ[ℝ] Vec3 :=
  Matrix.toLin' (R t).val

def fohRotationMoment (R : ℝ → SO3) (j : ℕ) (t : ℝ) : Vec3 →ₗ[ℝ] Vec3 :=
  Matrix.toLin' (∫ u in (0 : ℝ)..t, u ^ j • (R u).val)

theorem foh_rotationMap_derivative (R : ℝ → SO3) (w : Vec3) {t : ℝ}
    (hR : HasDerivAt (fun u => (R u).val) ((R t).val * skew w) t) (x : Vec3) :
    HasDerivAt (fun u => fohRotationMap R u x) (fohRotationMap R t (w ⨯₃ x)) t := by
  convert GNC.SymplecticResponse.mulVec_derivative hR (hasDerivAt_const t x) using 1
  simp [fohRotationMap, ← Matrix.mulVec_mulVec, skew_mulVec]

theorem foh_rotationMoment_derivative (R : ℝ → SO3)
    (hR : Continuous (fun t => (R t).val)) (j : ℕ) (t : ℝ) (x : Vec3) :
    HasDerivAt (fun u => fohRotationMoment R j u x) (t ^ j • rotate (R t) x) t := by
  have hc : Continuous (fun u => u ^ j • (R u).val) := (continuous_id.pow j).smul hR
  have hp := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  convert GNC.SymplecticResponse.mulVec_derivative hp (hasDerivAt_const t x) using 1
  simp [fohRotationMoment, rotate, Matrix.smul_mulVec]

@[simp] theorem foh_rotationMoment_initial (R : ℝ → SO3) (j : ℕ) :
    fohRotationMoment R j 0 = 0 := by simp [fohRotationMoment]

theorem foh_rotationMoment_integral (R : ℝ → SO3)
    (hR : Continuous (fun t => (R t).val)) (j : ℕ) (T : ℝ) (x : Vec3) :
    fohRotationMoment R j T x = ∫ t in (0 : ℝ)..T, t ^ j • rotate (R t) x := by
  have hc : Continuous (fun t => t ^ j • rotate (R t) x) :=
    (continuous_id.pow j).smul (hR.matrix_mulVec continuous_const)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => foh_rotationMoment_derivative R hR j t x) (hc.intervalIntegrable 0 T)
  simpa using h.symm

theorem foh_velocity_moments (R : ℝ → SO3) (v : ℝ → Vec3) (a b : Vec3)
    (hR : Continuous (fun t => (R t).val))
    (hv : ∀ t, HasDerivAt v (rotate (R t) (a + t • b)) t) (hv0 : v 0 = 0) (T : ℝ) :
    v T = fohRotationMoment R 0 T a + fohRotationMoment R 1 T b := by
  let V := fun t => fohRotationMoment R 0 t a + fohRotationMoment R 1 t b
  have hd (t : ℝ) : HasDerivAt V (rotate (R t) (a + t • b)) t := by
    convert (foh_rotationMoment_derivative R hR 0 t a).add
      (foh_rotationMoment_derivative R hR 1 t b) using 1
    simp [rotate, Matrix.mulVec_add, Matrix.mulVec_smul]
  have hz (t : ℝ) : HasDerivAt (fun u => v u - V u) 0 t := by
    simpa using (hv t).sub (hd t)
  have hc := is_const_of_deriv_eq_zero (fun t => (hz t).differentiableAt)
    (fun t => (hz t).deriv) T 0
  simpa [V, hv0] using sub_eq_zero.mp (by simpa [V, hv0] using hc)

theorem foh_position_moments (R : ℝ → SO3) (v p : ℝ → Vec3)
    (w s a b k : Vec3) (lam : ℝ)
    (hR : ∀ t, HasDerivAt (fun u => (R u).val) ((R t).val * skew (w + t • s)) t)
    (hb : b = s ⨯₃ k + lam • s)
    (hv : ∀ t, HasDerivAt v (rotate (R t) (a + t • b)) t) (hv0 : v 0 = 0)
    (hp : ∀ t, HasDerivAt p (v t) t) (hp0 : p 0 = 0) (T : ℝ) :
    p T = fohCompactPosition (fohRotationMap R) (fohRotationMoment R 0)
      (fohRotationMoment R 1) w s a b k lam T := by
  have hc : Continuous (fun t => (R t).val) :=
    continuous_iff_continuousAt.mpr (fun t => (hR t).continuousAt)
  let P := fohCompactPosition (fohRotationMap R) (fohRotationMoment R 0)
    (fohRotationMoment R 1) w s a b k lam
  have hd (t : ℝ) : HasDerivAt P (v t) t := by
    rw [foh_velocity_moments R v a b hc hv hv0 t]
    apply fohCompactPosition_derivative _ _ _ w s a b k lam t hb
    · exact fun x => foh_rotationMap_derivative R _ (hR t) x
    · intro x
      simpa [fohRotationMap, rotate] using foh_rotationMoment_derivative R hc 0 t x
    · intro x
      simpa [fohRotationMap, rotate] using foh_rotationMoment_derivative R hc 1 t x
  have hz (t : ℝ) : HasDerivAt (fun u => p u - P u) 0 t := by
    simpa using (hp t).sub (hd t)
  have hP0 : P 0 = 0 := fohCompactPosition_initial _ _ _ _ _ _ _ _ _
    (foh_rotationMoment_initial R 0) (foh_rotationMoment_initial R 1)
  have he := is_const_of_deriv_eq_zero (fun t => (hz t).differentiableAt)
    (fun t => (hz t).deriv) T 0
  exact sub_eq_zero.mp (by simpa only [hp0, hP0, sub_self] using he)

def fohForceCrossCoefficient (s b : Vec3) : Vec3 :=
  -(fohDot s s)⁻¹ • (s ⨯₃ b)
def fohForceParallelCoefficient (s b : Vec3) : ℝ := fohDot b s / fohDot s s

/-- The exact force moments are parameter derivatives of a constructed
rotation family, with no variation-equation or existence assumptions. -/
theorem foh_exact_moment_sensitivities (R : ℝ → SO3) (w s : Vec3)
    (hR : ∀ t, HasDerivAt (fun u => (R u).val) ((R t).val * skew (w + t • s)) t)
    (hR0 : R 0 = 1) {T : ℝ} (hT : 0 ≤ T) (x : Vec3) :
    HasDerivAt (fun q : ℝ => (fohExactRotation (w + q • x) s T).val * (R T)⁻¹.val)
      (skew (fohRotationMoment R 0 T x)) 0 ∧
    HasDerivAt (fun q : ℝ => (fohExactRotation w (s + q • x) T).val * (R T)⁻¹.val)
      (skew (fohRotationMoment R 1 T x)) 0 := by
  have hc : Continuous (fun t => (R t).val) :=
    continuous_iff_continuousAt.mpr (fun t => (hR t).continuousAt)
  have he := foh_exactRotation_unique R w s hR hR0
  have h0 := foh_exactRotation_constant_sensitivity w s x hT
  have h1 := foh_exactRotation_linear_sensitivity w s x hT
  rw [← he] at h0 h1
  constructor
  · simpa [foh_rotationMoment_integral R hc 0 T x] using h0
  · simpa [foh_rotationMoment_integral R hc 1 T x] using h1

/-- End-to-end exact FOH preintegration for noncollinear angular inputs and
affine specific force. The hypotheses are only the original physical time
ODEs, their initial data, and the generic-branch condition. The conclusions
combine the constructed Weber rotation, true parameter sensitivities, and
the compact velocity/position endpoints. -/
theorem foh_exact_preintegration_endpoints
    (R : ℝ → SO3) (v p : ℝ → Vec3) (w s a b : Vec3)
    (hcross : s ⨯₃ w ≠ 0)
    (hR : ∀ t, HasDerivAt (fun u => (R u).val) ((R t).val * skew (w + t • s)) t)
    (hR0 : R 0 = 1)
    (hv : ∀ t, HasDerivAt v (rotate (R t) (a + t • b)) t) (hv0 : v 0 = 0)
    (hp : ∀ t, HasDerivAt p (v t) t) (hp0 : p 0 = 0)
    {T : ℝ} (hT : 0 ≤ T) :
    ∃ (C : SO3) (δ β κ : ℝ), 0 < β ∧ 0 < κ ∧
      w = rotate C ![κ, 0, δ] ∧ s = rotate C ![0, 0, β] ∧
      (R T).val = C.val *
        fohQuaternionMatrix (fohWeberQuaternionScalar (fohWeberAlpha β) δ β κ T)
          (fohWeberQuaternionVector (fohWeberAlpha β) δ β κ T) * C⁻¹.val ∧
      (∀ x : Vec3,
        HasDerivAt (fun q : ℝ => (fohExactRotation (w + q • x) s T).val * (R T)⁻¹.val)
          (skew (fohRotationMoment R 0 T x)) 0 ∧
        HasDerivAt (fun q : ℝ => (fohExactRotation w (s + q • x) T).val * (R T)⁻¹.val)
          (skew (fohRotationMoment R 1 T x)) 0) ∧
      v T = fohRotationMoment R 0 T a + fohRotationMoment R 1 T b ∧
      p T = fohCompactPosition (fohRotationMap R) (fohRotationMoment R 0)
        (fohRotationMoment R 1) w s a b (fohForceCrossCoefficient s b)
          (fohForceParallelCoefficient s b) T := by
  obtain ⟨C, δ, β, κ, hβ, hκ, hw, hs, hf⟩ :=
    foh_noncollinear_rotation_formula R w s hcross hR hR0
  have hc : Continuous (fun t => (R t).val) :=
    continuous_iff_continuousAt.mpr (fun t => (hR t).continuousAt)
  have hs0 : s ≠ 0 := by intro h; apply hcross; simp [h]
  have hss : fohDot s s ≠ 0 := by
    have he : fohDot s s = lengthSq s := by simp [fohDot, lengthSq]; ring
    rw [he]
    exact (lengthSq_eq_zero_iff s).not.mpr hs0
  have hb : b = s ⨯₃ fohForceCrossCoefficient s b + fohForceParallelCoefficient s b • s :=
    foh_force_slope_decomposition s b hss
  exact ⟨C, δ, β, κ, hβ, hκ, hw, hs, hf T,
    fun x => foh_exact_moment_sensitivities R w s hR hR0 hT x,
    foh_velocity_moments R v a b hc hv hv0 T,
    foh_position_moments R v p w s a b _ _ hR hb hv hv0 hp hp0 T⟩

end GNC.Magnus
