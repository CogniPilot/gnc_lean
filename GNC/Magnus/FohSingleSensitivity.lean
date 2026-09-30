import GNC.Magnus.FohExactPreintegration

/-! Exact reconstruction of all three force moments from the endpoint rotation
and one constant-rate directional derivative. -/
noncomputable section
open Matrix Set
open scoped Matrix Matrix.Norms.Operator
namespace GNC.Magnus

def fohSingleSensitivityColumn (R : ℝ → SO3) (w s ex : Vec3) (T : ℝ) : Vec3 :=
  Cayley.unskew (deriv (fun q : ℝ =>
    (fohExactRotation (w + q • ex) s T).val * (R T)⁻¹.val) 0)

/-- The one derivative used in the reconstruction is an actual derivative of
the constructed rotation family, not supplied column data. -/
theorem foh_singleSensitivityColumn_eq (R : ℝ → SO3) (w s ex : Vec3)
    (hR : ∀ t, HasDerivAt (fun u => (R u).val)
      ((R t).val * skew (w + t • s)) t)
    (hR0 : R 0 = 1) {T : ℝ} (hT : 0 ≤ T) :
    fohSingleSensitivityColumn R w s ex T = fohRotationMoment R 0 T ex := by
  unfold fohSingleSensitivityColumn
  rw [(foh_exact_moment_sensitivities R w s hR hR0 hT ex).1.deriv]
  exact Cayley.unskew_skew _

/-- Reconstructed zeroth moment: one sensitivity and two endpoint columns.
The coefficients are coordinates in the supplied canonical SO(3) frame. -/
def fohSingleJ (R : ℝ → SO3) (C : SO3) (w s : Vec3) (β κ T : ℝ)
    (x : Vec3) : Vec3 :=
  (rotate C⁻¹ x) 0 • fohSingleSensitivityColumn R w s (rotate C ![1, 0, 0]) T +
  (rotate C⁻¹ x) 1 • ((β * κ)⁻¹ • (s - rotate (R T) s)) +
  (rotate C⁻¹ x) 2 • (β⁻¹ • (rotate (R T) (w + T • s) - w))

theorem foh_frame_coordinate_expansion (C : SO3) (x : Vec3) :
    x = (rotate C⁻¹ x) 0 • rotate C ![1, 0, 0] +
      (rotate C⁻¹ x) 1 • rotate C ![0, 1, 0] +
      (rotate C⁻¹ x) 2 • rotate C ![0, 0, 1] := by
  have he (y : Vec3) : y = y 0 • ![1, 0, 0] + y 1 • ![0, 1, 0] +
      y 2 • ![0, 0, 1] := by
    ext i
    fin_cases i <;> simp
  calc
    x = rotate C (rotate C⁻¹ x) := by simp [← rotate_mul]
    _ = _ := by
      conv_lhs => rw [he (rotate C⁻¹ x)]
      simp only [rotate, mulVec_add, mulVec_smul]

/-- The complete integrated rotation is recovered from a single sensitivity.
No integral or proposed-column equality is assumed. -/
theorem foh_singleJ_eq (R : ℝ → SO3) (C : SO3) (w s : Vec3) (δ β κ : ℝ)
    (hβ : β ≠ 0) (hκ : κ ≠ 0)
    (hw : w = rotate C ![κ, 0, δ]) (hs : s = rotate C ![0, 0, β])
    (hR : ∀ t, HasDerivAt (fun u => (R u).val)
      ((R t).val * skew (w + t • s)) t)
    (hR0 : R 0 = 1) {T : ℝ} (hT : 0 ≤ T) (x : Vec3) :
    fohSingleJ R C w s β κ T x = fohRotationMoment R 0 T x := by
  have hc : Continuous (fun t => (R t).val) :=
    continuous_iff_continuousAt.mpr (fun t => (hR t).continuousAt)
  have h0 : fohRotationMap R 0 = LinearMap.id := by
    ext y i
    simp [fohRotationMap, hR0]
  have hd (t : ℝ) (ht : t ∈ uIcc 0 T) (y : Vec3) :=
    foh_rotationMap_derivative R _ (hR t) y
  have hz := foh_slope_endpoint_integral (fohRotationMap R) w s T h0 hd
    ((hc.matrix_mulVec continuous_const).intervalIntegrable 0 T)
  have hy := foh_cross_endpoint_integral (fohRotationMap R) w s T h0 hd
    ((hc.matrix_mulVec continuous_const).intervalIntegrable 0 T)
  have hm (y : Vec3) : fohRotationMoment R 0 T y =
      ∫ t in (0 : ℝ)..T, fohRotationMap R t y := by
    simpa [fohRotationMap, rotate] using foh_rotationMoment_integral R hc 0 T y
  rw [← hm] at hz hy
  change fohRotationMoment R 0 T s = rotate (R T) (w + T • s) - w at hz
  change fohRotationMoment R 0 T (s ⨯₃ w) = s - rotate (R T) s at hy
  have hs' : s = β • rotate C ![0, 0, 1] := by
    rw [hs]
    simp [rotate, ← mulVec_smul]
  have hsw : s ⨯₃ w = (β * κ) • rotate C ![0, 1, 0] := by
    rw [hs, hw, ← rotate_cross]
    simp [cross_apply, rotate, ← mulVec_smul]
  have hez : fohRotationMoment R 0 T (rotate C ![0, 0, 1]) =
      β⁻¹ • (rotate (R T) (w + T • s) - w) := by
    rw [← hz, hs', map_smul, smul_smul, inv_mul_cancel₀ hβ, one_smul]
  have hey : fohRotationMoment R 0 T (rotate C ![0, 1, 0]) =
      (β * κ)⁻¹ • (s - rotate (R T) s) := by
    rw [← hy, hsw, map_smul, smul_smul, inv_mul_cancel₀ (mul_ne_zero hβ hκ), one_smul]
  symm
  exact foh_one_column_reconstruction _ _ _ _ _ _ _ x _ _ _
    (foh_frame_coordinate_expansion C x)
    (foh_singleSensitivityColumn_eq R w s _ hR hR0 hT).symm hey hez

/-- The first weighted moment, assembled using only `fohSingleJ` and endpoints. -/
def fohSingleK (R : ℝ → SO3) (C : SO3) (w s : Vec3) (β κ T : ℝ)
    (x : Vec3) : Vec3 :=
  let k := fohForceCrossCoefficient s x
  let lam := fohForceParallelCoefficient s x
  rotate (R T) k - k - fohSingleJ R C w s β κ T (w ⨯₃ k) +
    (lam / 2) • (T • rotate (R T) w + T^2 • rotate (R T) s -
      fohSingleJ R C w s β κ T w)

/-- The second weighted moment, assembled from the two reconstructed moments. -/
def fohSingleL (R : ℝ → SO3) (C : SO3) (w s : Vec3) (β κ T : ℝ)
    (x : Vec3) : Vec3 :=
  let k := fohForceCrossCoefficient s x
  let lam := fohForceParallelCoefficient s x
  T • rotate (R T) k - fohSingleJ R C w s β κ T k -
    fohSingleK R C w s β κ T (w ⨯₃ k) +
    lam • ((1 / 3 : ℝ) • (T^2 • rotate (R T) w + T^3 • rotate (R T) s -
      (2 : ℝ) • fohSingleK R C w s β κ T w))

/-- Actual first and second integral moments obey the endpoint reductions. -/
theorem foh_rotationMoment_boundary_reductions (R : ℝ → SO3) (w s : Vec3)
    (hss : fohDot s s ≠ 0)
    (hR : ∀ t, HasDerivAt (fun u => (R u).val)
      ((R t).val * skew (w + t • s)) t)
    (hR0 : R 0 = 1) (T : ℝ) (x : Vec3) :
    fohRotationMoment R 1 T x =
      fohFirstMoment (fohRotationMap R) (fohRotationMoment R 0) w s
        (fohForceCrossCoefficient s x) (fohForceParallelCoefficient s x) T ∧
    fohRotationMoment R 2 T x =
      fohSecondMoment (fohRotationMap R) (fohRotationMoment R 0)
        (fohRotationMoment R 1) w s (fohForceCrossCoefficient s x)
        (fohForceParallelCoefficient s x) T := by
  have hc : Continuous (fun t => (R t).val) :=
    continuous_iff_continuousAt.mpr (fun t => (hR t).continuousAt)
  have h0 : fohRotationMap R 0 = LinearMap.id := by
    ext y i
    simp [fohRotationMap, hR0]
  have hd (t : ℝ) (_ : t ∈ uIcc 0 T) (y : Vec3) :=
    foh_rotationMap_derivative R _ (hR t) y
  have h₀ (t : ℝ) (_ : t ∈ uIcc 0 T) (y : Vec3) :
      HasDerivAt (fun u => fohRotationMoment R 0 u y) (fohRotationMap R t y) t := by
    simpa [fohRotationMap, rotate] using foh_rotationMoment_derivative R hc 0 t y
  have h₁ (t : ℝ) (_ : t ∈ uIcc 0 T) (y : Vec3) :
      HasDerivAt (fun u => fohRotationMoment R 1 u y) (t • fohRotationMap R t y) t := by
    simpa [fohRotationMap, rotate] using foh_rotationMoment_derivative R hc 1 t y
  have hx : x = s ⨯₃ fohForceCrossCoefficient s x +
      fohForceParallelCoefficient s x • s := foh_force_slope_decomposition s x hss
  constructor
  · rw [foh_rotationMoment_integral R hc]
    simpa only [pow_one, fohRotationMap, rotate, Matrix.toLin'_apply] using
      fohFirstMoment_integral _ _ w s _ x _ T hx h0 (foh_rotationMoment_initial R 0)
        hd h₀ ((continuous_id.smul (hc.matrix_mulVec continuous_const)).intervalIntegrable 0 T)
  · rw [foh_rotationMoment_integral R hc]
    exact fohSecondMoment_integral _ _ _ w s _ x _ T hx
      (foh_rotationMoment_initial R 0) (foh_rotationMoment_initial R 1) hd h₀ h₁
      (((continuous_id.pow 2).smul (hc.matrix_mulVec continuous_const)).intervalIntegrable 0 T)

theorem foh_canonical_slope_dot_ne_zero (C : SO3) (s : Vec3) (β : ℝ)
    (hβ : β ≠ 0) (hs : s = rotate C ![0, 0, β]) : fohDot s s ≠ 0 := by
  have he : fohDot s s = s ⬝ᵥ s := by
    simp [fohDot, dotProduct, Fin.sum_univ_succ, add_assoc]
  rw [he, hs, rotate_dot]
  simpa using mul_ne_zero hβ hβ

section Reconstruction
variable (R : ℝ → SO3) (C : SO3) (w s : Vec3) (δ β κ : ℝ)
    (hβ : β ≠ 0) (hκ : κ ≠ 0)
    (hw : w = rotate C ![κ, 0, δ]) (hs : s = rotate C ![0, 0, β])
    (hR : ∀ t, HasDerivAt (fun u => (R u).val)
      ((R t).val * skew (w + t • s)) t)
    (hR0 : R 0 = 1) {T : ℝ} (hT : 0 ≤ T)
include hβ hκ hw hs hR hR0 hT

theorem foh_singleK_eq (x : Vec3) :
    fohSingleK R C w s β κ T x = fohRotationMoment R 1 T x := by
  rw [(foh_rotationMoment_boundary_reductions R w s
    (foh_canonical_slope_dot_ne_zero C s β hβ hs) hR hR0 T x).1]
  simp only [fohSingleK, fohFirstMoment,
    foh_singleJ_eq R C w s δ β κ hβ hκ hw hs hR hR0 hT]
  rfl

theorem foh_singleL_eq (x : Vec3) :
    fohSingleL R C w s β κ T x = fohRotationMoment R 2 T x := by
  rw [(foh_rotationMoment_boundary_reductions R w s
    (foh_canonical_slope_dot_ne_zero C s β hβ hs) hR hR0 T x).2]
  simp only [fohSingleL, fohSecondMoment, fohCrossMoment, fohParallelMoment,
    foh_singleJ_eq R C w s δ β κ hβ hκ hw hs hR hR0 hT,
    foh_singleK_eq R C w s δ β κ hβ hκ hw hs hR hR0 hT]
  rfl

/-- End-to-end velocity and position reconstruction from the endpoint rotation
and a single genuine constant-input sensitivity. All hypotheses are geometric
data, the physical ODEs, or initial conditions. -/
theorem foh_single_sensitivity_preintegration (v p : ℝ → Vec3) (a b : Vec3)
    (hv : ∀ t, HasDerivAt v (rotate (R t) (a + t • b)) t) (hv0 : v 0 = 0)
    (hp : ∀ t, HasDerivAt p (v t) t) (hp0 : p 0 = 0) :
    (∀ x, fohSingleJ R C w s β κ T x = fohRotationMoment R 0 T x) ∧
    (∀ x, fohSingleK R C w s β κ T x = fohRotationMoment R 1 T x) ∧
    (∀ x, fohSingleL R C w s β κ T x = fohRotationMoment R 2 T x) ∧
    v T = fohSingleJ R C w s β κ T a + fohSingleK R C w s β κ T b ∧
    p T = T • v T - fohSingleK R C w s β κ T a - fohSingleL R C w s β κ T b := by
  have hJ := foh_singleJ_eq R C w s δ β κ hβ hκ hw hs hR hR0 hT
  have hK := foh_singleK_eq R C w s δ β κ hβ hκ hw hs hR hR0 hT
  have hL := foh_singleL_eq R C w s δ β κ hβ hκ hw hs hR hR0 hT
  have hc : Continuous (fun t => (R t).val) :=
    continuous_iff_continuousAt.mpr (fun t => (hR t).continuousAt)
  have hss := foh_canonical_slope_dot_ne_zero C s β hβ hs
  have hb : b = s ⨯₃ fohForceCrossCoefficient s b +
      fohForceParallelCoefficient s b • s := foh_force_slope_decomposition s b hss
  refine ⟨hJ, hK, hL, ?_, ?_⟩
  · rw [hJ, hK]
    exact foh_velocity_moments R v a b hc hv hv0 T
  · rw [hK, hL, foh_velocity_moments R v a b hc hv hv0 T,
      (foh_rotationMoment_boundary_reductions R w s hss hR hR0 T b).2]
    rw [foh_position_moments R v p w s a b _ _ hR hb hv hv0 hp hp0 T]
    exact fohCompactPosition_eq _ _ _ _ _ _ _ _ _ _

end Reconstruction

/-- Noncollinearity constructs all geometric data needed for the single
sensitivity formulas. The conclusion contains no unevaluated force integrals. -/
theorem foh_noncollinear_single_sensitivity_preintegration
    (R : ℝ → SO3) (v p : ℝ → Vec3) (w s a b : Vec3)
    (hcross : s ⨯₃ w ≠ 0)
    (hR : ∀ t, HasDerivAt (fun u => (R u).val)
      ((R t).val * skew (w + t • s)) t)
    (hR0 : R 0 = 1)
    (hv : ∀ t, HasDerivAt v (rotate (R t) (a + t • b)) t) (hv0 : v 0 = 0)
    (hp : ∀ t, HasDerivAt p (v t) t) (hp0 : p 0 = 0)
    {T : ℝ} (hT : 0 ≤ T) :
    ∃ (C : SO3) (δ β κ : ℝ), 0 < β ∧ 0 < κ ∧
      w = rotate C ![κ, 0, δ] ∧ s = rotate C ![0, 0, β] ∧
      HasDerivAt (fun q : ℝ =>
        (fohExactRotation (w + q • rotate C ![1, 0, 0]) s T).val * (R T)⁻¹.val)
        (skew (fohSingleSensitivityColumn R w s (rotate C ![1, 0, 0]) T)) 0 ∧
      v T = fohSingleJ R C w s β κ T a + fohSingleK R C w s β κ T b ∧
      p T = T • v T - fohSingleK R C w s β κ T a -
        fohSingleL R C w s β κ T b := by
  obtain ⟨C, δ, β, κ, hβ, hκ, hw, hs⟩ := foh_canonical_frame_exists w s hcross
  have he := foh_single_sensitivity_preintegration R C w s δ β κ hβ.ne' hκ.ne'
    hw hs hR hR0 hT v p a b hv hv0 hp hp0
  refine ⟨C, δ, β, κ, hβ, hκ, hw, hs, ?_, he.2.2.2⟩
  rw [foh_singleSensitivityColumn_eq R w s _ hR hR0 hT]
  exact (foh_exact_moment_sensitivities R w s hR hR0 hT _).1

end GNC.Magnus
