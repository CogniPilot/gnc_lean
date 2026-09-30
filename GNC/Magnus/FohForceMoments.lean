import GNC.Magnus.FohVectorReduction
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Exact reduction of the quadratic force moment to the first two moments.
These statements use the actual rotation ODE; no frozen orientation or
truncated Magnus hypothesis is used. -/
noncomputable section
namespace GNC.Magnus
open Matrix
open scoped Matrix

def fohCrossMoment (R I₀ I₁ : ℝ → Vec3 →ₗ[ℝ] Vec3) (w k : Vec3) (t : ℝ) : Vec3 :=
  t • R t k-I₀ t k-I₁ t (w ⨯₃ k)

def fohParallelMoment (R I₁ : ℝ → Vec3 →ₗ[ℝ] Vec3) (w s : Vec3) (t : ℝ) : Vec3 :=
  (1/3:ℝ) • (t^2 • R t w+t^3 • R t s-(2:ℝ) • I₁ t w)

set_option maxHeartbeats 2000000 in
theorem fohCrossMoment_derivative
    (R I₀ I₁ : ℝ → Vec3 →ₗ[ℝ] Vec3) (w s k : Vec3) (t : ℝ)
    (hR : ∀ x, HasDerivAt (fun u => R u x) (R t ((w+t • s) ⨯₃ x)) t)
    (h₀ : ∀ x, HasDerivAt (fun u => I₀ u x) (R t x) t)
    (h₁ : ∀ x, HasDerivAt (fun u => I₁ u x) (t • R t x) t) :
    HasDerivAt (fohCrossMoment R I₀ I₁ w k) (t^2 • R t (s ⨯₃ k)) t := by
  have h := (((hasDerivAt_id t).smul (hR k)).sub (h₀ k)).sub (h₁ (w ⨯₃ k))
  convert h using 1
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, id_eq, one_smul]
  module

set_option maxHeartbeats 2000000 in
theorem fohParallelMoment_derivative
    (R I₁ : ℝ → Vec3 →ₗ[ℝ] Vec3) (w s : Vec3) (t : ℝ)
    (hR : ∀ x, HasDerivAt (fun u => R u x) (R t ((w+t • s) ⨯₃ x)) t)
    (h₁ : ∀ x, HasDerivAt (fun u => I₁ u x) (t • R t x) t) :
    HasDerivAt (fohParallelMoment R I₁ w s) (t^2 • R t s) t := by
  have h := (((hasDerivAt_id t).pow 2).smul (hR w)).add
    (((hasDerivAt_id t).pow 3).smul (hR s))
  have hh := (h.sub ((h₁ w).const_smul (2:ℝ))).const_smul (1/3:ℝ)
  convert hh using 1
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, id_eq, one_smul,
    cross_self, map_zero, smul_zero, add_zero, zero_add]
  rw [← cross_anticomm w s]
  simp only [map_neg]
  norm_num
  module

/-- Decompose any force slope into a cross component and a component along
angular acceleration. This permits exact reduction of its second time moment. -/
theorem foh_force_slope_decomposition (s b : Vec3) (hs : fohDot s s ≠ 0) :
    b = s ⨯₃ (-(fohDot s s)⁻¹ • (s ⨯₃ b)) +
      (fohDot b s / fohDot s s) • s := by
  ext i
  fin_cases i <;> simp [cross_apply, Matrix.vecHead, Matrix.vecTail,
    Pi.smul_apply, Pi.add_apply, smul_eq_mul] <;>
    field_simp [hs] <;> simp only [fohDot] <;> ring


/-- Exact second force moment assembled from first moments. -/
def fohSecondMoment (R I₀ I₁ : ℝ → Vec3 →ₗ[ℝ] Vec3)
    (w s k : Vec3) (lam t : ℝ) : Vec3 :=
  fohCrossMoment R I₀ I₁ w k t + lam • fohParallelMoment R I₁ w s t

theorem fohSecondMoment_derivative
    (R I₀ I₁ : ℝ → Vec3 →ₗ[ℝ] Vec3) (w s k b : Vec3) (lam t : ℝ)
    (hb : b = s ⨯₃ k + lam • s)
    (hR : ∀ x, HasDerivAt (fun u => R u x) (R t ((w+t • s) ⨯₃ x)) t)
    (h₀ : ∀ x, HasDerivAt (fun u => I₀ u x) (R t x) t)
    (h₁ : ∀ x, HasDerivAt (fun u => I₁ u x) (t • R t x) t) :
    HasDerivAt (fohSecondMoment R I₀ I₁ w s k lam) (t^2 • R t b) t := by
  have h := (fohCrossMoment_derivative R I₀ I₁ w s k t hR h₀ h₁).add
    ((fohParallelMoment_derivative R I₁ w s t hR h₁).const_smul lam)
  convert h using 1
  rw [hb]
  simp only [map_add, map_smul, smul_add, smul_smul]
  module

/-- The candidate moment equals an actual definite integral, not an assumed error. -/
theorem fohSecondMoment_integral
    (R I₀ I₁ : ℝ → Vec3 →ₗ[ℝ] Vec3) (w s k b : Vec3) (lam T : ℝ)
    (hb : b = s ⨯₃ k + lam • s) (h00 : I₀ 0 = 0) (h10 : I₁ 0 = 0)
    (hR : ∀ t ∈ Set.uIcc 0 T, ∀ x,
      HasDerivAt (fun u => R u x) (R t ((w+t • s) ⨯₃ x)) t)
    (h₀ : ∀ t ∈ Set.uIcc 0 T, ∀ x, HasDerivAt (fun u => I₀ u x) (R t x) t)
    (h₁ : ∀ t ∈ Set.uIcc 0 T, ∀ x, HasDerivAt (fun u => I₁ u x) (t • R t x) t)
    (hi : IntervalIntegrable (fun t => t^2 • R t b) MeasureTheory.volume 0 T) :
    ∫ t in (0:ℝ)..T, t^2 • R t b = fohSecondMoment R I₀ I₁ w s k lam T := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => fohSecondMoment_derivative R I₀ I₁ w s k b lam t hb
      (hR t ht) (h₀ t ht) (h₁ t ht)) hi
  simpa [fohSecondMoment, fohCrossMoment, fohParallelMoment, h00, h10] using h

/-- Position expression with two linear-input responses in total, including velocity. -/
def fohCompactPosition (R I₀ I₁ : ℝ → Vec3 →ₗ[ℝ] Vec3)
    (w s a b k : Vec3) (lam t : ℝ) : Vec3 :=
  t • (I₀ t a + I₁ t b) - t • R t k - (lam*t^2/3) • R t (w+t • s) +
    I₀ t k + I₁ t (w ⨯₃ k-a+(2*lam/3) • w)

/-- Formal expression-graph reduction: five response evaluations collapse to two. -/
theorem fohCompactPosition_eq
    (R I₀ I₁ : ℝ → Vec3 →ₗ[ℝ] Vec3) (w s a b k : Vec3) (lam t : ℝ) :
    fohCompactPosition R I₀ I₁ w s a b k lam t =
      t • (I₀ t a+I₁ t b)-I₁ t a-fohSecondMoment R I₀ I₁ w s k lam t := by
  simp only [fohCompactPosition, fohSecondMoment, fohCrossMoment, fohParallelMoment,
    map_add, map_sub, map_smul, smul_add, smul_sub, smul_smul]
  module

/-- The compact position solves the full position ODE exactly for affine force. -/
theorem fohCompactPosition_derivative
    (R I₀ I₁ : ℝ → Vec3 →ₗ[ℝ] Vec3) (w s a b k : Vec3) (lam t : ℝ)
    (hb : b = s ⨯₃ k+lam • s)
    (hR : ∀ x, HasDerivAt (fun u => R u x) (R t ((w+t • s) ⨯₃ x)) t)
    (h₀ : ∀ x, HasDerivAt (fun u => I₀ u x) (R t x) t)
    (h₁ : ∀ x, HasDerivAt (fun u => I₁ u x) (t • R t x) t) :
    HasDerivAt (fohCompactPosition R I₀ I₁ w s a b k lam) (I₀ t a+I₁ t b) t := by
  have h := (((hasDerivAt_id t).smul ((h₀ a).add (h₁ b))).sub (h₁ a)).sub
    (fohSecondMoment_derivative R I₀ I₁ w s k b lam t hb hR h₀ h₁)
  have heq : fohCompactPosition R I₀ I₁ w s a b k lam =
      fun u => u • (I₀ u a+I₁ u b)-I₁ u a-fohSecondMoment R I₀ I₁ w s k lam u := by
    funext u
    exact fohCompactPosition_eq R I₀ I₁ w s a b k lam u
  rw [heq]
  convert h using 1
  simp only [smul_add, smul_smul, id_eq, one_smul, Pi.add_apply]
  module


/-- The angular-acceleration column of the integrated rotation is an endpoint difference. -/
theorem foh_slope_endpoint_derivative
    (R : ℝ → Vec3 →ₗ[ℝ] Vec3) (w s : Vec3) (t : ℝ)
    (hR : ∀ x, HasDerivAt (fun u => R u x) (R t ((w+t • s) ⨯₃ x)) t) :
    HasDerivAt (fun u => R u w+u • R u s-w) (R t s) t := by
  have h := ((hR w).add ((hasDerivAt_id t).smul (hR s))).sub_const w
  convert h using 1
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    cross_self, smul_zero, add_zero, zero_add, map_zero, id_eq, one_smul]
  rw [← cross_anticomm w s]
  simp only [map_neg]
  module

/-- The cross-axis column is also an endpoint difference; no sensitivity is needed. -/
theorem foh_cross_endpoint_derivative
    (R : ℝ → Vec3 →ₗ[ℝ] Vec3) (w s : Vec3) (t : ℝ)
    (hR : ∀ x, HasDerivAt (fun u => R u x) (R t ((w+t • s) ⨯₃ x)) t) :
    HasDerivAt (fun u => s-R u s) (R t (s ⨯₃ w)) t := by
  convert (hR s).const_sub s using 1
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    cross_self, smul_zero, add_zero]
  rw [← cross_anticomm w s]
  simp only [map_neg]

/-- First force moment using only the integrated rotation and endpoint rotation. -/
def fohFirstMoment (R I₀ : ℝ → Vec3 →ₗ[ℝ] Vec3)
    (w s k : Vec3) (lam t : ℝ) : Vec3 :=
  R t k-k-I₀ t (w ⨯₃ k)+(lam/2) • (t • R t w+t^2 • R t s-I₀ t w)

set_option maxHeartbeats 2000000 in
theorem fohFirstMoment_derivative
    (R I₀ : ℝ → Vec3 →ₗ[ℝ] Vec3) (w s k x : Vec3) (lam t : ℝ)
    (hx : x = s ⨯₃ k+lam • s)
    (hR : ∀ x, HasDerivAt (fun u => R u x) (R t ((w+t • s) ⨯₃ x)) t)
    (h₀ : ∀ x, HasDerivAt (fun u => I₀ u x) (R t x) t) :
    HasDerivAt (fohFirstMoment R I₀ w s k lam) (t • R t x) t := by
  have h1 := ((hR k).sub_const k).sub (h₀ (w ⨯₃ k))
  have h2 := ((((hasDerivAt_id t).smul (hR w)).add
    (((hasDerivAt_id t).pow 2).smul (hR s))).sub (h₀ w)).const_smul (lam/2)
  convert h1.add h2 using 1
  rw [hx]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    cross_self, smul_zero, add_zero, zero_add, map_zero, id_eq, one_smul]
  rw [← cross_anticomm w s]
  simp only [map_neg]
  norm_num
  module

/-- Once two columns are known from endpoint identities, a single remaining
column determines the entire integrated rotation. This is exact linear algebra. -/
theorem foh_one_column_reconstruction
    (J : Vec3 →ₗ[ℝ] Vec3) (ex ey ez mx my mz x : Vec3)
    (a b c : ℝ) (hx : x = a • ex+b • ey+c • ez)
    (h1 : J ex = mx) (h2 : J ey = my) (h3 : J ez = mz) :
    J x = a • mx+b • my+c • mz := by
  rw [hx]
  simp only [map_add, map_smul, h1, h2, h3]


/-- Endpoint reconstruction of the angular-slope column as an actual integral. -/
theorem foh_slope_endpoint_integral
    (R : ℝ → Vec3 →ₗ[ℝ] Vec3) (w s : Vec3) (T : ℝ)
    (h0 : R 0 = LinearMap.id)
    (hR : ∀ t ∈ Set.uIcc 0 T, ∀ x,
      HasDerivAt (fun u => R u x) (R t ((w+t • s) ⨯₃ x)) t)
    (hi : IntervalIntegrable (fun t => R t s) MeasureTheory.volume 0 T) :
    ∫ t in (0:ℝ)..T, R t s = R T (w+T • s)-w := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => foh_slope_endpoint_derivative R w s t (hR t ht)) hi
  simpa [h0, map_add, map_smul] using h

/-- Endpoint reconstruction of the cross-axis column as an actual integral. -/
theorem foh_cross_endpoint_integral
    (R : ℝ → Vec3 →ₗ[ℝ] Vec3) (w s : Vec3) (T : ℝ)
    (h0 : R 0 = LinearMap.id)
    (hR : ∀ t ∈ Set.uIcc 0 T, ∀ x,
      HasDerivAt (fun u => R u x) (R t ((w+t • s) ⨯₃ x)) t)
    (hi : IntervalIntegrable (fun t => R t (s ⨯₃ w)) MeasureTheory.volume 0 T) :
    ∫ t in (0:ℝ)..T, R t (s ⨯₃ w) = s-R T s := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => foh_cross_endpoint_derivative R w s t (hR t ht)) hi
  simpa [h0] using h

/-- The first moment reconstruction equals the exact weighted integral. -/
theorem fohFirstMoment_integral
    (R I₀ : ℝ → Vec3 →ₗ[ℝ] Vec3) (w s k x : Vec3) (lam T : ℝ)
    (hx : x = s ⨯₃ k+lam • s) (h0 : R 0 = LinearMap.id) (h00 : I₀ 0 = 0)
    (hR : ∀ t ∈ Set.uIcc 0 T, ∀ x,
      HasDerivAt (fun u => R u x) (R t ((w+t • s) ⨯₃ x)) t)
    (h₀ : ∀ t ∈ Set.uIcc 0 T, ∀ x, HasDerivAt (fun u => I₀ u x) (R t x) t)
    (hi : IntervalIntegrable (fun t => t • R t x) MeasureTheory.volume 0 T) :
    ∫ t in (0:ℝ)..T, t • R t x = fohFirstMoment R I₀ w s k lam T := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => fohFirstMoment_derivative R I₀ w s k x lam t hx
      (hR t ht) (h₀ t ht)) hi
  simpa [fohFirstMoment, h0, h00] using h

theorem fohCompactPosition_initial
    (R I₀ I₁ : ℝ → Vec3 →ₗ[ℝ] Vec3) (w s a b k : Vec3) (lam : ℝ)
    (h00 : I₀ 0 = 0) (h10 : I₁ 0 = 0) :
    fohCompactPosition R I₀ I₁ w s a b k lam 0 = 0 := by
  simp [fohCompactPosition, h00, h10]

end GNC.Magnus



