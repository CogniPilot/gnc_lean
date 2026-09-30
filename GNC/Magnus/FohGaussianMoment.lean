import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# The changing-rate fixed-axis Gaussian moment

The entire Gaussian has a global primitive by Mathlib's complex primitive
theorem. Normalizing that primitive at zero defines the complex error function.
The completed-square formula is proved by differentiating this constructed
primitive and applying the interval fundamental theorem of calculus.

The positive-slope square root is explicitly `exp (-I*pi/4) * sqrt (β/2)`.
These statements concern the mathematical special function; they do not assume
or certify any numerical implementation of the complex error function.
-/

noncomputable section
open Complex Set
namespace GNC.Magnus

theorem foh_gaussian_primitive_exists :
    ∃ E : ℂ → ℂ, E 0 = 0 ∧ ∀ z, HasDerivAt E (Complex.exp (-z^2)) z := by
  have hd : Differentiable ℂ (fun z : ℂ => Complex.exp (-z^2)) := by fun_prop
  obtain ⟨E, h0, hd⟩ := hd.isExactOn_univ.with_val_at 0 0
  exact ⟨E, h0, fun z => hd z (mem_univ z)⟩

/-- The entire Gaussian primitive normalized to vanish at zero. -/
def fohGaussianPrimitive : ℂ → ℂ := foh_gaussian_primitive_exists.choose

@[simp] theorem foh_gaussianPrimitive_zero : fohGaussianPrimitive 0 = 0 :=
  foh_gaussian_primitive_exists.choose_spec.1

theorem foh_gaussianPrimitive_hasDerivAt (z : ℂ) :
    HasDerivAt fohGaussianPrimitive (Complex.exp (-z^2)) z :=
  foh_gaussian_primitive_exists.choose_spec.2 z

/-- The complex error function, defined through its entire Gaussian primitive. -/
def fohComplexErf (z : ℂ) : ℂ :=
  (2 / (Real.sqrt Real.pi : ℂ)) * fohGaussianPrimitive z

@[simp] theorem foh_complexErf_zero : fohComplexErf 0 = 0 := by simp [fohComplexErf]

theorem foh_complexErf_hasDerivAt (z : ℂ) :
    HasDerivAt fohComplexErf
      ((2 / (Real.sqrt Real.pi : ℂ)) * Complex.exp (-z^2)) z :=
  (foh_gaussianPrimitive_hasDerivAt z).const_mul _

/-- Completing the square in the complex Gaussian exponent. -/
theorem foh_gaussian_completed_square (δ β c z : ℂ) (hβ : β ≠ 0)
    (hc : c^2 = -Complex.I * β / 2) :
    -Complex.I * δ^2 / (2*β) - (c*(z + δ/β))^2 =
      Complex.I * (δ*z + β*z^2/2) := by
  rw [mul_pow, hc]
  field_simp
  ring

theorem foh_gaussian_completed_primitive_hasDerivAt (δ β c z : ℂ)
    (hβ : β ≠ 0) (hc : c^2 = -Complex.I * β / 2) :
    HasDerivAt (fun z : ℂ => Complex.exp (-Complex.I*δ^2/(2*β)) / c *
      fohGaussianPrimitive (c*(z + δ/β)))
      (Complex.exp (Complex.I*(δ*z + β*z^2/2))) z := by
  have hc0 : c ≠ 0 := by
    intro h
    have hz : -Complex.I * β / 2 = 0 := by simpa [h] using hc.symm
    have hmul : -Complex.I * β = 0 := (div_eq_zero_iff).mp hz |>.resolve_right (by norm_num)
    exact hβ ((mul_eq_zero.mp hmul).resolve_left (by simp))
  have hh := ((foh_gaussianPrimitive_hasDerivAt (c*(z+δ/β))).comp z
    (((hasDerivAt_id z).add_const (δ/β)).const_mul c)).const_mul
      (Complex.exp (-Complex.I*δ^2/(2*β))/c)
  convert hh using 1
  simp only [mul_one]
  rw [show Complex.exp (-Complex.I*δ^2/(2*β))/c *
      (Complex.exp (-(c*(z+δ/β))^2)*c) =
      Complex.exp (-Complex.I*δ^2/(2*β)) * Complex.exp (-(c*(z+δ/β))^2) by field_simp]
  rw [← Complex.exp_add, ← sub_eq_add_neg,
    foh_gaussian_completed_square δ β c z hβ hc]

/-- The changing-rate scalar moment as a proved Gaussian endpoint formula. -/
theorem foh_gaussian_moment_integral (δ β : ℝ) (c : ℂ) (hβ : β ≠ 0)
    (hc : c^2 = -Complex.I * (β : ℂ) / 2) (T : ℝ) :
    (∫ t in (0 : ℝ)..T, Complex.exp (Complex.I*((δ : ℂ)*t + (β : ℂ)*t^2/2))) =
      Complex.exp (-Complex.I*(δ : ℂ)^2/(2*(β : ℂ))) / c *
        (fohGaussianPrimitive (c*((T : ℂ)+(δ : ℂ)/(β : ℂ))) -
          fohGaussianPrimitive (c*((δ : ℂ)/(β : ℂ)))) := by
  have hbc : (β : ℂ) ≠ 0 := by exact_mod_cast hβ
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t (_ : t ∈ uIcc 0 T) =>
      (foh_gaussian_completed_primitive_hasDerivAt δ β c t hbc hc).comp_ofReal)
    ((show Continuous (fun t : ℝ =>
      Complex.exp (Complex.I*((δ : ℂ)*t + (β : ℂ)*t^2/2))) by fun_prop).intervalIntegrable 0 T)
  simpa only [ofReal_zero, zero_add, mul_sub] using hh

/-- The explicit error-function endpoint expression for the zeroth moment. -/
def fohGaussianF0 (δ β : ℝ) (c : ℂ) (T : ℝ) : ℂ :=
  Complex.exp (-Complex.I*(δ : ℂ)^2/(2*(β : ℂ))) *
    (Real.sqrt Real.pi : ℂ) / (2*c) *
      (fohComplexErf (c*((T : ℂ)+(δ : ℂ)/(β : ℂ))) -
        fohComplexErf (c*((δ : ℂ)/(β : ℂ))))

@[simp] theorem foh_gaussianF0_initial (δ β : ℝ) (c : ℂ) :
    fohGaussianF0 δ β c 0 = 0 := by simp [fohGaussianF0]

theorem foh_gaussianF0_primitive (δ β : ℝ) (c : ℂ) (T : ℝ) :
    fohGaussianF0 δ β c T =
      Complex.exp (-Complex.I*(δ : ℂ)^2/(2*(β : ℂ))) / c *
        (fohGaussianPrimitive (c*((T : ℂ)+(δ : ℂ)/(β : ℂ))) -
          fohGaussianPrimitive (c*((δ : ℂ)/(β : ℂ)))) := by
  have hp : (Real.sqrt Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  by_cases hc : c = 0
  · simp [fohGaussianF0, hc]
  · unfold fohGaussianF0 fohComplexErf
    field_simp

/-- Differentiating the finite error-function expression gives the chirp
integrand. Thus the special-function formula is not an assumed primitive. -/
theorem foh_gaussianF0_hasDerivAt (δ β : ℝ) (c : ℂ) (hβ : β ≠ 0)
    (hc : c^2 = -Complex.I * (β : ℂ) / 2) (t : ℝ) :
    HasDerivAt (fohGaussianF0 δ β c)
      (Complex.exp (Complex.I*((δ : ℂ)*t + (β : ℂ)*t^2/2))) t := by
  have hbc : (β : ℂ) ≠ 0 := by exact_mod_cast hβ
  have hd := ((foh_gaussian_completed_primitive_hasDerivAt δ β c t hbc hc).comp_ofReal).sub_const
    (Complex.exp (-Complex.I*(δ : ℂ)^2/(2*(β : ℂ))) / c *
      fohGaussianPrimitive (c*((δ : ℂ)/(β : ℂ))))
  convert hd using 1
  funext t
  rw [foh_gaussianF0_primitive, mul_sub]

theorem foh_gaussianF0_integral (δ β : ℝ) (c : ℂ) (hβ : β ≠ 0)
    (hc : c^2 = -Complex.I * (β : ℂ) / 2) (T : ℝ) :
    (∫ t in (0 : ℝ)..T, Complex.exp (Complex.I*((δ : ℂ)*t + (β : ℂ)*t^2/2))) =
      fohGaussianF0 δ β c T := by
  rw [foh_gaussianF0_primitive]
  exact foh_gaussian_moment_integral δ β c hβ hc T

/-- The square-root branch used for positive angular acceleration. -/
def fohGaussianRoot (β : ℝ) : ℂ :=
  Complex.exp (-Complex.I * (Real.pi : ℂ) / 4) * (Real.sqrt (β/2) : ℂ)

theorem foh_gaussianRoot_sq {β : ℝ} (hβ : 0 ≤ β) :
    (fohGaussianRoot β)^2 = -Complex.I * (β : ℂ) / 2 := by
  unfold fohGaussianRoot
  rw [mul_pow, ← Complex.exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  have he : (2 : ℂ)*(-Complex.I*(Real.pi : ℂ)/4) = -(Real.pi : ℂ)/2*Complex.I := by ring
  rw [he, Complex.exp_neg_pi_div_two_mul_I]
  have hs : (Real.sqrt (β/2) : ℂ)^2 = (β : ℂ)/2 := by
    norm_cast
    exact Real.sq_sqrt (by positivity)
  rw [hs]
  ring

/-- The positive-slope changing-rate `F₀` formula on its explicit Gaussian
square-root branch. This is an equality with the actual definite integral. -/
theorem foh_positive_slope_F0 (δ β T : ℝ) (hβ : 0 < β) :
    (∫ t in (0 : ℝ)..T, Complex.exp (Complex.I*((δ : ℂ)*t + (β : ℂ)*t^2/2))) =
      fohGaussianF0 δ β (fohGaussianRoot β) T :=
  foh_gaussianF0_integral δ β _ hβ.ne' (foh_gaussianRoot_sq hβ.le) T

end GNC.Magnus
