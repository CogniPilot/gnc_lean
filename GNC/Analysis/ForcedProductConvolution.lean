import GNC.Analysis.ExponentialConvolution

/-! A zero-initial-data forced mode and the convolution of two such modes.
The formulas include zero frequencies and exact resonances. Keeping the two
forced modes together permits later cancellation of low-order polynomial
terms before evaluation; this module does not certify floating arithmetic.
-/
noncomputable section
set_option autoImplicit false
namespace GNC.ForcedProductConvolution
open ExponentialConvolution

def first (a t : ℂ) : ℂ := moment a 0 0 t

theorem first_of_ne (a t : ℂ) (ha : a ≠ 0) :
    first a t = (Complex.exp (a*t)-1)/a := by
  simp [first, moment, Ne.symm ha]
  field_simp
  ring

@[simp] theorem first_zero_rate (t : ℂ) : first 0 t = t := by
  simp [first, moment]

@[simp] theorem first_initial (a : ℂ) : first a 0 = 0 := by simp [first]

theorem derivative_first (a t : ℂ) :
    HasDerivAt (first a) (a*first a t+1) t := by
  simpa [first, mode] using derivative_moment a 0 t 0

theorem derivative_product (a b t : ℂ) :
    HasDerivAt (fun s => first a s*first b s)
      ((a+b)*(first a t*first b t)+first a t+first b t) t := by
  convert (derivative_first a t).mul (derivative_first b t) using 1
  ring

/-- Every division by a frequency has an exact zero-frequency alternative.
The inner `moment` handles coincident output/source frequencies. -/
def kernel (lam a b t : ℂ) : ℂ :=
  if a = 0 then
    if b = 0 then moment lam 0 2 t
    else (moment lam b 1 t-moment lam 0 1 t)/b
  else if b = 0 then (moment lam a 1 t-moment lam 0 1 t)/a
  else (moment lam (a+b) 0 t-moment lam a 0 t-
    moment lam b 0 t+moment lam 0 0 t)/(a*b)

@[simp] theorem kernel_initial (lam a b : ℂ) : kernel lam a b 0 = 0 := by
  simp [kernel]

/-- The elementary expression actually solves the scalar quadratic-forcing
ODE for every frequency, including all zero and resonant cases. -/
theorem derivative_kernel (lam a b t : ℂ) :
    HasDerivAt (kernel lam a b)
      (lam*kernel lam a b t+first a t*first b t) t := by
  by_cases ha : a = 0
  · subst a
    by_cases hb : b = 0
    · subst b
      have he : kernel lam 0 0 = moment lam 0 2 := by funext s; simp [kernel]
      rw [he]
      simpa [mode, pow_two] using derivative_moment lam 0 t 2
    · have he : kernel lam 0 b = fun s => (moment lam b 1 s-moment lam 0 1 s)/b := by
        funext s; simp [kernel, hb]
      rw [he]
      convert ((derivative_moment lam b t 1).sub
        (derivative_moment lam 0 t 1)).div_const b using 1
      rw [first_zero_rate, first_of_ne b t hb]
      simp only [mode, pow_one, zero_mul, Complex.exp_zero]
      field_simp
      ring
  · by_cases hb : b = 0
    · subst b
      have he : kernel lam a 0 = fun s => (moment lam a 1 s-moment lam 0 1 s)/a := by
        funext s; simp [kernel, ha]
      rw [he]
      convert ((derivative_moment lam a t 1).sub
        (derivative_moment lam 0 t 1)).div_const a using 1
      rw [first_zero_rate, first_of_ne a t ha]
      simp only [mode, pow_one, zero_mul, Complex.exp_zero]
      field_simp
      ring
    · have he : kernel lam a b = fun s =>
          (moment lam (a+b) 0 s-moment lam a 0 s-
            moment lam b 0 s+moment lam 0 0 s)/(a*b) := by
        funext s; simp [kernel, ha, hb]
      rw [he]
      convert (((derivative_moment lam (a+b) t 0).sub
        (derivative_moment lam a t 0)).sub
        (derivative_moment lam b t 0)).add
        (derivative_moment lam 0 t 0) |>.div_const (a*b) using 1
      rw [first_of_ne a t ha, first_of_ne b t hb]
      simp only [mode, pow_zero, one_mul, zero_mul, Complex.exp_zero,
        add_mul, Complex.exp_add]
      field_simp
      ring

end GNC.ForcedProductConvolution
