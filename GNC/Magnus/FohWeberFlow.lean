import GNC.Analysis.SpecialFunctions.Weber
import GNC.Magnus.FohSpinorReduction
import GNC.Magnus.FohQuaternionRotation
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.Complex.RealDeriv

/-! Entire Weber basis for the canonical affine angular-rate equation.
All scalar derivatives and the spinor fundamental matrix are derived from
the convergent Kummer construction. -/
noncomputable section
open Matrix
open scoped Matrix Matrix.Norms.Operator
namespace GNC.Magnus
open GNC.SpecialFunctions

def fohWeberNu (β κ : ℂ) : ℂ := -Complex.I * κ ^ 2 / (4 * β)
def fohWeberZ (α δ β t : ℂ) : ℂ := α * (t + δ / β)
def fohWeberEven (α δ β κ t : ℂ) : ℂ :=
  weberEven (fohWeberNu β κ) (fohWeberZ α δ β t)
def fohWeberEvenPrime (α δ β κ t : ℂ) : ℂ :=
  α * weberEvenPrime (fohWeberNu β κ) (fohWeberZ α δ β t)
def fohWeberOdd (α δ β κ t : ℂ) : ℂ :=
  weberOdd (fohWeberNu β κ) (fohWeberZ α δ β t)
def fohWeberOddPrime (α δ β κ t : ℂ) : ℂ :=
  α * weberOddPrime (fohWeberNu β κ) (fohWeberZ α δ β t)

theorem foh_weberZ_derivative (α δ β t : ℂ) :
    HasDerivAt (fohWeberZ α δ β) α t := by
  simpa [fohWeberZ] using ((hasDerivAt_id t).add_const (δ / β)).const_mul α

theorem foh_weberEven_derivative (α δ β κ t : ℂ) :
    HasDerivAt (fohWeberEven α δ β κ) (fohWeberEvenPrime α δ β κ t) t := by
  convert (weberEven_derivative (fohWeberNu β κ) (fohWeberZ α δ β t)).comp t
    (foh_weberZ_derivative α δ β t) using 1
  exact mul_comm _ _

theorem foh_weberOdd_derivative (α δ β κ t : ℂ) :
    HasDerivAt (fohWeberOdd α δ β κ) (fohWeberOddPrime α δ β κ t) t := by
  convert (weberOdd_derivative (fohWeberNu β κ) (fohWeberZ α δ β t)).comp t
    (foh_weberZ_derivative α δ β t) using 1
  exact mul_comm _ _

theorem foh_weber_coefficient (α δ β κ t : ℂ) (hβ : β ≠ 0)
    (hα : α ^ 2 = Complex.I * β) :
    α ^ 2 * (fohWeberNu β κ + 1 / 2 - (fohWeberZ α δ β t) ^ 2 / 4) =
      ((δ + β * t) ^ 2 + κ ^ 2) / 4 + Complex.I * β / 2 := by
  dsimp [fohWeberNu, fohWeberZ]
  rw [mul_pow, hα]
  field_simp
  linear_combination (norm := ring_nf) 0
  all_goals simp [Complex.I_sq] <;> ring

theorem foh_weberEven_ode (α δ β κ t : ℂ) (hβ : β ≠ 0)
    (hα : α ^ 2 = Complex.I * β) :
    HasDerivAt (fohWeberEvenPrime α δ β κ)
      (-(((δ + β * t) ^ 2 + κ ^ 2) / 4 + Complex.I * β / 2) *
        fohWeberEven α δ β κ t) t := by
  have h := ((weberEven_ode (fohWeberNu β κ) (fohWeberZ α δ β t)).comp t
    (foh_weberZ_derivative α δ β t)).const_mul α
  convert h using 1
  change _ = α * (-(_)*_ * α)
  rw [show α * (-(fohWeberNu β κ + 1 / 2 - fohWeberZ α δ β t ^ 2 / 4) *
      weberEven (fohWeberNu β κ) (fohWeberZ α δ β t) * α) =
      -(α ^ 2 * (fohWeberNu β κ + 1 / 2 - fohWeberZ α δ β t ^ 2 / 4)) *
      weberEven (fohWeberNu β κ) (fohWeberZ α δ β t) by ring]
  rw [foh_weber_coefficient α δ β κ t hβ hα]
  rfl

theorem foh_weberOdd_ode (α δ β κ t : ℂ) (hβ : β ≠ 0)
    (hα : α ^ 2 = Complex.I * β) :
    HasDerivAt (fohWeberOddPrime α δ β κ)
      (-(((δ + β * t) ^ 2 + κ ^ 2) / 4 + Complex.I * β / 2) *
        fohWeberOdd α δ β κ t) t := by
  have h := ((weberOdd_ode (fohWeberNu β κ) (fohWeberZ α δ β t)).comp t
    (foh_weberZ_derivative α δ β t)).const_mul α
  convert h using 1
  change _ = α * (-(_)*_ * α)
  rw [show α * (-(fohWeberNu β κ + 1 / 2 - fohWeberZ α δ β t ^ 2 / 4) *
      weberOdd (fohWeberNu β κ) (fohWeberZ α δ β t) * α) =
      -(α ^ 2 * (fohWeberNu β κ + 1 / 2 - fohWeberZ α δ β t ^ 2 / 4)) *
      weberOdd (fohWeberNu β κ) (fohWeberZ α δ β t) by ring]
  rw [foh_weber_coefficient α δ β κ t hβ hα]
  rfl

def fohSpinorGenerator (δ β κ t : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (-Complex.I / 2) • !![δ + β * t, κ; κ, -(δ + β * t)]

def fohWeberFundamental (α δ β κ t : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![fohWeberEven α δ β κ t, fohWeberOdd α δ β κ t;
    fohSpinorSecond (fohWeberEven α δ β κ) (fohWeberEvenPrime α δ β κ) δ β κ t,
    fohSpinorSecond (fohWeberOdd α δ β κ) (fohWeberOddPrime α δ β κ) δ β κ t]

theorem foh_weber_wronskian (α δ β κ t : ℂ) :
    fohWeberEven α δ β κ t * fohWeberOddPrime α δ β κ t -
      fohWeberEvenPrime α δ β κ t * fohWeberOdd α δ β κ t = α := by
  dsimp [fohWeberEven, fohWeberEvenPrime, fohWeberOdd, fohWeberOddPrime]
  linear_combination α * weber_wronskian (fohWeberNu β κ) (fohWeberZ α δ β t)

theorem foh_weberFundamental_det (α δ β κ t : ℂ) :
    (fohWeberFundamental α δ β κ t).det = 2 * Complex.I * α / κ := by
  calc
    _ = (2 * Complex.I / κ) * (fohWeberEven α δ β κ t * fohWeberOddPrime α δ β κ t -
        fohWeberEvenPrime α δ β κ t * fohWeberOdd α δ β κ t) := by
      simp [fohWeberFundamental, det_fin_two, fohSpinorSecond]
      ring
    _ = _ := by rw [foh_weber_wronskian]; ring

theorem foh_weberFundamental_det_ne_zero (α δ β κ t : ℂ)
    (hβ : β ≠ 0) (hκ : κ ≠ 0) (hα : α ^ 2 = Complex.I * β) :
    (fohWeberFundamental α δ β κ t).det ≠ 0 := by
  have ha : α ≠ 0 := by
    intro hz
    rw [hz, zero_pow (by norm_num)] at hα
    exact mul_ne_zero Complex.I_ne_zero hβ hα.symm
  rw [foh_weberFundamental_det]
  exact div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) ha) hκ

theorem foh_weberFundamental_derivative (α δ β κ t : ℂ)
    (hβ : β ≠ 0) (hκ : κ ≠ 0) (hα : α ^ 2 = Complex.I * β) :
    HasDerivAt (fohWeberFundamental α δ β κ)
      (fohSpinorGenerator δ β κ t * fohWeberFundamental α δ β κ t) t := by
  have he := foh_scalar_to_spinor (fohWeberEven α δ β κ) (fohWeberEvenPrime α δ β κ)
    δ β κ t hκ (foh_weberEven_derivative α δ β κ t) (foh_weberEven_ode α δ β κ t hβ hα)
  have ho := foh_scalar_to_spinor (fohWeberOdd α δ β κ) (fohWeberOddPrime α δ β κ)
    δ β κ t hκ (foh_weberOdd_derivative α δ β κ t) (foh_weberOdd_ode α δ β κ t hβ hα)
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  fin_cases i <;> fin_cases j
  · convert he.1 using 1 <;> simp [fohWeberFundamental, fohSpinorGenerator, mul_apply, Fin.sum_univ_succ] <;> ring
  · convert ho.1 using 1 <;> simp [fohWeberFundamental, fohSpinorGenerator, mul_apply, Fin.sum_univ_succ] <;> ring
  · convert he.2 using 1 <;> simp [fohWeberFundamental, fohSpinorGenerator, mul_apply, Fin.sum_univ_succ] <;> ring
  · convert ho.2 using 1 <;> simp [fohWeberFundamental, fohSpinorGenerator, mul_apply, Fin.sum_univ_succ] <;> ring

def fohWeberRightFlow (α δ β κ t : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (fohWeberFundamental α δ β κ t * (fohWeberFundamental α δ β κ 0)⁻¹).transpose

theorem foh_weberRightFlow_initial (α δ β κ : ℂ)
    (hβ : β ≠ 0) (hκ : κ ≠ 0) (hα : α ^ 2 = Complex.I * β) :
    fohWeberRightFlow α δ β κ 0 = 1 := by
  rw [fohWeberRightFlow, Matrix.mul_nonsing_inv _
    (isUnit_iff_ne_zero.mpr (foh_weberFundamental_det_ne_zero α δ β κ 0 hβ hκ hα))]
  simp

theorem foh_weberRightFlow_derivative (α δ β κ t : ℂ)
    (hβ : β ≠ 0) (hκ : κ ≠ 0) (hα : α ^ 2 = Complex.I * β) :
    HasDerivAt (fohWeberRightFlow α δ β κ)
      (fohWeberRightFlow α δ β κ t * fohSpinorGenerator δ β κ t) t := by
  have hd := (foh_weberFundamental_derivative α δ β κ t hβ hκ hα).mul_const
    (fohWeberFundamental α δ β κ 0)⁻¹
  have ht : HasDerivAt (fohWeberRightFlow α δ β κ)
      ((fohSpinorGenerator δ β κ t * fohWeberFundamental α δ β κ t *
        (fohWeberFundamental α δ β κ 0)⁻¹).transpose) t := by
    apply hasDerivAt_pi.mpr
    intro i
    apply hasDerivAt_pi.mpr
    intro j
    exact hasDerivAt_pi.mp (hasDerivAt_pi.mp hd j) i
  convert ht using 1
  rw [mul_assoc, transpose_mul]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

-- The Lie-algebra imports supply an alternative module instance; this
-- direct continuity proof keeps the real restriction independent of it.
local instance : ContinuousSMul ℝ ℂ := ⟨by
  simpa only [Complex.real_smul] using
    (Complex.continuous_ofReal.comp (continuous_fst : Continuous (fun p : ℝ × ℂ => p.1))).mul continuous_snd⟩

def fohSpinorQuaternionScalar (u : ℝ → ℂ) (t : ℝ) : ℝ := (u t).re
def fohSpinorQuaternionVector (u v : ℝ → ℂ) (t : ℝ) : Vec3 :=
  ![-(v t).im, -(v t).re, -(u t).im]

/-- A single normalized spinor row supplies all four real quaternion
components. Its complex ODE proves the real quaternion ODE directly. -/
theorem foh_spinor_row_quaternion_ode (u v : ℝ → ℂ) (d k t : ℝ)
    (hu : HasDerivAt u (-Complex.I / 2 * ((d : ℂ) * u t + (k : ℂ) * v t)) t)
    (hv : HasDerivAt v (-Complex.I / 2 * ((k : ℂ) * u t - (d : ℂ) * v t)) t) :
    HasDerivAt (fohSpinorQuaternionScalar u)
      (-(fohSpinorQuaternionVector u v t ⬝ᵥ ![k, 0, d]) / 2) t ∧
    HasDerivAt (fohSpinorQuaternionVector u v)
      ((1 / 2 : ℝ) • (fohSpinorQuaternionScalar u t • ![k, 0, d] +
        fohSpinorQuaternionVector u v t ⨯₃ ![k, 0, d])) t := by
  have hur := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hu
  have hui := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hu
  have hvr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hv
  have hvi := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hv
  constructor
  · convert hur using 1
    simp [fohSpinorQuaternionVector, dotProduct, Fin.sum_univ_succ, Complex.mul_re,
      Complex.mul_im, Complex.div_re, Complex.div_im]
    ring
  · apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · convert hvi.neg using 1
      simp [fohSpinorQuaternionScalar, fohSpinorQuaternionVector, cross_apply,
        Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]
      ring
    · convert hvr.neg using 1
      simp [fohSpinorQuaternionScalar, fohSpinorQuaternionVector, cross_apply,
        Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]
      ring
    · convert hui.neg using 1
      simp [fohSpinorQuaternionScalar, fohSpinorQuaternionVector, cross_apply,
        Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]
      ring

def fohWeberU (α : ℂ) (δ β κ t : ℝ) : ℂ := fohWeberRightFlow α δ β κ t 0 0
def fohWeberV (α : ℂ) (δ β κ t : ℝ) : ℂ := fohWeberRightFlow α δ β κ t 0 1

theorem foh_weber_row_derivatives (α : ℂ) (δ β κ t : ℝ)
    (hβ : β ≠ 0) (hκ : κ ≠ 0) (hα : α ^ 2 = Complex.I * (β : ℂ)) :
    HasDerivAt (fohWeberU α δ β κ)
      (-Complex.I / 2 * (((δ + β * t : ℝ) : ℂ) * fohWeberU α δ β κ t +
        (κ : ℂ) * fohWeberV α δ β κ t)) t ∧
    HasDerivAt (fohWeberV α δ β κ)
      (-Complex.I / 2 * ((κ : ℂ) * fohWeberU α δ β κ t -
        ((δ + β * t : ℝ) : ℂ) * fohWeberV α δ β κ t)) t := by
  have hd := foh_weberRightFlow_derivative α δ β κ t
    (by exact_mod_cast hβ) (by exact_mod_cast hκ) hα
  have hu := (hasDerivAt_pi.mp (hasDerivAt_pi.mp hd 0) 0).comp_ofReal
  have hv := (hasDerivAt_pi.mp (hasDerivAt_pi.mp hd 0) 1).comp_ofReal
  constructor
  · convert hu using 1
    simp [fohWeberU, fohWeberV, fohSpinorGenerator, mul_apply, Fin.sum_univ_succ]
    ring
  · convert hv using 1
    simp [fohWeberU, fohWeberV, fohSpinorGenerator, mul_apply, Fin.sum_univ_succ]
    ring

def fohWeberQuaternionScalar (α : ℂ) (δ β κ : ℝ) : ℝ → ℝ :=
  fohSpinorQuaternionScalar (fohWeberU α δ β κ)
def fohWeberQuaternionVector (α : ℂ) (δ β κ : ℝ) : ℝ → Vec3 :=
  fohSpinorQuaternionVector (fohWeberU α δ β κ) (fohWeberV α δ β κ)

theorem foh_weber_quaternion_ode (α : ℂ) (δ β κ t : ℝ)
    (hβ : β ≠ 0) (hκ : κ ≠ 0) (hα : α ^ 2 = Complex.I * (β : ℂ)) :
    HasDerivAt (fohWeberQuaternionScalar α δ β κ)
      (-(fohWeberQuaternionVector α δ β κ t ⬝ᵥ ![κ, 0, δ + β * t]) / 2) t ∧
    HasDerivAt (fohWeberQuaternionVector α δ β κ)
      ((1 / 2 : ℝ) • (fohWeberQuaternionScalar α δ β κ t • ![κ, 0, δ + β * t] +
        fohWeberQuaternionVector α δ β κ t ⨯₃ ![κ, 0, δ + β * t])) t :=
  foh_spinor_row_quaternion_ode (fohWeberU α δ β κ) (fohWeberV α δ β κ) (δ + β * t) κ t
    (foh_weber_row_derivatives α δ β κ t hβ hκ hα).1
    (foh_weber_row_derivatives α δ β κ t hβ hκ hα).2

theorem foh_weber_quaternion_initial (α : ℂ) (δ β κ : ℝ)
    (hβ : β ≠ 0) (hκ : κ ≠ 0) (hα : α ^ 2 = Complex.I * (β : ℂ)) :
    fohWeberQuaternionScalar α δ β κ 0 = 1 ∧ fohWeberQuaternionVector α δ β κ 0 = 0 := by
  have h := foh_weberRightFlow_initial α δ β κ (by exact_mod_cast hβ) (by exact_mod_cast hκ) hα
  constructor
  · simp [fohWeberQuaternionScalar, fohSpinorQuaternionScalar, fohWeberU, h]
  · ext i
    fin_cases i <;>
      simp [fohWeberQuaternionVector, fohSpinorQuaternionVector, fohWeberU, fohWeberV, h]

/-- End-to-end canonical noncommuting FOH rotation: the convergent Weber
construction produces a unit-initialized SO(3) solution of the stated ODE. -/
theorem foh_weber_to_rotation (α : ℂ) (δ β κ : ℝ)
    (hβ : β ≠ 0) (hκ : κ ≠ 0) (hα : α ^ 2 = Complex.I * (β : ℂ)) :
    ∃ R : ℝ → SO3, R 0 = 1 ∧
      (∀ t, (R t).val = fohQuaternionMatrix (fohWeberQuaternionScalar α δ β κ t)
        (fohWeberQuaternionVector α δ β κ t)) ∧
      (∀ t, HasDerivAt (fun s => (R s).val) ((R t).val * skew ![κ, 0, δ + β * t]) t) := by
  exact foh_quaternion_to_rotation
    (fohWeberQuaternionScalar α δ β κ) (fohWeberQuaternionVector α δ β κ)
    (fun t => ![κ, 0, δ + β * t])
    (fun t => (foh_weber_quaternion_ode α δ β κ t hβ hκ hα).1)
    (fun t => (foh_weber_quaternion_ode α δ β κ t hβ hκ hα).2)
    (foh_weber_quaternion_initial α δ β κ hβ hκ hα).1
    (foh_weber_quaternion_initial α δ β κ hβ hκ hα).2

/-- Uniqueness of rotation trajectories is a consequence of their original
ODE: the derivative of the relative rotation vanishes. -/
theorem foh_rotation_ode_unique (R S : ℝ → SO3) (w : ℝ → Vec3)
    (hR : ∀ t, HasDerivAt (fun u => (R u).val) ((R t).val * skew (w t)) t)
    (hS : ∀ t, HasDerivAt (fun u => (S u).val) ((S t).val * skew (w t)) t)
    (h0 : R 0 = S 0) : R = S := by
  have hd (t : ℝ) : HasDerivAt (fun u => (R u).val * ((S u)⁻¹).val) 0 t := by
    convert (hR t).mul (GNC.RotationKinematics.inverse_derivative (hS t)) using 1
    noncomm_ring
  have hc (t : ℝ) : (R t).val * ((S t)⁻¹).val = 1 := by
    have hh := is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt)
      (fun t => (hd t).deriv) t 0
    rw [h0] at hh
    have hz : (S 0).val * ((S 0)⁻¹).val = 1 := by
      change ((S 0) * (S 0)⁻¹).val = 1
      simp
    exact hh.trans hz
  funext t
  apply Subtype.ext
  have hh := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M * (S t).val) (hc t)
  have hi : ((S t)⁻¹).val * (S t).val = 1 := by
    change ((S t)⁻¹ * S t).val = 1
    simp
  simpa only [mul_assoc, hi, mul_one, one_mul] using hh

/-- The explicit Weber expression equals every actual canonical FOH
rotation solution, so the result is a solution formula, not just existence. -/
theorem foh_weber_rotation_formula (R : ℝ → SO3) (α : ℂ) (δ β κ : ℝ)
    (hβ : β ≠ 0) (hκ : κ ≠ 0) (hα : α ^ 2 = Complex.I * (β : ℂ))
    (hR : ∀ t, HasDerivAt (fun u => (R u).val) ((R t).val * skew ![κ, 0, δ + β * t]) t)
    (hR0 : R 0 = 1) (t : ℝ) :
    (R t).val = fohQuaternionMatrix (fohWeberQuaternionScalar α δ β κ t)
      (fohWeberQuaternionVector α δ β κ t) := by
  obtain ⟨S, hs0, hs, hsd⟩ := foh_weber_to_rotation α δ β κ hβ hκ hα
  have he := foh_rotation_ode_unique R S (fun t => ![κ, 0, δ + β * t]) hR hsd
    (hR0.trans hs0.symm)
  rw [he]
  exact hs t

def fohWeberAlpha (β : ℝ) : ℂ := (Real.sqrt (β / 2) : ℂ) * (1 + Complex.I)

theorem foh_weberAlpha_sq {β : ℝ} (hβ : 0 ≤ β) :
    fohWeberAlpha β ^ 2 = Complex.I * (β : ℂ) := by
  have hs := Real.sq_sqrt (show 0 ≤ β / 2 by positivity)
  apply Complex.ext <;> simp [fohWeberAlpha, pow_two, Complex.mul_re, Complex.mul_im]
  simp [Real.sqrt_div] at hs
  nlinarith

/-- A fixed change of axes transports the canonical solution to the
physical affine angular rate. The supplied frame is an actual SO(3) element. -/
theorem foh_conjugate_rotation_derivative (C : SO3) (R : ℝ → SO3) (w : Vec3) {t : ℝ}
    (hR : HasDerivAt (fun u => (R u).val) ((R t).val * skew w) t) :
    HasDerivAt (fun u => (C * R u * C⁻¹).val)
      ((C * R t * C⁻¹).val * skew (rotate C w)) t := by
  have hs := skew_rotate C⁻¹ (rotate C w)
  simp only [← rotate_mul, inv_mul_cancel, rotate_one] at hs
  convert (hR.const_mul C.val).mul_const C⁻¹.val using 1
  change C.val * (R t).val * C⁻¹.val * skew (rotate C w) =
    C.val * ((R t).val * skew w) * C⁻¹.val
  simp only [mul_assoc, ← hs]

theorem foh_weber_rotation_formula_in_frame (R : ℝ → SO3) (C : SO3)
    (w s : Vec3) (δ β κ : ℝ) (hβ : 0 < β) (hκ : κ ≠ 0)
    (hw : w = rotate C ![κ, 0, δ]) (hs : s = rotate C ![0, 0, β])
    (hR : ∀ t, HasDerivAt (fun u => (R u).val) ((R t).val * skew (w + t • s)) t)
    (hR0 : R 0 = 1) (t : ℝ) :
    (R t).val = C.val *
      fohQuaternionMatrix (fohWeberQuaternionScalar (fohWeberAlpha β) δ β κ t)
        (fohWeberQuaternionVector (fohWeberAlpha β) δ β κ t) * C⁻¹.val := by
  obtain ⟨S, hs0, hsf, hsd⟩ := foh_weber_to_rotation (fohWeberAlpha β) δ β κ
    hβ.ne' hκ (foh_weberAlpha_sq hβ.le)
  let Q : ℝ → SO3 := fun t => C * S t * C⁻¹
  have hq (t : ℝ) : HasDerivAt (fun u => (Q u).val) ((Q t).val * skew (w + t • s)) t := by
    have he : w + t • s = rotate C ![κ, 0, δ + β * t] := by
      rw [hw, hs]
      simp only [rotate, ← Matrix.mulVec_smul, ← Matrix.mulVec_add]
      congr 1
      ext i
      fin_cases i <;> simp <;> ring
    rw [he]
    exact foh_conjugate_rotation_derivative C S _ (hsd t)
  have hq0 : Q 0 = 1 := by simp [Q, hs0]
  have he := foh_rotation_ode_unique R Q (fun t => w + t • s) hR hq (hR0.trans hq0.symm)
  rw [he]
  change C.val * (S t).val * C⁻¹.val = _
  rw [hsf]

end GNC.Magnus
