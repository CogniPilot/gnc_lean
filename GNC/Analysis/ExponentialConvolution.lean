import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic

/-! Elementary forced exponential modes, including exact resonance.

`moment lam ν n` solves `y' = lam*y + t^n*exp(ν*t)`, with zero initial data.
Complex time includes oscillatory modes without a separate trigonometric
case. Restriction to real time gives the physical-time formula. This is a
constant-coefficient variation-of-constants identity, not a claim that a
nonlinear vector field has a finite-dimensional exact linear realization.
-/
noncomputable section
set_option autoImplicit false
namespace GNC.ExponentialConvolution

def mode (ν : ℂ) (n : ℕ) (t : ℂ) : ℂ := t^n * Complex.exp (ν*t)

theorem mode_mul (ν μ t : ℂ) (n m : ℕ) :
    mode ν n t * mode μ m t = mode (ν+μ) (n+m) t := by
  simp only [mode, pow_add, add_mul, Complex.exp_add]
  ring

theorem derivative_exp (ν t : ℂ) :
    HasDerivAt (fun s => Complex.exp (ν*s)) (ν*Complex.exp (ν*t)) t := by
  simpa [mul_comm] using ((hasDerivAt_id t).const_mul ν).cexp

theorem derivative_mode_succ (ν t : ℂ) (n : ℕ) :
    HasDerivAt (mode ν (n+1))
      ((n+1 : ℂ)*mode ν n t + ν*mode ν (n+1) t) t := by
  convert ((hasDerivAt_id t).pow (n+1)).mul (derivative_exp ν t) using 1
  simp [mode, pow_succ]
  ring

/-- Recursion terminates in the polynomial degree. The resonance branch is
an equality of mathematical frequencies; it is not a numerical tolerance. -/
def moment (lam ν : ℂ) : ℕ → ℂ → ℂ
  | 0, t => if ν = lam then t*Complex.exp (lam*t)
      else (Complex.exp (ν*t)-Complex.exp (lam*t))/(ν-lam)
  | n+1, t => if ν = lam then mode lam (n+1+1) t/(n+1+1 : ℂ)
      else (mode ν (n+1) t-(n+1 : ℂ)*moment lam ν n t)/(ν-lam)

theorem moment_resonant (lam t : ℂ) (n : ℕ) :
    moment lam lam n t = mode lam (n+1) t/(n+1 : ℂ) := by
  cases n <;> simp [moment, mode]

@[simp] theorem moment_zero (lam ν : ℂ) (n : ℕ) : moment lam ν n 0 = 0 := by
  induction n with
  | zero => simp [moment]
  | succ n ih => simp [moment, mode, ih]

/-- The actual derivative of the elementary formula; no coefficient ODE is
assumed. In particular exact resonance contributes a secular time factor. -/
theorem derivative_moment (lam ν t : ℂ) (n : ℕ) :
    HasDerivAt (moment lam ν n) (lam*moment lam ν n t+mode ν n t) t := by
  by_cases h : ν = lam
  · subst ν
    have he : moment lam lam n = fun s => mode lam (n+1) s/(n+1 : ℂ) :=
      funext (fun s => moment_resonant lam s n)
    rw [he]
    convert (derivative_mode_succ lam t n).div_const (n+1 : ℂ) using 1
    have hn : (n+1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    field_simp
    ring
  · have hd : ν-lam ≠ 0 := sub_ne_zero.mpr h
    induction n with
    | zero =>
      have he : moment lam ν 0 = fun s =>
          (Complex.exp (ν*s)-Complex.exp (lam*s))/(ν-lam) := by
        funext s; simp [moment, h]
      rw [he]
      convert ((derivative_exp ν t).sub (derivative_exp lam t)).div_const (ν-lam) using 1
      simp only [mode, pow_zero, one_mul]
      field_simp
      ring
    | succ n ih =>
      have he : moment lam ν (n+1) = fun s =>
          (mode ν (n+1) s-(n+1 : ℂ)*moment lam ν n s)/(ν-lam) := by
        funext s; simp [moment, h]
      rw [he]
      convert ((derivative_mode_succ ν t n).sub
        (ih.const_mul (n+1 : ℂ))).div_const (ν-lam) using 1
      field_simp
      ring

end GNC.ExponentialConvolution
