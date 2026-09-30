import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic

/-! Finite polynomial--trigonometric expressions are closed under multiplication
and definite integration. This is the constructive elementary-function mechanism
behind each fixed-order interaction expansion; it does not assert a finite
expression for an infinite sum. Complex notation abbreviates real sin/cos pairs.
-/
noncomputable section
namespace GNC.Oscillatory
open Complex

def mode (k : ℝ) (t : ℝ) : ℂ := Complex.exp (Complex.I * (k : ℂ) * (t : ℂ))

inductive Polynomial : (ℝ → ℂ) → Prop
  | term (a : ℂ) (k : ℝ) (n : ℕ) :
      Polynomial (fun t => a * (t : ℂ)^n * mode k t)
  | add {f g : ℝ → ℂ} : Polynomial f → Polynomial g → Polynomial (fun t => f t + g t)

theorem mode_hasDerivAt (k t : ℝ) :
    HasDerivAt (mode k) (mode k t * (Complex.I * (k : ℂ))) t := by
  have h := (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (Complex.I * (k : ℂ))
  simpa [mode] using h.cexp

theorem mode_add (k l t : ℝ) : mode (k+l) t = mode k t * mode l t := by
  simp [mode, add_mul, mul_add, Complex.exp_add]

theorem Polynomial.constant (a : ℂ) : Polynomial (fun _ => a) := by
  simpa [mode] using Polynomial.term a 0 0

theorem Polynomial.scale {f : ℝ → ℂ} (hf : Polynomial f) (a : ℂ) :
    Polynomial (fun t => a * f t) := by
  induction hf with
  | term b k n => simpa only [mul_assoc] using Polynomial.term (a*b) k n
  | add hf hg ihf ihg => simpa only [mul_add] using ihf.add ihg

theorem Polynomial.neg {f : ℝ → ℂ} (hf : Polynomial f) : Polynomial (fun t => -f t) := by
  simpa using hf.scale (-1)

theorem Polynomial.sub {f g : ℝ → ℂ} (hf : Polynomial f) (hg : Polynomial g) :
    Polynomial (fun t => f t - g t) := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

theorem Polynomial.mul {f g : ℝ → ℂ} (hf : Polynomial f) (hg : Polynomial g) :
    Polynomial (fun t => f t * g t) := by
  induction hf with
  | term a k n =>
    induction hg with
    | term b l m =>
      convert Polynomial.term (a*b) (k+l) (n+m) using 1
      funext t
      rw [mode_add, pow_add]
      ring
    | add hg hh ihg ihh => simpa only [mul_add] using ihg.add ihh
  | add hf hh ihf ihh => simpa only [add_mul] using ihf.add ihh

theorem Polynomial.continuous {f : ℝ → ℂ} (hf : Polynomial f) : Continuous f := by
  induction hf with
  | term a k n => unfold mode; fun_prop
  | add hf hg ihf ihg => exact ihf.add ihg

/-- Integration-by-parts recurrence. Its depth is the polynomial degree,
not an accuracy-dependent truncation of a transcendental series. -/
def primitive (k : ℝ) : ℕ → ℝ → ℂ
  | 0, t => mode k t / (Complex.I * (k : ℂ))
  | n+1, t => (t : ℂ)^(n+1) * mode k t / (Complex.I * (k : ℂ)) -
      (n+1 : ℂ) / (Complex.I * (k : ℂ)) * primitive k n t

theorem primitive_polynomial (k : ℝ) (n : ℕ) : Polynomial (primitive k n) := by
  induction n with
  | zero =>
    simpa [primitive, div_eq_mul_inv, mul_comm] using
      Polynomial.term ((Complex.I * (k : ℂ))⁻¹) k 0
  | succ n ih =>
    have ht := Polynomial.term ((Complex.I * (k : ℂ))⁻¹) k (n+1)
    have hb := ht.sub (ih.scale ((n+1 : ℂ)/(Complex.I * (k : ℂ))))
    convert hb using 1
    funext t
    simp only [primitive, div_eq_mul_inv]
    ring

theorem primitive_hasDerivAt (k : ℝ) (hk : k ≠ 0) (n : ℕ) (t : ℝ) :
    HasDerivAt (primitive k n) ((t : ℂ)^n * mode k t) t := by
  have hl : Complex.I * (k : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hk)
  induction n with
  | zero =>
    convert (mode_hasDerivAt k t).div_const (Complex.I * (k : ℂ)) using 1
    simp [hl]
  | succ n ih =>
    have h := (((Complex.ofRealCLM.hasDerivAt (x := t)).pow (n+1)).mul
      (mode_hasDerivAt k t)).div_const (Complex.I * (k : ℂ))
    convert h.sub (ih.const_mul ((n+1 : ℂ)/(Complex.I * (k : ℂ)))) using 1
    simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel,
      Complex.ofRealCLM_apply, Complex.ofReal_one, Pi.pow_apply, mul_one]
    field_simp [show (k : ℂ) ≠ 0 by exact_mod_cast hk]
    <;> ring

/-- Every finite oscillatory polynomial has an elementary primitive in the
same class, including zero-frequency resonances. -/
theorem Polynomial.has_primitive {f : ℝ → ℂ} (hf : Polynomial f) :
    ∃ g : ℝ → ℂ, Polynomial g ∧ ∀ t, HasDerivAt g (f t) t := by
  induction hf with
  | term a k n =>
    by_cases hk : k = 0
    · subst k
      refine ⟨fun t => a/(n+1 : ℂ) * (t : ℂ)^(n+1), ?_, ?_⟩
      · simpa [mode] using Polynomial.term (a/(n+1 : ℂ)) 0 (n+1)
      · intro t
        convert ((Complex.ofRealCLM.hasDerivAt (x := t)).pow (n+1)).const_mul
          (a/(n+1 : ℂ)) using 1
        simp only [mode, Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero,
          mul_one, Nat.add_sub_cancel, Complex.ofRealCLM_apply, Complex.ofReal_one]
        have hn : (n+1 : ℂ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero n)
        push_cast
        field_simp
    · exact ⟨fun t => a * primitive k n t, (primitive_polynomial k n).scale a,
        fun t => by simpa only [mul_assoc] using (primitive_hasDerivAt k hk n t).const_mul a⟩
  | add hf hg ihf ihg =>
    obtain ⟨f, hf, hdf⟩ := ihf
    obtain ⟨g, hg, hdg⟩ := ihg
    exact ⟨fun t => f t + g t, hf.add hg, fun t => (hdf t).add (hdg t)⟩

/-- Exact closure under integration, with arbitrary real endpoints. -/
theorem Polynomial.integral {f : ℝ → ℂ} (hf : Polynomial f) (a : ℝ) :
    Polynomial (fun t => ∫ s in a..t, f s) := by
  obtain ⟨g, hg, hdg⟩ := hf.has_primitive
  have he : (fun t => ∫ s in a..t, f s) = (fun t => g t - g a) := by
    funext t
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _ => hdg s) (hf.continuous.intervalIntegrable a t)
  rw [he]
  exact hg.sub (Polynomial.constant (g a))


/-- The complex modes are exactly sine/cosine pairs, not new special functions. -/
theorem mode_eq_sin_cos (k t : ℝ) :
    mode k t = (Real.cos (k*t) : ℂ) + (Real.sin (k*t) : ℂ) * Complex.I := by
  have he : Complex.I * (k : ℂ) * (t : ℂ) = ((k*t : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  simp only [mode, he, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

theorem Polynomial.sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℂ)
    (hf : ∀ i ∈ s, Polynomial (f i)) : Polynomial (fun t => ∑ i ∈ s, f i t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Polynomial.constant 0
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self i s)).add
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

/-- Ordered interaction coefficients, integrated entrywise. -/
def dysonCoefficient {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : ℝ → Matrix ι ι ℂ) (a : ℝ) : ℕ → ℝ → Matrix ι ι ℂ
  | 0, _ => 1
  | n+1, t => fun i j => ∫ s in a..t, (dysonCoefficient B a n s * B s) i j

/-- Every finite matrix Dyson coefficient has a finite sin/cos-polynomial
representation. This is independent of matrix dimension and truncation order. -/
theorem dysonCoefficient_polynomial {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : ℝ → Matrix ι ι ℂ) (a : ℝ)
    (hB : ∀ i j, Polynomial (fun t => B t i j)) (n : ℕ) :
    ∀ i j, Polynomial (fun t => dysonCoefficient B a n t i j) := by
  induction n with
  | zero =>
    intro i j
    exact Polynomial.constant ((1 : Matrix ι ι ℂ) i j)
  | succ n ih =>
    intro i j
    exact (Polynomial.sum Finset.univ
      (fun k t => dysonCoefficient B a n t i k * B t k j)
      (fun k _ => (ih i k).mul (hB k j))).integral a

/-- The constructed elementary coefficients solve the actual coefficient ODE. -/
theorem dysonCoefficient_hasDerivAt {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : ℝ → Matrix ι ι ℂ) (a : ℝ)
    (hB : ∀ i j, Polynomial (fun t => B t i j)) (n : ℕ) (t : ℝ) (i j : ι) :
    HasDerivAt (fun t => dysonCoefficient B a (n+1) t i j)
      ((dysonCoefficient B a n t * B t) i j) t := by
  have hc := (Polynomial.sum Finset.univ
    (fun k t => dysonCoefficient B a n t i k * B t k j)
    (fun k _ => (dysonCoefficient_polynomial B a hB n i k).mul (hB k j))).continuous
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable a t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

end GNC.Oscillatory
