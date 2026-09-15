import GNC.Analysis.PolynomialBounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Exact integration of executable coefficient lists, with a real integral
specification. Polynomial integration introduces no quadrature error; a
separate bound transfers an approximate integrand to its actual integral.
-/
namespace GNC.PolynomialIntegral
open Planning.PolynomialKernel PolynomialBounds
variable {K : Type*} [Field K] [CharZero K]

def unweight : ℕ → List K → List K
  | _, [] => []
  | n, a :: cs => a / (n+1:ℕ) :: unweight (n+1) cs

def primitive (cs : List K) : List K := 0 :: unweight 0 cs

theorem weighted_unweight (cs : List K) (n : ℕ) :
    weighted (n+1) (unweight n cs) = cs := by
  induction cs generalizing n with
  | nil => rfl
  | cons a cs ih =>
    simp only [unweight, weighted, ih, List.cons.injEq, and_true]
    exact mul_div_cancel₀ a (by exact_mod_cast Nat.succ_ne_zero n)

theorem differentiate_primitive (cs : List K) : differentiate (primitive cs) = cs := by
  exact weighted_unweight cs 0

theorem unweight_map {L : Type*} [Field L] [CharZero L] (f : K →+* L)
    (cs : List K) (n : ℕ) : (unweight n cs).map f = unweight n (cs.map f) := by
  induction cs generalizing n with
  | nil => rfl
  | cons a cs ih => simp [unweight, ih]

theorem primitive_map {L : Type*} [Field L] [CharZero L] (f : K →+* L)
    (cs : List K) : (primitive cs).map f = primitive (cs.map f) := by
  simp [primitive, unweight_map]

def integrate (cs : List K) (a b : K) : K :=
  evaluate (primitive cs) b - evaluate (primitive cs) a

theorem integrate_map {L : Type*} [Field L] [CharZero L] (f : K →+* L)
    (cs : List K) (a b : K) : integrate (cs.map f) (f a) (f b) = f (integrate cs a b) := by
  simp only [integrate, ← primitive_map, evaluate_map, map_sub]

theorem primitive_derivative (cs : List ℝ) (t : ℝ) :
    HasDerivAt (evaluate (primitive cs)) (evaluate cs t) t := by
  simpa only [differentiate_primitive] using evaluate_hasDerivAt (primitive cs) t

theorem evaluate_continuous (cs : List ℝ) : Continuous (evaluate cs) := by
  exact continuous_iff_continuousAt.mpr (fun t => (evaluate_hasDerivAt cs t).continuousAt)

theorem integrate_correct (cs : List ℝ) (a b : ℝ) :
    integrate cs a b = ∫ t in a..b, evaluate cs t := by
  symm
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => primitive_derivative cs t) ((evaluate_continuous cs).intervalIntegrable a b)

theorem rational_integral (cs : List ℚ) (a b : ℚ) :
    (∫ t in (a:ℝ)..(b:ℝ), evaluate (cs.map (Rat.castHom ℝ)) t) =
      ((integrate cs a b : ℚ):ℝ) := by
  rw [← integrate_correct]
  exact integrate_map (Rat.castHom ℝ) cs a b

theorem integral_error (f p : ℝ → ℝ) {a b ε : ℝ} (hab : a ≤ b)
    (hf : IntervalIntegrable f MeasureTheory.volume a b)
    (hp : IntervalIntegrable p MeasureTheory.volume a b)
    (herr : ∀ t ∈ Set.Icc a b, |f t-p t| ≤ ε) :
    |(∫ t in a..b, f t) - (∫ t in a..b, p t)| ≤ (b-a)*ε := by
  rw [← intervalIntegral.integral_sub hf hp]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (fun t ht => show ‖f t-p t‖ ≤ ε by
      rw [Real.norm_eq_abs]
      exact herr t ⟨(Set.uIoc_of_le hab ▸ ht).1.le, (Set.uIoc_of_le hab ▸ ht).2⟩)
  simpa [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab), mul_comm] using h

end GNC.PolynomialIntegral
