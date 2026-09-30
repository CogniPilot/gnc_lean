import GNC.Analysis.PolynomialTimeProfile
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! Finite linear-response polynomials with executable residual coefficients.
All coefficients are rational, while time, rates and uncertain features are real.
Zero-prefix checks preserve the power of time in a uniform residual bound.
No existence of an exact response, sampling, or floating arithmetic is assumed. -/
namespace GNC.LinearResponsePolynomial
open PolynomialBounds PolynomialOrder PolynomialTimeProfile Planning.PolynomialKernel Set
open scoped BigOperators

abbrev Coefficients (n m : ℕ) := Fin n → Fin m → List ℚ

def sumPolys (ps : List (List ℚ)) : List ℚ := ps.foldr PolynomialBounds.add []

theorem value_sumPolys (ps : List (List ℚ)) (s : ℝ) :
    value (sumPolys ps) s = (ps.map (fun p => value p s)).sum := by
  induction ps with
  | nil => simp [sumPolys, value, evaluate]
  | cons p ps ih => simpa [sumPolys, value_add] using congrArg (value p s + ·) ih

theorem value_product (p q : List ℚ) (s : ℝ) :
    value (multiply p q) s = value p s * value q s := by
  unfold value
  rw [multiply_map, evaluate_multiply]

/-- The exact coefficients of G(s) P(s) + F(s) - P''(s). -/
def residual {n m : ℕ} (g : Coefficients n n) (p f : Coefficients n m) :
    Coefficients n m := fun i j =>
  subtract (add (sumPolys (List.ofFn (fun k => multiply (g i k) (p k j)))) (f i j))
    (differentiate (differentiate (p i j)))

theorem residual_value {n m : ℕ} (g : Coefficients n n) (p f : Coefficients n m)
    (i : Fin n) (j : Fin m) (s : ℝ) :
    value (residual g p f i j) s =
      (∑ k, value (g i k) s * value (p k j) s) + value (f i j) s -
      value (differentiate (differentiate (p i j))) s := by
  simp [residual, value_subtract, value_add, value_sumPolys, List.map_ofFn,
    List.sum_ofFn, value_product]

/-- Absolute coefficient majorant, weighted by proved feature bounds. -/
def budget {n m : ℕ} (p : Coefficients n m) (σ : Fin m → ℚ) (h : ℚ) : ℚ :=
  ∑ i, ∑ j, bound (p i j) h * σ j

theorem budget_nonneg {n m : ℕ} (p : Coefficients n m) (σ : Fin m → ℚ)
    {h : ℚ} (hh : 0≤h) (hσ : ∀ j, 0≤σ j) : 0≤budget p σ h := by
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    mul_nonneg (bound_nonneg _ hh) (hσ j)

section Vector
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {n m : ℕ}

noncomputable def response (basis : Fin n → E) (p : Coefficients n m)
    (features : Fin m → ℝ) (s : ℝ) : E :=
  ∑ i, ∑ j, (value (p i j) s * features j) • basis i

/-- Full-interval, all-feature bound, not a grid check. -/
theorem response_bound (basis : Fin n → E) (hbasis : ∀ i, ‖basis i‖≤1)
    (p : Coefficients n m) (features : Fin m → ℝ) (σ : Fin m → ℚ)
    (hf : ∀ j, |features j|≤σ j) (k : ℕ) (hz : ∀ i j, zeroPrefix k (p i j))
    {h : ℚ} (hh : 0≤h) {s t : ℝ} (hs : |s|≤h) (ht : t∈Icc (0:ℝ) 1) :
    ‖response basis p features (s*t)‖≤(budget p σ h:ℝ)*t^k := by
  have hσ (j) : (0:ℝ)≤σ j := (abs_nonneg _).trans (hf j)
  unfold response
  calc
    _ ≤ ∑ i, ∑ j, ‖(value (p i j) (s*t)*features j) • basis i‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _)
    _ ≤ ∑ i, ∑ j, ((bound (p i j) h:ℝ)*t^k)*(σ j:ℝ) := by
      apply Finset.sum_le_sum; intro i _
      apply Finset.sum_le_sum; intro j _
      rw [norm_smul, Real.norm_eq_abs, abs_mul]
      calc
        _ ≤ (|value (p i j) (s*t)| *|features j|)*1 :=
          mul_le_mul_of_nonneg_left (hbasis i) (by positivity)
        _ ≤ _ := by
          rw [mul_one]
          exact mul_le_mul (profile_bound _ k (hz i j) hh hs ht) (hf j)
            (abs_nonneg _) (mul_nonneg (by exact_mod_cast bound_nonneg (p i j) hh) (pow_nonneg ht.1 k))
    _ = _ := by simp [budget, Finset.mul_sum, mul_comm, mul_left_comm]

noncomputable def velocity (basis : Fin n → E) (p : Coefficients n m)
    (features : Fin m → ℝ) (rate t : ℝ) : E :=
  rate • response basis (fun i j => differentiate (p i j)) features (rate*t)

noncomputable def acceleration (basis : Fin n → E) (p : Coefficients n m)
    (features : Fin m → ℝ) (rate t : ℝ) : E :=
  rate^2 • response basis (fun i j => differentiate (differentiate (p i j))) features (rate*t)

theorem response_derivative (basis : Fin n → E) (p : Coefficients n m)
    (features : Fin m → ℝ) (rate t : ℝ) :
    HasDerivAt (fun u => response basis p features (rate*u))
      (velocity basis p features rate t) t := by
  have hd (i) (j) := (((value_derivative (p i j) (rate*t)).comp t
    ((hasDerivAt_id t).const_mul rate)).mul_const (features j)).smul_const (basis i)
  convert HasDerivAt.fun_sum (fun i _ => HasDerivAt.fun_sum (fun j _ => hd i j)) using 1
  simp [velocity, response, Finset.smul_sum, smul_smul, mul_comm, mul_left_comm]

theorem velocity_derivative (basis : Fin n → E) (p : Coefficients n m)
    (features : Fin m → ℝ) (rate t : ℝ) :
    HasDerivAt (velocity basis p features rate)
      (acceleration basis p features rate t) t := by
  simpa [velocity, acceleration, smul_smul, pow_two] using
    (response_derivative basis (fun i j => differentiate (p i j)) features rate t).const_smul rate

/-- The checked polynomial residual is exactly the differential defect
of the implemented candidate in any supplied basis. -/
theorem defect_identity (basis : Fin n → E) (p f : Coefficients n m)
    (g : Coefficients n n) (features : Fin m → ℝ) (A : ℝ → E →L[ℝ] E)
    (hA : ∀ s j, A s (basis j) = ∑ i, value (g i j) s • basis i)
    (rate t : ℝ) :
    rate^2 • (A (rate*t) (response basis p features (rate*t)) +
      response basis f features (rate*t)) - acceleration basis p features rate t =
      rate^2 • response basis (residual g p f) features (rate*t) := by
  simp only [acceleration, ← smul_sub]
  congr 1
  simp only [response, map_sum, map_smul, hA, Finset.smul_sum, smul_smul,
    residual_value, sub_mul, add_mul, Finset.sum_mul, sub_smul, add_smul,
    Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_smul]
  congr 2
  conv_lhs => enter [2, k]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro k _
  congr 1
  ring

/-- Combined residual identity and coefficient check. The factor rate^2
is essential when coefficients are in swept angle rather than physical time. -/
theorem defect_bound (basis : Fin n → E) (hbasis : ∀ i, ‖basis i‖≤1)
    (p f : Coefficients n m) (g : Coefficients n n) (features : Fin m → ℝ)
    (A : ℝ → E →L[ℝ] E)
    (hA : ∀ s j, A s (basis j) = ∑ i, value (g i j) s • basis i)
    (σ : Fin m → ℚ) (hf : ∀ j, |features j|≤σ j)
    (k : ℕ) (hz : ∀ i j, zeroPrefix k (residual g p f i j))
    {h : ℚ} (hh : 0≤h) {rate t : ℝ} (hrate : |rate|≤h) (ht : t∈Icc (0:ℝ) 1) :
    ‖rate^2 • (A (rate*t) (response basis p features (rate*t)) +
      response basis f features (rate*t)) - acceleration basis p features rate t‖ ≤
      (rate^2*(budget (residual g p f) σ h:ℝ))*t^k := by
  rw [defect_identity basis p f g features A hA, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg _), mul_assoc]
  exact mul_le_mul_of_nonneg_left
    (response_bound basis hbasis _ features σ hf k hz hh hrate ht) (sq_nonneg _)

end Vector
end GNC.LinearResponsePolynomial
