import GNC.Analysis.LinearResponsePolynomial
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema

/-! Certified anchored, parity-preserving compression of a degree-eight
polynomial to degree seven. The omitted function is a scaled Chebyshev
polynomial, not a Taylor tail. Its zero value and slope at zero preserve
the initial position and velocity. An existing physical certificate can
therefore be transferred by a uniform output bound.
-/
namespace GNC.ChebyshevCompression
open PolynomialBounds PolynomialOrder Planning.PolynomialKernel
open LinearResponsePolynomial

def annihilator (h : ℚ) : List ℚ :=
  [0,0,-h^6/32,0,9*h^4/16,0,-3*h^2/2,0,1]

def annihilator7 (h : ℚ) : List ℚ := [0,0,0,h^4/8,0,-h^2,0,1]

def compress (k : ℕ) (w p : List ℚ) : List ℚ :=
  subtract p (scale (p.getD k 0) w)

theorem value_annihilator (h : ℚ) (s : ℝ) :
    value (annihilator h) s=
      s^8-(3/2:ℝ)*(h:ℝ)^2*s^6+(9/16:ℝ)*(h:ℝ)^4*s^4-(h:ℝ)^6*s^2/32 := by
  simp [annihilator, value, evaluate]
  ring

theorem value_compress (k : ℕ) (w p : List ℚ) (s : ℝ) :
    value (compress k w p) s=value p s-(p.getD k 0:ℝ)*value w s := by
  simp [compress, value_subtract, value_scale]

/-- Mathlib supplies the Chebyshev extremum theorem; no trigonometric
inequality is rederived locally. The factor 32 follows from T3's leading
coefficient and the affine change of variable. -/
theorem annihilator_bound {h : ℚ} (hh : 0<h) {s : ℝ} (hs : |s|≤(h:ℝ)) :
    |value (annihilator h) s|≤(h:ℝ)^8/32 := by
  have hr : (0:ℝ)<h := by exact_mod_cast hh
  have hs2 : s^2≤(h:ℝ)^2 := (sq_le_sq).mpr (by simpa [abs_of_pos hr] using hs)
  have hx : |2*s^2/(h:ℝ)^2-1|≤1 := by
    apply abs_le.mpr
    constructor
    · have : 0≤2*s^2/(h:ℝ)^2 := by positivity
      linarith
    · have := (div_le_iff₀ (sq_pos_of_pos hr)).mpr
        (show 2*s^2≤2*(h:ℝ)^2 by linarith)
      linarith
  have hc := Polynomial.Chebyshev.abs_eval_T_real_le_one 3 hx
  have he : value (annihilator h) s=
      ((h:ℝ)^6*s^2/32)*(Polynomial.Chebyshev.T ℝ 3).eval
        (2*s^2/(h:ℝ)^2-1) := by
    rw [value_annihilator]
    rw [show (3:ℤ)=1+2 by norm_num, Polynomial.Chebyshev.T_add_two]
    simp [Polynomial.Chebyshev.T_two, Polynomial.Chebyshev.T_one]
    field_simp
    <;> ring
  rw [he, abs_mul, abs_of_nonneg (by positivity : 0≤(h:ℝ)^6*s^2/32)]
  calc
    _ ≤ ((h:ℝ)^6*s^2/32)*1 := mul_le_mul_of_nonneg_left hc (by positivity)
    _ ≤ (h:ℝ)^8/32 := by nlinarith [mul_le_mul_of_nonneg_left hs2 (pow_nonneg hr.le 6)]

/-- The odd-degree reduction uses s^3 T2, preserving parity and the zero
initial position and velocity. -/
theorem annihilator7_bound {h : ℚ} (hh : 0<h) {s : ℝ}
    (hs0 : 0≤s) (hs : s≤(h:ℝ)) :
    |value (annihilator7 h) s|≤(h:ℝ)^7/8 := by
  have hr : (0:ℝ)<h := by exact_mod_cast hh
  have hs2 : s^2≤(h:ℝ)^2 := pow_le_pow_left₀ hs0 hs 2
  have hx : |2*s^2/(h:ℝ)^2-1|≤1 := by
    apply abs_le.mpr
    constructor
    · have : 0≤2*s^2/(h:ℝ)^2 := by positivity
      linarith
    · have := (div_le_iff₀ (sq_pos_of_pos hr)).mpr
        (show 2*s^2≤2*(h:ℝ)^2 by linarith)
      linarith
  have hc := Polynomial.Chebyshev.abs_eval_T_real_le_one 2 hx
  have he : value (annihilator7 h) s=
      ((h:ℝ)^4*s^3/8)*(Polynomial.Chebyshev.T ℝ 2).eval
        (2*s^2/(h:ℝ)^2-1) := by
    simp [annihilator7, value, evaluate, Polynomial.Chebyshev.T_two]
    field_simp
    <;> ring
  rw [he, abs_mul, abs_of_nonneg (by positivity : 0≤(h:ℝ)^4*s^3/8)]
  calc
    _ ≤ ((h:ℝ)^4*s^3/8)*1 := mul_le_mul_of_nonneg_left hc (by positivity)
    _ ≤ (h:ℝ)^7/8 := by
      have := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs0 hs 3) (pow_nonneg hr.le 4)
      nlinarith

section Vector
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n m : ℕ}

def loss (p : Coefficients n m) (σ : Fin m → ℚ) (k : ℕ) (B : ℚ) : ℚ :=
  ∑ i, ∑ j, |(p i j).getD k 0| * σ j*B

theorem response_difference_bound (basis : Fin n → E) (hb : ∀ i, ‖basis i‖≤1)
    (p : Coefficients n m) (features : Fin m → ℝ) (σ : Fin m → ℚ)
    (hf : ∀ j, |features j|≤(σ j:ℝ)) (k : ℕ) (w : List ℚ) {B : ℚ}
    {s : ℝ} (hw : |value w s|≤(B:ℝ)) :
    ‖response basis p features s-
      response basis (fun i j => compress k w (p i j)) features s‖≤(loss p σ k B:ℝ) := by
  have hB : (0:ℝ)≤B := (abs_nonneg _).trans hw
  have he : response basis p features s-
      response basis (fun i j => compress k w (p i j)) features s=
      ∑ i, ∑ j, (((p i j).getD k 0:ℝ)*value w s*features j) • basis i := by
    simp only [response, value_compress, sub_mul, sub_smul, Finset.sum_sub_distrib]
    abel
  rw [he]
  calc
    _ ≤ ∑ i, ∑ j, ‖(((p i j).getD k 0:ℝ)*value w s*features j) • basis i‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _)
    _ ≤ ∑ i, ∑ j, |((p i j).getD k 0:ℝ)| * (σ j:ℝ)*(B:ℝ) := by
      apply Finset.sum_le_sum; intro i _
      apply Finset.sum_le_sum; intro j _
      rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_mul]
      have hσ : (0:ℝ)≤σ j := (abs_nonneg _).trans (hf j)
      calc
        _ ≤ (|((p i j).getD k 0:ℝ)| * (B:ℝ)*(σ j:ℝ))*1 :=
          mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hw (abs_nonneg _))
            (hf j) (abs_nonneg _) (by positivity)) (hb i) (norm_nonneg _) (by positivity)
        _ = _ := by ring
    _ = _ := by simp [loss]

end Vector
end GNC.ChebyshevCompression
