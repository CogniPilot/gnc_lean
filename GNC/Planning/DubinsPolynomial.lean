import GNC.Dynamics.GravityField
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! Differential geometry of transverse offsets from Dubins arcs and lines.
Nominal distance is not generally arc length of the offset curve. These
identities specify the geometry used by CogniPilot's DubinsPolynomial
evaluator, without assuming compiler correctness or global path optimality.
-/
noncomputable section
open Real
open scoped RealInnerProductSpace
namespace GNC.Planning.DubinsPolynomial
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Exact normalized septic used for zero offset/heading and prescribed
second derivatives at both ends. Physical coefficients multiply by L² and
evaluate at q/L; the numerical planner uses the same Hermite conditions. -/
def seed (a b : ℝ) : Polynomial ℝ :=
  Polynomial.C (a/2)*Polynomial.X^2+
  Polynomial.C (-5*a+5*b/2)*Polynomial.X^4+
  Polynomial.C (10*a-7*b)*Polynomial.X^5+
  Polynomial.C (-15*a/2+13*b/2)*Polynomial.X^6+
  Polynomial.C (2*a-2*b)*Polynomial.X^7

theorem seed_jets (a b : ℝ) :
    (seed a b).eval 0 = 0 ∧ (seed a b).eval 1 = 0 ∧
    (seed a b).derivative.eval 0 = 0 ∧ (seed a b).derivative.eval 1 = 0 ∧
    (seed a b).derivative.derivative.eval 0 = a ∧
    (seed a b).derivative.derivative.eval 1 = b ∧
    (seed a b).derivative.derivative.derivative.eval 0 = 0 ∧
    (seed a b).derivative.derivative.derivative.eval 1 = 0 := by
  norm_num [seed, Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_pow] <;> ring_nf <;> simp

/-- The zero-junction-curvature choice used by the figure eight has an
explicit factorization, so its metric cannot become singular between samples. -/
theorem seed_equal (k u : ℝ) :
    (seed (-k) (-k)).eval u = k*u^2*(1-u)^2*(u^2-u-1/2) := by
  simp [seed]
  ring

theorem seed_regular {u : ℝ} (hu : u ∈ Set.Icc (0:ℝ) 1) (k L : ℝ) :
    1 ≤ 1-k*(L^2*(seed (-k) (-k)).eval u) := by
  rw [seed_equal]
  have hq : u^2-u-1/2 ≤ 0 := by nlinarith [mul_nonneg hu.1 (sub_nonneg.mpr hu.2)]
  have hp := mul_nonpos_of_nonneg_of_nonpos
    (mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg k) (sq_nonneg L))
      (sq_nonneg u)) (sq_nonneg (1-u))) hq
  nlinarith [hp]

def offset (base normal : E) (P : ℝ) : E := base+P • normal
def first (tangent normal : E) (k P P₁ : ℝ) : E :=
  (1-k*P) • tangent+P₁ • normal
def second (tangent normal : E) (k P P₁ P₂ : ℝ) : E :=
  (-2*k*P₁) • tangent+(k*(1-k*P)+P₂) • normal
def third (tangent normal : E) (k P P₁ P₂ P₃ : ℝ) : E :=
  (-3*k*P₂-k^2*(1-k*P)) • tangent+(P₃-3*k^2*P₁) • normal
def fourth (tangent normal : E) (k P P₁ P₂ P₃ P₄ : ℝ) : E :=
  (4*k^3*P₁-4*k*P₃) • tangent+(P₄-6*k^2*P₂-k^3+k^4*P) • normal

theorem offset_derivative {base tangent normal : ℝ → E} {P : ℝ → ℝ}
    {s k P₁ : ℝ} (hb : HasDerivAt base (tangent s) s)
    (hn : HasDerivAt normal (-k • tangent s) s) (hP : HasDerivAt P P₁ s) :
    HasDerivAt (fun x => offset (base x) (normal x) (P x))
      (first (tangent s) (normal s) k (P s) P₁) s := by
  convert hb.add (hP.smul hn) using 1
  dsimp [first]
  module

theorem first_derivative {tangent normal : ℝ → E} {P P₁ : ℝ → ℝ}
    {s k P₂ : ℝ} (ht : HasDerivAt tangent (k • normal s) s)
    (hn : HasDerivAt normal (-k • tangent s) s)
    (hP : HasDerivAt P (P₁ s) s) (hP₁ : HasDerivAt P₁ P₂ s) :
    HasDerivAt (fun x => first (tangent x) (normal x) k (P x) (P₁ x))
      (second (tangent s) (normal s) k (P s) (P₁ s) P₂) s := by
  convert (((hP.const_mul k).const_sub 1).smul ht).add (hP₁.smul hn) using 1
  dsimp [second]
  module

theorem second_derivative {tangent normal : ℝ → E} {P P₁ P₂ : ℝ → ℝ}
    {s k P₃ : ℝ} (ht : HasDerivAt tangent (k • normal s) s)
    (hn : HasDerivAt normal (-k • tangent s) s)
    (hP : HasDerivAt P (P₁ s) s) (hP₁ : HasDerivAt P₁ (P₂ s) s)
    (hP₂ : HasDerivAt P₂ P₃ s) :
    HasDerivAt (fun x => second (tangent x) (normal x) k (P x) (P₁ x) (P₂ x))
      (third (tangent s) (normal s) k (P s) (P₁ s) (P₂ s) P₃) s := by
  convert ((hP₁.const_mul (-2*k)).smul ht).add
    (((((hP.const_mul k).const_sub 1).const_mul k).add hP₂).smul hn) using 1
  dsimp [third]
  module

theorem third_derivative {tangent normal : ℝ → E} {P P₁ P₂ P₃ : ℝ → ℝ}
    {s k P₄ : ℝ} (ht : HasDerivAt tangent (k • normal s) s)
    (hn : HasDerivAt normal (-k • tangent s) s)
    (hP : HasDerivAt P (P₁ s) s) (hP₁ : HasDerivAt P₁ (P₂ s) s)
    (hP₂ : HasDerivAt P₂ (P₃ s) s) (hP₃ : HasDerivAt P₃ P₄ s) :
    HasDerivAt (fun x => third (tangent x) (normal x) k (P x) (P₁ x) (P₂ x) (P₃ x))
      (fourth (tangent s) (normal s) k (P s) (P₁ s) (P₂ s) (P₃ s) P₄) s := by
  convert (((hP₂.const_mul (-3*k)).sub
    (((hP.const_mul k).const_sub 1).const_mul (k^2))).smul ht).add
    ((hP₃.sub (hP₁.const_mul (3*k^2))).smul hn) using 1
  dsimp [fourth]
  module

/-- Metric scale used by the Modelica evaluator. A lower bound on this
quantity is necessary before dividing by it or differentiating its inverse. -/
theorem metric_sq (tangent normal : E) (k P P₁ : ℝ)
    (ht : ‖tangent‖ = 1) (hn : ‖normal‖ = 1) (horth : ⟪tangent,normal⟫ = 0) :
    ‖first tangent normal k P P₁‖^2 = (1-k*P)^2+P₁^2 := by
  rw [first, norm_add_sq_real]
  simp [norm_smul, ht, hn, horth, Real.norm_eq_abs, sq_abs]
  rw [real_inner_smul_left, real_inner_smul_right, horth, mul_zero, mul_zero]

theorem metric_lower (tangent normal : E) (k P P₁ : ℝ)
    (ht : ‖tangent‖ = 1) (hn : ‖normal‖ = 1) (horth : ⟪tangent,normal⟫ = 0)
    (h : 1 ≤ 1-k*P) : 1 ≤ ‖first tangent normal k P P₁‖ := by
  have hm := metric_sq tangent normal k P P₁ ht hn horth
  nlinarith [norm_nonneg (first tangent normal k P P₁), sq_nonneg P₁]

/-- A positive diagonal footprint scaling retains a lower metric bound. -/
theorem diagonal_metric_lower {sx sy m x y : ℝ} (hm : 0 ≤ m)
    (hx : m ≤ sx) (hy : m ≤ sy) (h : 1 ≤ x^2+y^2) :
    m^2 ≤ (sx*x)^2+(sy*y)^2 := by
  have hsx : 0 ≤ sx^2-m^2 := by nlinarith
  have hsy : 0 ≤ sy^2-m^2 := by nlinarith
  nlinarith [mul_nonneg hsx (sq_nonneg x), mul_nonneg hsy (sq_nonneg y),
    mul_nonneg (sq_nonneg m) (sub_nonneg.mpr h)]

def unitTangent (d₁ : E) : E := ‖d₁‖⁻¹ • d₁
def arcSecond (d₁ d₂ : E) : E :=
  (1/‖d₁‖^2) • d₂-(⟪d₁,d₂⟫/‖d₁‖^4) • d₁
def arcThird (d₁ d₂ d₃ : E) : E :=
  (1/‖d₁‖^3) • d₃-(3*⟪d₁,d₂⟫/‖d₁‖^5) • d₂-
    ((⟪d₂,d₂⟫+⟪d₁,d₃⟫)/‖d₁‖^5) • d₁+
    (4*⟪d₁,d₂⟫^2/‖d₁‖^7) • d₁

theorem unitTangent_norm (d₁ : E) (h : d₁ ≠ 0) : ‖unitTangent d₁‖ = 1 := by
  simp [unitTangent, norm_smul, abs_of_pos (norm_pos_iff.mpr h), h]

theorem unitTangent_derivative {d₁ : ℝ → E} {d₂ : E} {s : ℝ}
    (h : HasDerivAt d₁ d₂ s) (hz : d₁ s ≠ 0) :
    HasDerivAt (fun x => unitTangent (d₁ x))
      (‖d₁ s‖ • arcSecond (d₁ s) d₂) s := by
  have hn : ‖d₁ s‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  convert ((Gravity.norm_derivative h hz).inv hn).smul h using 1
  dsimp [arcSecond]
  match_scalars <;> field_simp <;> ring

theorem arcSecond_derivative {d₁ d₂ : ℝ → E} {d₃ : E} {s : ℝ}
    (h₁ : HasDerivAt d₁ (d₂ s) s) (h₂ : HasDerivAt d₂ d₃ s) (hz : d₁ s ≠ 0) :
    HasDerivAt (fun x => arcSecond (d₁ x) (d₂ x))
      (‖d₁ s‖ • arcThird (d₁ s) (d₂ s) d₃) s := by
  have hn : ‖d₁ s‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hs := Gravity.norm_derivative h₁ hz
  have hi := h₁.inner ℝ h₂
  convert (((hasDerivAt_const s (1:ℝ)).div (hs.pow 2) (pow_ne_zero 2 hn)).smul h₂).sub
    ((hi.div (hs.pow 4) (pow_ne_zero 4 hn)).smul h₁) using 1
  dsimp [arcThird]
  match_scalars <;> field_simp <;> ring

theorem time_acceleration {d₁ : ℝ → E} {distance : ℝ → ℝ} {d₂ : E} {t V : ℝ}
    (h₁ : HasDerivAt d₁ d₂ (distance t)) (hz : d₁ (distance t) ≠ 0)
    (hd : HasDerivAt distance (V/‖d₁ (distance t)‖) t) :
    HasDerivAt (fun s => V • unitTangent (d₁ (distance s)))
      (V^2 • arcSecond (d₁ (distance t)) d₂) t := by
  have hn : ‖d₁ (distance t)‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  convert ((unitTangent_derivative h₁ hz).scomp t hd).const_smul V using 1
  simp only [smul_smul]
  congr 1
  field_simp

theorem time_jerk {d₁ d₂ : ℝ → E} {distance : ℝ → ℝ} {d₃ : E} {t V : ℝ}
    (h₁ : HasDerivAt d₁ (d₂ (distance t)) (distance t))
    (h₂ : HasDerivAt d₂ d₃ (distance t)) (hz : d₁ (distance t) ≠ 0)
    (hd : HasDerivAt distance (V/‖d₁ (distance t)‖) t) :
    HasDerivAt (fun s => V^2 • arcSecond (d₁ (distance s)) (d₂ (distance s)))
      (V^3 • arcThird (d₁ (distance t)) (d₂ (distance t)) d₃) t := by
  have hn : ‖d₁ (distance t)‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  convert ((arcSecond_derivative h₁ h₂ hz).scomp t hd).const_smul (V^2) using 1
  simp only [smul_smul]
  congr 1
  field_simp

/-- Constant speed requires nominal-distance rate V/metricScale.
Advancing nominal distance at V would give physical speed V*metricScale. -/
theorem constant_speed {curve : ℝ → E} {distance : ℝ → ℝ} {d₁ : E} {t V : ℝ}
    (hc : HasDerivAt curve d₁ (distance t)) (hd : HasDerivAt distance (V/‖d₁‖) t)
    (hz : d₁ ≠ 0) (hV : 0 ≤ V) :
    HasDerivAt (fun x => curve (distance x)) (V • unitTangent d₁) t ∧
      ‖V • unitTangent d₁‖ = V := by
  constructor
  · convert hc.scomp t hd using 1
    simp only [unitTangent, smul_smul, div_eq_mul_inv]
  · rw [norm_smul, unitTangent_norm d₁ hz, Real.norm_eq_abs, abs_of_nonneg hV, mul_one]

def bank (curvature speed gravity : ℝ) : ℝ := arctan (speed^2*curvature/gravity)
def bankRate (curvature curvatureDistanceDerivative speed gravity : ℝ) : ℝ :=
  speed^3*curvatureDistanceDerivative/(gravity*(1+(speed^2*curvature/gravity)^2))

theorem bank_derivative {curvature : ℝ → ℝ} {t kₛ V g : ℝ} (hg : g ≠ 0)
    (hk : HasDerivAt curvature (V*kₛ) t) :
    HasDerivAt (fun s => bank (curvature s) V g) (bankRate (curvature t) kₛ V g) t := by
  convert ((hk.const_mul (V^2)).div_const g).arctan using 1
  dsimp [bankRate]
  field_simp

end GNC.Planning.DubinsPolynomial
