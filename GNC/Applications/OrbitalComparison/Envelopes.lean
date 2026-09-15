import GNC.Analysis.SecondOrderEnvelope
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! An exact polynomial supersolution for the 600-second orbital comparison.
Time is tau = t / 600. The gravity-gradient norm bound is 17/20 in these units.
For k = 17/20, the final coefficient is k^3 / (720*(56-k)), chosen so that
P'' - k*P = 1 + k*coefficient*t^6*(1-t^2) >= 1 on [0,1].
There is no truncation tolerance, initial offset, or fitted forcing margin.
-/
noncomputable section
open Polynomial Set
namespace GNC.OrbitalComparison

def shapePolynomial : Polynomial ℝ :=
  C (1/2)*X^2 + C (17/480)*X^4 +
    C (289/288000)*X^6 + C (4913/317664000)*X^8

def shape (t : ℝ) : ℝ := shapePolynomial.eval t
def shapeV (t : ℝ) : ℝ := shapePolynomial.derivative.eval t
def shapeW (t : ℝ) : ℝ := shapePolynomial.derivative.derivative.eval t

theorem shape_derivative (t : ℝ) : HasDerivAt shape (shapeV t) t :=
  shapePolynomial.hasDerivAt t
theorem shapeV_derivative (t : ℝ) : HasDerivAt shapeV (shapeW t) t :=
  shapePolynomial.derivative.hasDerivAt t

theorem shape_initial : shape 0 = 0 ∧ shapeV 0 = 0 := by
  norm_num [shape, shapeV, shapePolynomial, derivative_add, derivative_mul, derivative_pow]

theorem shape_bounds {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    0 ≤ shape t ∧ shape t ≤ shape 1 ∧ 0 ≤ shapeV t ∧ shapeV t ≤ shapeV 1 := by
  have ht0 : 0 ≤ t := ht.1
  simp only [shape, shapeV, shapePolynomial, derivative_add, derivative_mul, derivative_C,
    derivative_pow, derivative_X, eval_add, eval_mul, eval_pow, eval_C, eval_X,
    eval_zero, eval_one, zero_mul, mul_zero, zero_add, add_zero, mul_one]
  constructor
  · positivity
  constructor
  · gcongr <;> first | exact ht.1 | exact ht.2
  constructor
  · positivity
  · gcongr <;> first | exact ht.1 | exact ht.2

theorem shape_defect {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    (17/20:ℝ)*shape t + 1 ≤ shapeW t := by
  have he : shapeW t - (17/20:ℝ)*shape t =
      1 + (83521/6353280000:ℝ)*t^6*(1-t^2) := by
    simp [shape, shapeW, shapePolynomial, derivative_add, derivative_mul, derivative_pow]
    ring
  have hp : 0 ≤ 1-t^2 := sub_nonneg.mpr (pow_le_one₀ ht.1 ht.2)
  have hterm : 0 ≤ (83521/6353280000:ℝ)*t^6*(1-t^2) := by positivity
  linarith

/-- An order limit used only in the proof. No value of epsilon enters the
computed gains or certificate. -/
theorem remove_slack {x y M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ ε : ℝ, 0 < ε → x ≤ y+ε*M) : x ≤ y := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hden : 0 < M+1 := by linarith
  have hfrac : 0 < ε/(M+1) := div_pos hε hden
  have he := div_mul_cancel₀ ε hden.ne'
  have hx := hb (ε/(M+1)) hfrac
  nlinarith

/-- Closed, uniform gains for all prefixes and every nonnegative forcing
budget, including zero. The actual coefficient matrix may vary arbitrarily
with time within its proved norm bound. -/
theorem response_gain {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p v acc : ℝ → E) {T C : ℝ} (hT : T ≤ 1) (hC : 0 ≤ C)
    (hp : Continuous p) (hv : Continuous v)
    (hdp : ∀ t ∈ Icc 0 T, HasDerivAt p (v t) t)
    (hdv : ∀ t ∈ Icc 0 T, HasDerivAt v (acc t) t)
    (hip : p 0 = 0) (hiv : v 0 = 0)
    (ha : ∀ t ∈ Icc 0 T, ‖acc t‖ ≤ (17/20)*‖p t‖+C) :
    ∀ t ∈ Icc 0 T, ‖p t‖ ≤ shape 1*C ∧ ‖v t‖ ≤ shapeV 1*C := by
  intro t ht
  have hb (ε : ℝ) (hε : 0 < ε) :
      ‖p t‖ ≤ shape 1*C+ε*(1+(17/20)*shape 1) ∧
      ‖v t‖ ≤ shapeV 1*C+ε*((17/20)*shapeV 1) := by
    let c := C+(17/20)*ε
    have hc : 0 ≤ c := by dsimp [c]; positivity
    have h := SecondOrderEnvelope.barrier p v acc (fun s => ε+c*shape s)
      (fun s => c*shapeV s) (fun s => c*shapeW s) hp hv hdp hdv
      (fun s => ((shape_derivative s).const_mul c).const_add ε)
      (fun s => (shapeV_derivative s).const_mul c)
      (by simpa only [hip,norm_zero,shape_initial.1,mul_zero,add_zero] using hε)
      (by simp only [hiv,norm_zero,shape_initial.2,mul_zero,le_refl]) (by
        intro s hs hreg
        have hdef := mul_le_mul_of_nonneg_left
          (shape_defect ⟨hs.1,hs.2.trans hT⟩) hc
        have hacc := ha s hs
        dsimp [c] at *
        nlinarith) t ht
    have hs := shape_bounds ⟨ht.1,ht.2.trans hT⟩
    have hsp := mul_le_mul_of_nonneg_left hs.2.1 hc
    have hsv := mul_le_mul_of_nonneg_left hs.2.2.2 hc
    dsimp [c] at *
    constructor <;> nlinarith
  have hs := shape_bounds (show (1:ℝ) ∈ Icc 0 1 by norm_num)
  exact ⟨remove_slack (by nlinarith [hs.1]) (fun ε hε => (hb ε hε).1),
    remove_slack (mul_nonneg (by norm_num) hs.2.2.1) (fun ε hε => (hb ε hε).2)⟩

end GNC.OrbitalComparison
