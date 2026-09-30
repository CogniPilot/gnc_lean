import GNC.Analysis.SpecialFunctions.Kummer
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.MeanValue

/-! Normalized even/odd Weber functions constructed from entire Kummer series.
Their differential equation and nonzero Wronskian are proved, not postulated. -/
noncomputable section
namespace GNC.SpecialFunctions

def weberEnvelope (a : ℂ) (b : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (-z^2/4)*kummerJet a b 0 (z^2/2)

def weberEnvelopePrime (a : ℂ) (b : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (-z^2/4)*z*(kummerJet a b 1 (z^2/2)-kummerJet a b 0 (z^2/2)/2)

theorem weberGaussian_derivative (z : ℂ) :
    HasDerivAt (fun z : ℂ => Complex.exp (-z^2/4))
      ((-z/2)*Complex.exp (-z^2/4)) z := by
  convert (((hasDerivAt_pow 2 z).neg.div_const 4).cexp) using 1 <;> simp only [Pi.neg_apply] <;> ring

theorem weberKummer_derivative (a : ℂ) {b : ℝ} (hb : 0 < b) (j : ℕ) (z : ℂ) :
    HasDerivAt (fun z : ℂ => kummerJet a b j (z^2/2))
      (z*kummerJet a b (j+1) (z^2/2)) z := by
  convert (kummerJet_hasDerivAt a hb j (z^2/2)).comp z
    ((hasDerivAt_pow 2 z).div_const 2) using 1 <;> ring

theorem weberEnvelope_derivative (a : ℂ) {b : ℝ} (hb : 0 < b) (z : ℂ) :
    HasDerivAt (weberEnvelope a b) (weberEnvelopePrime a b z) z := by
  convert (weberGaussian_derivative z).mul (weberKummer_derivative a hb 0 z) using 1
  dsimp [weberEnvelopePrime]
  ring

theorem weberEnvelopePrime_derivative (a : ℂ) {b : ℝ} (hb : 0 < b) (z : ℂ) :
    HasDerivAt (weberEnvelopePrime a b)
      (Complex.exp (-z^2/4)*(z^2*kummerJet a b 2 (z^2/2)+
        (1-z^2)*kummerJet a b 1 (z^2/2)+
        (z^2/4-1/2)*kummerJet a b 0 (z^2/2))) z := by
  convert ((weberGaussian_derivative z).mul (hasDerivAt_id z)).mul
    ((weberKummer_derivative a hb 1 z).sub
      ((weberKummer_derivative a hb 0 z).div_const 2)) using 1
  dsimp
  ring

def weberEven (ν z : ℂ) : ℂ := weberEnvelope (-ν/2) (1/2) z
def weberEvenPrime (ν z : ℂ) : ℂ := weberEnvelopePrime (-ν/2) (1/2) z

def weberOdd (ν z : ℂ) : ℂ := z*weberEnvelope ((1-ν)/2) (3/2) z
def weberOddPrime (ν z : ℂ) : ℂ :=
  weberEnvelope ((1-ν)/2) (3/2) z+z*weberEnvelopePrime ((1-ν)/2) (3/2) z

theorem weberEven_derivative (ν z : ℂ) :
    HasDerivAt (weberEven ν) (weberEvenPrime ν z) z :=
  weberEnvelope_derivative (-ν/2) (by norm_num) z

theorem weberEven_ode (ν z : ℂ) :
    HasDerivAt (weberEvenPrime ν) (-(ν+1/2-z^2/4)*weberEven ν z) z := by
  convert weberEnvelopePrime_derivative (-ν/2) (by norm_num : (0:ℝ)<1/2) z using 1
  dsimp [weberEven, weberEnvelope]
  have h := kummer_ode (-ν/2) (by norm_num : (0:ℝ)<1/2) (z^2/2)
  push_cast at h
  linear_combination -2*Complex.exp (-z^2/4)*h

theorem weberOdd_derivative (ν z : ℂ) :
    HasDerivAt (weberOdd ν) (weberOddPrime ν z) z := by
  convert (hasDerivAt_id z).mul
    (weberEnvelope_derivative ((1-ν)/2) (by norm_num : (0:ℝ)<3/2) z) using 1
  dsimp [weberOddPrime]
  ring

theorem weberOdd_ode (ν z : ℂ) :
    HasDerivAt (weberOddPrime ν) (-(ν+1/2-z^2/4)*weberOdd ν z) z := by
  convert (weberEnvelope_derivative ((1-ν)/2) (by norm_num : (0:ℝ)<3/2) z).add
    ((hasDerivAt_id z).mul
      (weberEnvelopePrime_derivative ((1-ν)/2) (by norm_num : (0:ℝ)<3/2) z)) using 1
  dsimp [weberOdd, weberEnvelope, weberEnvelopePrime]
  have h := kummer_ode ((1-ν)/2) (by norm_num : (0:ℝ)<3/2) (z^2/2)
  push_cast at h
  linear_combination -2*z*Complex.exp (-z^2/4)*h

@[simp] theorem weberEven_zero (ν : ℂ) : weberEven ν 0 = 1 := by
  simp [weberEven, weberEnvelope, kummerJet_zero, kummerNumerator]
@[simp] theorem weberEvenPrime_zero (ν : ℂ) : weberEvenPrime ν 0 = 0 := by
  simp [weberEvenPrime, weberEnvelopePrime]
@[simp] theorem weberOdd_zero (ν : ℂ) : weberOdd ν 0 = 0 := by simp [weberOdd]
@[simp] theorem weberOddPrime_zero (ν : ℂ) : weberOddPrime ν 0 = 1 := by
  simp [weberOddPrime, weberEnvelope, kummerJet_zero, kummerNumerator]

/-- Entire independence of the normalized scalar solution pair. -/
theorem weber_wronskian (ν z : ℂ) :
    weberEven ν z*weberOddPrime ν z-weberEvenPrime ν z*weberOdd ν z = 1 := by
  let W := fun z => weberEven ν z*weberOddPrime ν z-weberEvenPrime ν z*weberOdd ν z
  have hd (u : ℂ) : HasDerivAt W 0 u := by
    convert ((weberEven_derivative ν u).mul (weberOdd_ode ν u)).sub
      ((weberEven_ode ν u).mul (weberOdd_derivative ν u)) using 1
    ring
  have h := is_const_of_deriv_eq_zero (fun u => (hd u).differentiableAt)
    (fun u => (hd u).deriv) z 0
  simpa [W] using h

end GNC.SpecialFunctions
