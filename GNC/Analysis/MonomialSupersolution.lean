import GNC.Analysis.PolynomialSupersolution

/-! A closed polynomial supersolution for each nonnegative forcing monomial.
The denominator is the second-derivative coefficient of the closing term.
This constructs time-profile envelopes without iteration or an error allowance. -/
noncomputable section
namespace GNC.MonomialSupersolution
open Polynomial Set

def pair (n : ℕ) : ℝ := ((n:ℝ)+1)*((n:ℝ)+2)
def four (n : ℕ) : ℝ := pair n*pair (n+2)
def six (n : ℕ) : ℝ := four n*pair (n+4)

theorem pair_pos (n : ℕ) : 0<pair n := by unfold pair; positivity
theorem four_pos (n : ℕ) : 0<four n := mul_pos (pair_pos n) (pair_pos (n+2))
theorem six_pos (n : ℕ) : 0<six n := mul_pos (four_pos n) (pair_pos (n+4))

theorem closing_coefficient_lower (n : ℕ) : 56 ≤ pair (n+6) := by
  simp only [pair,Nat.cast_add,Nat.cast_ofNat]
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

def polynomial (κ : ℝ) (n : ℕ) : Polynomial ℝ :=
  monomial (n+2) (1/pair n) + monomial (n+4) (κ/four n) +
    monomial (n+6) (κ^2/six n) + monomial (n+8) (κ^3/(six n*(pair (n+6)-κ)))
def value (κ : ℝ) (n : ℕ) (t : ℝ) : ℝ := (polynomial κ n).eval t
def velocity (κ : ℝ) (n : ℕ) (t : ℝ) : ℝ := (polynomial κ n).derivative.eval t
def acceleration (κ : ℝ) (n : ℕ) (t : ℝ) : ℝ := (polynomial κ n).derivative.derivative.eval t

theorem derivative (κ : ℝ) (n : ℕ) (t : ℝ) :
    HasDerivAt (value κ n) (velocity κ n t) t := (polynomial κ n).hasDerivAt t
theorem velocity_derivative (κ : ℝ) (n : ℕ) (t : ℝ) :
    HasDerivAt (velocity κ n) (acceleration κ n t) t := (polynomial κ n).derivative.hasDerivAt t

theorem monomial_second (a t : ℝ) (n : ℕ) :
    ((monomial (n+2) a).derivative.derivative).eval t=a*pair n*t^n := by
  rw [show n+2=(n+1)+1 by omega,derivative_monomial_succ,derivative_monomial_succ]
  simp only [eval_monomial,pair,Nat.cast_add,Nat.cast_one]
  ring

theorem initial (κ : ℝ) (n : ℕ) : value κ n 0=0 ∧ velocity κ n 0=0 := by
  simp [value,velocity,polynomial,derivative_add,eval_monomial]

theorem defect_identity {κ : ℝ} (n : ℕ) (hk : κ<pair (n+6)) (t : ℝ) :
    acceleration κ n t-κ*value κ n t =
      t^n+κ^4/(six n*(pair (n+6)-κ))*t^(n+6)*(1-t^2) := by
  have hp := (pair_pos n).ne'
  have hq := (pair_pos (n+2)).ne'
  have hr := (pair_pos (n+4)).ne'
  have hf := (four_pos n).ne'
  have hs := (six_pos n).ne'
  have hk' : pair (n+6)-κ≠0 := (sub_pos.mpr hk).ne'
  simp only [acceleration,value,polynomial,derivative_add,eval_add]
  rw [monomial_second,monomial_second _ _ (n+2),monomial_second _ _ (n+4),
    monomial_second _ _ (n+6)]
  simp only [eval_monomial,pow_add]
  dsimp only [six,four] at hs hf ⊢
  field_simp
  ring

theorem supersolution {κ t : ℝ} (n : ℕ) (hk : κ<pair (n+6))
    (ht : t ∈ Icc (0:ℝ) 1) : κ*value κ n t+t^n≤acceleration κ n t := by
  have h := defect_identity n hk t
  have hd : 0<six n*(pair (n+6)-κ) := mul_pos (six_pos n) (sub_pos.mpr hk)
  have ht2 : 0≤1-t^2 := sub_nonneg.mpr (pow_le_one₀ ht.1 ht.2)
  have hn : 0≤κ^4/(six n*(pair (n+6)-κ))*t^(n+6)*(1-t^2) :=
    mul_nonneg (mul_nonneg (div_nonneg (by positivity) hd.le)
      (pow_nonneg ht.1 _)) ht2
  linarith

theorem supersolution_of_gain_lt {κ t : ℝ} (n : ℕ) (hk : κ<56)
    (ht : t ∈ Icc (0:ℝ) 1) : κ*value κ n t+t^n≤acceleration κ n t :=
  supersolution n (hk.trans_le (closing_coefficient_lower n)) ht

end GNC.MonomialSupersolution
