import GNC.Applications.OrbitalComparison.SpinningOrbitNormal
import GNC.Analysis.QuarticHarmonicResponse

/-! A fair refinement of the classical comparator: 32 rate cells, each
with five coefficient responses and a degree-four uncertainty polynomial.
All source tails and nonlinear gravity are charged. The endpoint query's
coefficients are mathematical ODE responses, not certified floating data.
-/
noncomputable section
namespace GNC.OrbitalComparison.SpinningOrbitRefinement
open SpinningOrbit SpinningOrbitNormal Set Real

def halfwidth : ℝ := 3/8
def center (i : Fin 32) : ℝ := 108+(3/4)*((i:ℕ)+(1/2:ℝ))
def forcingBudget : ℝ := QuarticHarmonicResponse.sourceBudget halfwidth
def approximationError : ℝ := forcingBudget*MonomialSupersolution.velocity 2 5 1/1200
def physicalError : ℝ := SpinningOrbitNormal.velocityError+approximationError
def predictor (i : Fin 32) (ω t : ℝ) : ℝ :=
  (QuarticHarmonicResponse.response gravityGain (center i) (duration*ω-center i) t).2/1200

def ratePolynomial (i : Fin 32) (t : ℝ) : Polynomial ℝ :=
  Polynomial.C (1/1200)*
    (QuarticHarmonicResponse.velocityPolynomial gravityGain (center i) t).comp
      (Polynomial.C duration*Polynomial.X-Polynomial.C (center i))

theorem ratePolynomial_degree (i : Fin 32) (t : ℝ) :
    (ratePolynomial i t).natDegree≤4 := by
  apply (Polynomial.natDegree_C_mul_le _ _).trans
  apply Polynomial.natDegree_comp_le.trans
  rw [Polynomial.natDegree_sub_C,
    Polynomial.natDegree_C_mul (by norm_num [duration] : duration≠0),Polynomial.natDegree_X,
    mul_one]
  exact QuarticHarmonicResponse.velocityPolynomial_degree _ _ _

theorem ratePolynomial_eval (i : Fin 32) (ω t : ℝ) :
    (ratePolynomial i t).eval ω=predictor i ω t := by
  simp only [ratePolynomial,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_comp,
    Polynomial.eval_sub,Polynomial.eval_X,QuarticHarmonicResponse.velocityPolynomial_eval,predictor]
  ring

theorem numbers : 0≤forcingBudget ∧ approximationError<14/10000000 ∧
    physicalError<1/100000 := by
  norm_num [forcingBudget,halfwidth,QuarticHarmonicResponse.sourceBudget,
    approximationError,physicalError,SpinningOrbitNormal.velocityError,gravityBudget,
    Gravity.remainderBound,mu,Direct.gravityParameter,
    PolynomialSupersolution.value,PolynomialSupersolution.velocity,PolynomialSupersolution.polynomial,
    MonomialSupersolution.velocity,MonomialSupersolution.polynomial,
    MonomialSupersolution.six,MonomialSupersolution.four,MonomialSupersolution.pair,
    Polynomial.derivative_add,Polynomial.derivative_mul,Polynomial.derivative_pow]

theorem profile_endpoint {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    MonomialSupersolution.velocity 2 5 t≤MonomialSupersolution.velocity 2 5 1 := by
  norm_num [MonomialSupersolution.velocity,MonomialSupersolution.polynomial,
    MonomialSupersolution.six,MonomialSupersolution.four,MonomialSupersolution.pair,
    Polynomial.derivative_add,Polynomial.derivative_monomial,Polynomial.eval_add,
    Polynomial.eval_monomial] at ⊢
  have h6 : t^6≤1 := pow_le_one₀ ht.1 ht.2
  have h8 : t^8≤1 := pow_le_one₀ ht.1 ht.2
  have h10 : t^10≤1 := pow_le_one₀ ht.1 ht.2
  have h12 : t^12≤1 := pow_le_one₀ ht.1 ht.2
  linarith

theorem response_error {ω : ℝ} (hω : Admissible ω) (i : Fin 32)
    (hi : |duration*ω-center i|≤halfwidth) :
    ∀ t ∈ Icc (0:ℝ) 1, |SpinningOrbitNormal.velocity ω t/1200-predictor i ω t|≤approximationError := by
  let c := center i
  let d := duration*ω-c
  let Y := QuarticHarmonicResponse.response gravityGain c d
  let p := fun t => SpinningOrbitNormal.position ω t-(Y t).1
  let v := fun t => SpinningOrbitNormal.velocity ω t-(Y t).2
  let a := fun t => -gravityGain*p t+
    (144*cos (phase ω t)-QuarticHarmonicResponse.forcing c d t)
  have hYp (t : ℝ) : HasDerivAt (fun s => (Y s).1) ((Y t).2) t := by
    simpa [Y] using (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t
      (QuarticHarmonicResponse.derivative gravityGain c d t)
  have hYv (t : ℝ) : HasDerivAt (fun s => (Y s).2)
      (-gravityGain*(Y t).1+QuarticHarmonicResponse.forcing c d t) t := by
    simpa [Y] using (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t
      (QuarticHarmonicResponse.derivative gravityGain c d t)
  have hdp (t : ℝ) : HasDerivAt p (v t) t :=
    (SpinningOrbitNormal.derivative_position ω t).sub (hYp t)
  have hdv (t : ℝ) : HasDerivAt v (a t) t := by
    convert (SpinningOrbitNormal.derivative_velocity hω t).sub (hYv t) using 1
    dsimp [a,p]; ring
  have h := MonomialSecondOrderBound.response p v a 5 (κ := 2) (F := forcingBudget)
    (by norm_num) (by norm_num) numbers.1
    (continuous_iff_continuousAt.mpr fun t => (hdp t).continuousAt)
    (continuous_iff_continuousAt.mpr fun t => (hdv t).continuousAt)
    (fun t _ => hdp t) (fun t _ => hdv t)
    (by simp [p,Y,QuarticHarmonicResponse.initial,(SpinningOrbitNormal.initial ω).1])
    (by simp [v,Y,QuarticHarmonicResponse.initial,(SpinningOrbitNormal.initial ω).2]) (by
      intro t ht
      have hs := QuarticHarmonicResponse.source_profile c hi ht
      have he : (c+(duration*ω-center i))*t=phase ω t := by dsimp [c,phase]; ring
      rw [he] at hs
      change |144*cos (phase ω t)-QuarticHarmonicResponse.forcing c d t|≤forcingBudget*t^5 at hs
      have hh := norm_add_le (-gravityGain*p t)
        (144*cos (phase ω t)-QuarticHarmonicResponse.forcing c d t)
      simp only [Real.norm_eq_abs,abs_mul,abs_neg,abs_of_nonneg gravity_numbers.1.le] at hh
      change |a t|≤2*|p t|+forcingBudget*t^5
      dsimp [a]
      nlinarith [gravity_numbers.2.1,abs_nonneg (p t)])
  intro t ht
  have hv := (h t ht).2.trans
    (mul_le_mul_of_nonneg_left (profile_endpoint ht) numbers.1)
  change |SpinningOrbitNormal.velocity ω t/1200-(Y t).2/1200|≤_
  rw [← sub_div,abs_div]
  simpa [v,approximationError] using div_le_div_of_nonneg_right hv (by norm_num : (0:ℝ)≤1200)

theorem physical_prediction {ω : ℝ} (hω : Admissible ω) (X : Motion ω) (i : Fin 32)
    (hi : |duration*ω-center i|≤halfwidth) :
    ∀ t ∈ Icc (0:ℝ) 1, |X.v t 2/1200-predictor i ω t|<1/100000 := by
  intro t ht
  have h := (SpinningOrbitNormal.physical_prediction hω X t ht).2
  have hp : |X.v t 2/1200-SpinningOrbitNormal.velocity ω t/1200|≤SpinningOrbitNormal.velocityError := by
    rw [← sub_div,abs_div]; simpa using h
  have hh := (abs_sub_le _ (SpinningOrbitNormal.velocity ω t/1200) _).trans
    (add_le_add hp (response_error hω i hi t ht))
  exact hh.trans_lt numbers.2.2

theorem cover {ω : ℝ} (hω : Admissible ω) :
    ∃ i : Fin 32, |duration*ω-center i|≤halfwidth := by
  let x := (duration*ω-108)*(4/3:ℝ)
  have hx : 0≤x ∧ x≤32 := by
    have hlo := hω.1
    have hhi := hω.2
    dsimp [x,duration]; constructor <;> linarith
  have hl := Nat.floor_le hx.1
  have hu := Nat.lt_floor_add_one x
  by_cases hn : ⌊x⌋₊<32
  · refine ⟨⟨⌊x⌋₊,hn⟩,?_⟩
    rw [abs_le]
    dsimp [center,halfwidth,x] at *
    constructor <;> linarith
  · have hn' : (32:ℝ)≤⌊x⌋₊ := by exact_mod_cast Nat.le_of_not_gt hn
    refine ⟨31,?_⟩
    norm_num [center,halfwidth]
    dsimp [x] at *
    rw [abs_le]
    constructor <;> linarith

/-- Piecewise quartics recover the 0.01 mm/s physical target. This does
not contradict the global quartic obstruction, and proves no need for 32
separate error propagations: the same uniform profile works on every cell. -/
theorem refined_certificate {ω : ℝ} (hω : Admissible ω) (X : Motion ω) :
    ∃ i : Fin 32, ∀ t ∈ Icc (0:ℝ) 1, |X.v t 2/1200-predictor i ω t|<1/100000 := by
  obtain ⟨i,hi⟩ := cover hω
  exact ⟨i,physical_prediction hω X i hi⟩

end GNC.OrbitalComparison.SpinningOrbitRefinement
