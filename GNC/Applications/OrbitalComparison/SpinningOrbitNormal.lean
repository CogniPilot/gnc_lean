import GNC.Applications.OrbitalComparison.SpinningOrbitLinear
import GNC.Applications.OrbitalComparison.UncertainSpin

/-! Closed normal response, full nonlinear physical certificate, and a
universal quartic obstruction for the uncertain-spin orbital family.
The force and gravity are both included. The same exact response is
available to a classical frequency-aware modal construction. -/
noncomputable section
namespace GNC.OrbitalComparison.SpinningOrbitNormal
open SpatialBurn UniformCertificate PointingCapFrame SpinningOrbit Set Real

def Admissible (ω : ℝ) : Prop := ω ∈ Icc (9/100:ℝ) (11/100)
def position (ω : ℝ) : ℝ → ℝ := ForcedOscillator.position 144 gravityFrequency (duration*ω)
def velocity (ω : ℝ) : ℝ → ℝ := ForcedOscillator.velocity 144 gravityFrequency (duration*ω)
def positionError : ℝ := gravityBudget*PolynomialSupersolution.value 2 1
def velocityError : ℝ := gravityBudget*PolynomialSupersolution.velocity 2 1/1200
def freeCorrection : ℝ := 144/(108^2-2)*(2/108+13/10)/1200
def totalDifference : ℝ := velocityError+freeCorrection

theorem frequency_bounds {ω : ℝ} (hω : Admissible ω) :
    0≤gravityFrequency ∧ gravityFrequency≤13/10 ∧
    gravityFrequency^2=gravityGain ∧ 108≤duration*ω ∧
    gravityFrequency^2<(duration*ω)^2 := by
  have hs : gravityFrequency^2=gravityGain := sq_sqrt gravity_numbers.1.le
  have h0 : 0≤gravityFrequency := sqrt_nonneg _
  have hg : gravityGain<(13/10:ℝ)^2 := by
    norm_num [gravityGain,mu,Direct.gravityParameter]
  have hw := hω.1
  dsimp [duration] at *
  refine ⟨h0,?_,hs,?_,?_⟩ <;> nlinarith [gravity_numbers.2.1]

theorem derivative_position (ω t : ℝ) : HasDerivAt (position ω) (velocity ω t) t :=
  ForcedOscillator.derivative_position _ _ _ _

theorem derivative_velocity {ω : ℝ} (hω : Admissible ω) (t : ℝ) :
    HasDerivAt (velocity ω) (-gravityGain*position ω t+144*cos (phase ω t)) t := by
  have hf := frequency_bounds hω
  simpa [position,phase,hf.2.2.1] using
    ForcedOscillator.derivative_velocity 144 gravityFrequency (duration*ω) t
      (sub_pos.mpr hf.2.2.2.2).ne'

theorem initial (ω : ℝ) : position ω 0=0 ∧ velocity ω 0=0 := ForcedOscillator.initial _ _ _

theorem error_numbers : positionError<43/10000 ∧ velocityError<82/10000000 ∧
    totalDifference<22/1000000 := by
  norm_num [positionError,velocityError,totalDifference,freeCorrection,gravityBudget,
    Gravity.remainderBound,mu,Direct.gravityParameter,
    PolynomialSupersolution.value,PolynomialSupersolution.velocity,PolynomialSupersolution.polynomial,
    Polynomial.derivative_add,Polynomial.derivative_mul,Polynomial.derivative_pow]

theorem physical_prediction {ω : ℝ} (hω : Admissible ω) (X : Motion ω) :
    ∀ t ∈ Icc (0:ℝ) 1,
      |X.p t 2-position ω t|≤positionError ∧
      |X.v t 2-velocity ω t|/1200≤velocityError := by
  let p := fun t => X.p t 2-position ω t
  let v := fun t => X.v t 2-velocity ω t
  let a := fun t => -gravityGain*p t+(gravityResidual ω X t) 2
  have hp := (EuclideanSpace.proj (𝕜 := ℝ) (2:Fin 3)).continuous.comp X.continuous_p
  have hv := (EuclideanSpace.proj (𝕜 := ℝ) (2:Fin 3)).continuous.comp X.continuous_v
  have hdp (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : HasDerivAt p (v t) t :=
    ((EuclideanSpace.proj (𝕜 := ℝ) (2:Fin 3)).hasFDerivAt.comp_hasDerivAt t
      (X.derivative_p t ht)).sub (derivative_position ω t)
  have hdv (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : HasDerivAt v (a t) t := by
    have h := ((EuclideanSpace.proj (𝕜 := ℝ) (2:Fin 3)).hasFDerivAt.comp_hasDerivAt t
      (X.derivative_v t ht)).sub (derivative_velocity hω t)
    convert h using 1
    change -gravityGain*p t+(gravityResidual ω X t) 2 =
      acceleration ω t (X.p t) 2-(-gravityGain*position ω t+144*cos (phase ω t))
    rw [normal_acceleration]
    dsimp [p]; ring
  have h := ConstantSecondOrderBound.endpoint_bounds p v a (κ := 2) (F := gravityBudget)
    (by norm_num) (by norm_num) gravity_numbers.2.2.1
    (hp.sub (continuous_iff_continuousAt.mpr fun t => (derivative_position ω t).continuousAt))
    (hv.sub (continuous_iff_continuousAt.mpr fun t => (derivative_velocity hω t).continuousAt))
    hdp hdv
    (by simp [p,X.initial_p,(initial ω).1,(reference_normal 0).1])
    (by simp [v,X.initial_v,(initial ω).2,(reference_normal 0).2]) (by
      intro t ht
      have hb := (PiLp.norm_apply_le (gravityResidual ω X t) 2).trans (residual_bound ω X ht)
      have hh := norm_add_le (-gravityGain*p t) ((gravityResidual ω X t) 2)
      simp only [Real.norm_eq_abs,abs_mul,abs_neg,abs_of_nonneg gravity_numbers.1.le] at hh hb
      change |a t|≤2*|p t|+gravityBudget
      dsimp [a]
      nlinarith [gravity_numbers.2.1,abs_nonneg (p t)])
  intro t ht
  exact ⟨(h t ht).1,div_le_div_of_nonneg_right (h t ht).2 (by norm_num)⟩

theorem retained_minus_free {ω : ℝ} (hω : Admissible ω) (t : ℝ) :
    |velocity ω t/1200-SpinningThrust.velocityX (1/10000) ω (1200*t)|≤freeCorrection := by
  have hf := frequency_bounds hω
  have hw : 0<duration*ω := by linarith [hf.2.2.2.1]
  have h := ForcedOscillator.velocity_minus_free_bound (by norm_num : (0:ℝ)≤144)
    hf.1 hw hf.2.2.2.2 t
  have he : 144*sin (duration*ω*t)/(duration*ω)/1200=
      SpinningThrust.velocityX (1/10000) ω (1200*t) := by
    dsimp [duration,SpinningThrust.velocityX]
    rw [show 1200*ω*t=ω*(1200*t) by ring]
    ring
  have hd := div_le_div_of_nonneg_right h (by norm_num : (0:ℝ)≤1200)
  rw [show (1200:ℝ)=|1200| by norm_num,← abs_div] at hd
  rw [show (ForcedOscillator.velocity 144 gravityFrequency (duration*ω) t-
      144*sin (duration*ω*t)/(duration*ω))/1200 =
      velocity ω t/1200-SpinningThrust.velocityX (1/10000) ω (1200*t) by
        rw [sub_div,he]; rfl] at hd
  have hden : (108:ℝ)^2-2 ≤ (duration*ω)^2-gravityFrequency^2 := by
    nlinarith [hf.2.2.1,gravity_numbers.2.1,hf.2.2.2.1]
  have hdiv : gravityFrequency^2/(duration*ω) ≤ (2:ℝ)/108 := by
    apply div_le_div₀ (by positivity) (hf.2.2.1.le.trans gravity_numbers.2.1.le)
      (by norm_num) hf.2.2.2.1
  have hrecip : (144:ℝ)/((duration*ω)^2-gravityFrequency^2)≤144/(108^2-2) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hden
  have hmul := mul_le_mul hrecip (add_le_add hdiv hf.2.1)
    (add_nonneg (div_nonneg (sq_nonneg _) hw.le) hf.1)
    (by norm_num : (0:ℝ)≤144/(108^2-2))
  have hh := div_le_div_of_nonneg_right hmul (by norm_num : (0:ℝ)≤1200)
  norm_num only [abs_of_pos (by norm_num : (0:ℝ)<1200)] at hd
  exact hd.trans hh

theorem physical_minus_free {ω : ℝ} (hω : Admissible ω) (X : Motion ω)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    |X.v t 2/1200-SpinningThrust.velocityX (1/10000) ω (1200*t)|≤totalDifference := by
  have h := (physical_prediction hω X t ht).2
  have hc := retained_minus_free hω t
  have he : |X.v t 2/1200-velocity ω t/1200|≤velocityError := by
    rw [← sub_div,abs_div]
    simpa using h
  exact (abs_sub_le _ (velocity ω t/1200) _).trans (add_le_add he hc)

/-- Every quartic rate predictor fails in the actual nonlinear orbit.
The witness's linear-gravity and nonlinear-gravity corrections are both
bounded above before transferring its obstruction. -/
theorem physical_quartic_obstruction (p : Polynomial ℝ) (hp : p.natDegree≤4) :
    ∃ ω ∈ Icc (9/100:ℝ) (11/100),
      97/100000 < |(trajectory ω).v 1 2/1200-p.eval ω| := by
  by_contra! h
  have hb := UncertainSpin.perturbed_quartic_lower_bound
    (by norm_num : (0:ℝ)≤1/10000) (by norm_num : (0:ℝ)<1200)
    (fun ω => (trajectory ω).v 1 2/1200) p hp (δ := totalDifference)
    (fun i => by
      simpa using physical_minus_free (UncertainSpin.example_rates i)
        (trajectory (UncertainSpin.rates 1200 i)) (by norm_num : (1:ℝ) ∈ Icc 0 1))
    (fun i => h _ (UncertainSpin.example_rates i))
  have hpi := Real.pi_lt_d4
  have hpos := Real.pi_pos
  have hsmall := error_numbers.2.2
  have hsig : (1/10000:ℝ)*2*1200/(77*Real.pi)>992/1000000 := by
    rw [gt_iff_lt,lt_div_iff₀ (by positivity)]
    nlinarith
  linarith

/-- An actual physical error separation, not just a comparison of two
upper bounds. At a witness rate, every quartic's endpoint error exceeds
118 times the retained oscillator's endpoint error. -/
theorem certified_separation (p : Polynomial ℝ) (hp : p.natDegree≤4) :
    ∃ ω ∈ Icc (9/100:ℝ) (11/100),
      97/100000 < |(trajectory ω).v 1 2/1200-p.eval ω| ∧
      118*|(trajectory ω).v 1 2/1200-velocity ω 1/1200| <
        |(trajectory ω).v 1 2/1200-p.eval ω| := by
  obtain ⟨ω,hω,hpω⟩ := physical_quartic_obstruction p hp
  have h := (physical_prediction hω (trajectory ω) 1 (by norm_num)).2
  have he : |(trajectory ω).v 1 2/1200-velocity ω 1/1200|≤velocityError := by
    rw [← sub_div,abs_div]
    simpa using h
  exact ⟨ω,hω,hpω,by linarith [error_numbers.2.1]⟩

end GNC.OrbitalComparison.SpinningOrbitNormal
