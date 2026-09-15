import GNC.Applications.OrbitalComparison.SpinningOrbit
import GNC.Analysis.FundamentalSolution

/-! Existence and full spatial error certificate for the retained-gradient
response of the spinning-thrust orbit. Only the nonlinear gravity remainder
is discarded, and its complete effect is bounded. The forcing phase remains
inside the exact linear response rather than an uncertainty polynomial. -/
noncomputable section
namespace GNC.OrbitalComparison.SpinningOrbitLinear
open SpatialBurn UniformCertificate PointingCapFrame SpinningOrbit Set
open scoped RealInnerProductSpace

abbrev State := E3 × E3
def generator : State →ₗ[ℝ] State where
  toFun x := (x.2,positionOperator 2 x.1+velocityOperator 2 x.2)
  map_add' x y := by simp; abel
  map_smul' c x := by simp
def bodyInput (ω t : ℝ) : E3 :=
  (144:ℝ) • pack 0 (Real.sin (phase ω t)) (Real.cos (phase ω t))

theorem turn_input (ω t : ℝ) : turn 2 t (bodyInput ω t)=input ω t := by
  simp [bodyInput,input,SpinningOrbit.direction]

structure Response (ω : ℝ) where
  p : ℝ → E3
  v : ℝ → E3
  continuous_p : Continuous p
  continuous_v : Continuous v
  initial_p : p 0=0
  initial_v : v 0=0
  derivative_p : ∀ t, HasDerivAt p (v t) t
  derivative_v : ∀ t, HasDerivAt v
    ((1440000:ℝ) • Gravity.gradient mu (reference 2 t) (p t)+input ω t) t

theorem exists_response (ω : ℝ) : Nonempty (Response ω) := by
  let A := generator.toContinuousLinearMap
  let u : ℝ → State := fun t => (0,bodyInput ω t)
  have hu : Continuous u := by
    dsimp [u,bodyInput,pack,phase,duration]
    fun_prop
  obtain ⟨x,hx,_⟩ := ForcedResponse.exists_unique_response (fun _ => A)
    continuous_const u hu 0
  have hp (t : ℝ) : HasDerivAt (fun s => (x s).1) ((x t).2) t := by
    simpa [A,generator,u] using
      (ContinuousLinearMap.fst ℝ E3 E3).hasFDerivAt.comp_hasDerivAt t (hx.2 t)
  have hv (t : ℝ) : HasDerivAt (fun s => (x s).2)
      (positionOperator 2 (x t).1+velocityOperator 2 (x t).2+bodyInput ω t) t := by
    simpa [A,generator,u] using
      (ContinuousLinearMap.snd ℝ E3 E3).hasFDerivAt.comp_hasDerivAt t (hx.2 t)
  let p := fun t => turn 2 t (x t).1
  let v := fun t => turn 2 t ((x t).2+spin 2 (x t).1)
  have hdp (t : ℝ) : HasDerivAt p (v t) t := turn_derivative 2 (hp t)
  have hdv (t : ℝ) : HasDerivAt v
      ((1440000:ℝ) • Gravity.gradient mu (reference 2 t) (p t)+input ω t) t := by
    have hd := turn_derivative 2 ((hv t).add (spin_derivative 2 (hp t)))
    have he := linear_residual_identity 2 t (x t).1 (x t).2
      (positionOperator 2 (x t).1+velocityOperator 2 (x t).2+bodyInput ω t) (bodyInput ω t)
    have hz : (positionOperator 2 (x t).1+velocityOperator 2 (x t).2+bodyInput ω t)-
        positionOperator 2 (x t).1-velocityOperator 2 (x t).2-bodyInput ω t=0 := by abel
    rw [hz,map_zero,turn_input] at he
    have heq := sub_eq_iff_eq_add.mp (sub_eq_zero.mp he)
    convert hd using 1
    calc
      _ = turn 2 t (positionOperator 2 (x t).1+velocityOperator 2 (x t).2+
          bodyInput ω t+(2:ℝ) • spin 2 (x t).2+spin 2 (spin 2 (x t).1)) := by
        norm_num [p,scale,add_comm] at heq ⊢
        exact heq.symm
      _ = _ := by
        congr 1
        simp only [Pi.add_apply,map_add]
        module
  exact ⟨{
    p := p
    v := v
    continuous_p := continuous_iff_continuousAt.mpr fun t => (hdp t).continuousAt
    continuous_v := continuous_iff_continuousAt.mpr fun t => (hdv t).continuousAt
    initial_p := by simp [p,hx.1]
    initial_v := by simp [v,hx.1]
    derivative_p := hdp
    derivative_v := hdv }⟩

def response (ω : ℝ) : Response ω := Classical.choice (exists_response ω)

theorem gradient_bound (t : ℝ) (d : E3) :
    ‖(1440000:ℝ) • Gravity.gradient mu (reference 2 t) d‖≤4*‖d‖ := by
  have h := Gravity.gradient_bound mu (by norm_num [mu]) (reference 2 t) d
  rw [reference_norm] at h
  rw [norm_smul]
  norm_num only [Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<1440000)]
  have hg : 1440000*(2*mu/7000000^3)≤(4:ℝ) := by norm_num [mu,Direct.gravityParameter]
  nlinarith [mul_le_mul_of_nonneg_left h (by norm_num : (0:ℝ)≤1440000),
    mul_le_mul_of_nonneg_right hg (norm_nonneg d)]

theorem response_bound (ω : ℝ) (Y : Response ω) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ‖Y.p t‖≤100 := by
  have h := ConstantSecondOrderBound.endpoint_bounds Y.p Y.v
    (fun t => (1440000:ℝ) • Gravity.gradient mu (reference 2 t) (Y.p t)+input ω t)
    (κ := 4) (F := 144) (by norm_num) (by norm_num) (by norm_num)
    Y.continuous_p Y.continuous_v (fun t _ => Y.derivative_p t)
    (fun t _ => Y.derivative_v t) Y.initial_p Y.initial_v (fun t _ =>
      (norm_add_le _ _).trans (by rw [input_norm]; exact add_le_add (gradient_bound t (Y.p t)) le_rfl)) t ht
  norm_num [PolynomialSupersolution.value,PolynomialSupersolution.polynomial] at h
  linarith [h.1]

def positionError : ℝ := gravityBudget*PolynomialSupersolution.value 4 1
def velocityError : ℝ := gravityBudget*PolynomialSupersolution.velocity 4 1/1200

theorem error_numbers : 0≤positionError ∧ positionError<1/200 ∧
    0≤velocityError ∧ velocityError<11/1000000 := by
  norm_num [positionError,velocityError,gravityBudget,Gravity.remainderBound,mu,Direct.gravityParameter,
    PolynomialSupersolution.value,PolynomialSupersolution.velocity,PolynomialSupersolution.polynomial,
    Polynomial.derivative_add,Polynomial.derivative_mul,Polynomial.derivative_pow]

/-- Every physical solution is within 5 mm and 0.011 mm/s of the exact
retained-gradient response, for every real rate and every time in the burn.
No pre-existing tube assumption or numerical sample is a premise. -/
theorem physical_prediction (ω : ℝ) (X : Motion ω) (Y : Response ω) :
    ∀ t ∈ Icc (0:ℝ) 1,
      ‖X.p t-(reference 2 t+Y.p t)‖≤positionError ∧
      ‖X.v t-(referenceVelocity 2 t+Y.v t)‖/1200≤velocityError := by
  let q := fun t => reference 2 t+Y.p t
  let qv := fun t => referenceVelocity 2 t+Y.v t
  let qa := fun t => physicalAcceleration 2 e0 t (reference 2 t)+
    (1440000:ℝ) • Gravity.gradient mu (reference 2 t) (Y.p t)+input ω t
  have hr (t : ℝ) (_ht : t ∈ Icc (0:ℝ) 1) : 6999800+100≤‖q t‖ := by
    have h := norm_sub_le (q t) (Y.p t)
    have he : q t-Y.p t=reference 2 t := by simp [q]
    rw [he,reference_norm] at h
    linarith [response_bound ω Y _ht]
  have hd (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      ‖(1440000:ℝ) • (Gravity.field mu (q t)+thrust ω t)-qa t‖≤gravityBudget := by
    have h := Gravity.remainder_bound_of_norm_le mu (by norm_num [mu]) (reference 2 t)
      (Y.p t) (response_bound ω Y ht) (by rw [reference_norm]; norm_num)
    rw [reference_norm] at h
    have he : (1440000:ℝ) • (Gravity.field mu (q t)+thrust ω t)-qa t =
        (1440000:ℝ) • (Gravity.field mu (reference 2 t+Y.p t)-Gravity.field mu (reference 2 t)-
          Gravity.gradient mu (reference 2 t) (Y.p t)) := by
      dsimp [q,qa,thrust,physicalAcceleration,scale,forceAmplitude,input]
      module
    rw [he,norm_smul]
    simpa [gravityBudget] using mul_le_mul_of_nonneg_left h (by norm_num : (0:ℝ)≤1440000)
  have h := Gravity.constant_prediction mu 1440000 (by norm_num [mu]) (by norm_num)
    X.p X.v q qv qa (thrust ω) (κ := 4) (F := gravityBudget) (r := 6999800) (M := 100)
    (by norm_num) (by norm_num) gravity_numbers.2.2.1 (by norm_num)
    (by change positionError<100; linarith [error_numbers.2.1])
    (by norm_num [mu,Direct.gravityParameter]) hr
    X.continuous_p X.continuous_v ((PointingCapBurn.reference_continuous 2).add Y.continuous_p)
    ((PointingCapBurn.referenceVelocity_continuous 2).add Y.continuous_v)
    X.derivative_p X.derivative_v
    (fun t _ => (reference_derivative 2 t).add (Y.derivative_p t))
    (fun t _ => by
      convert (referenceVelocity_derivative 2 t).add (Y.derivative_v t) using 1
      dsimp [qa]; abel)
    (by simpa [q,Y.initial_p] using X.initial_p)
    (by simpa [qv,Y.initial_v] using X.initial_v) hd
  intro t ht
  exact ⟨(h t ht).1,div_le_div_of_nonneg_right (h t ht).2 (by norm_num)⟩

end GNC.OrbitalComparison.SpinningOrbitLinear
