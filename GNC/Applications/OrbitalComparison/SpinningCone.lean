import GNC.Applications.OrbitalComparison.PointingCapBurn
import GNC.Analysis.ConstantSecondOrderBound
import GNC.Analysis.FundamentalSolution

/-! A 120-second spinning nominal with a body-fixed thrust misalignment, in
full inverse-square gravity. The reference is the existing powered circle.
The nominal body frame keeps its thrust axis radial and spins about it by
`Ω` radians over the burn; the uncertain input is a constant body-frame
misalignment with transverse features `f 0, f 1` and axial feature `f 2`,
so the transverse thrust perturbation rotates at the spin rate. The
retained-gradient response keeps the exact features and the exact spin
phase; only the nonlinear gravity remainder is discarded, and its complete
effect is bounded for every spin rate and every feature vector in the ball.
Time is normalized by 120 s and velocities here are derivatives in that time. -/
noncomputable section
namespace GNC.OrbitalComparison.SpinningCone
open SpatialBurn UniformCertificate PointingCapFrame Set Real
open scoped RealInnerProductSpace

/-- Horizon scale: `600*alpha` seconds. -/
def alpha : ℝ := 1/5
/-- Feature-ball radius: the misalignment features satisfy `‖f‖ ≤ 1/10`. -/
def sigma : ℝ := 1/10
/-- Body-frame thrust direction change, spun about the radial thrust axis. -/
def misalignment (f : Fin 3 → ℝ) (Ω t : ℝ) : E3 :=
  pack (f 2) (f 0*cos (Ω*t)-f 1*sin (Ω*t)) (f 0*sin (Ω*t)+f 1*cos (Ω*t))
def bodyInput (f : Fin 3 → ℝ) (Ω t : ℝ) : E3 :=
  (scale alpha*(Direct.thrust:ℝ)) • misalignment f Ω t
def input (f : Fin 3 → ℝ) (Ω t : ℝ) : E3 := turn alpha t (bodyInput f Ω t)
def thrust (f : Fin 3 → ℝ) (Ω t : ℝ) : E3 :=
  (Direct.thrust:ℝ) • turn alpha t (e0+misalignment f Ω t)
def acceleration (f : Fin 3 → ℝ) (Ω t : ℝ) (p : E3) : E3 :=
  scale alpha • (Gravity.field mu p+thrust f Ω t)

theorem scale_alpha : scale alpha=14400 := by norm_num [scale,alpha]

theorem misalignment_norm_sq (f : Fin 3 → ℝ) (Ω t : ℝ) :
    ‖misalignment f Ω t‖^2=f 0^2+f 1^2+f 2^2 := by
  rw [misalignment,pack_norm_sq]
  linear_combination (f 0^2+f 1^2)*sin_sq_add_cos_sq (Ω*t)

theorem misalignment_norm {f : Fin 3 → ℝ} (hf : f 0^2+f 1^2+f 2^2≤sigma^2) (Ω t : ℝ) :
    ‖misalignment f Ω t‖≤sigma := by
  have h := misalignment_norm_sq f Ω t
  have hs : (0:ℝ)≤sigma := by norm_num [sigma]
  nlinarith [norm_nonneg (misalignment f Ω t)]

theorem input_bound {f : Fin 3 → ℝ} (hf : f 0^2+f 1^2+f 2^2≤sigma^2) (Ω t : ℝ) :
    ‖input f Ω t‖≤22 := by
  have hm := misalignment_norm hf Ω t
  have ht : (0:ℝ)≤Direct.thrust := SpatialFieldCertificate.physical_constants.2.2
  rw [input,turn_norm,bodyInput,norm_smul,Real.norm_eq_abs,scale_alpha,
    abs_of_nonneg (by positivity)]
  have hn : (14400:ℝ)*(Direct.thrust:ℝ)≤220 := by
    norm_num [Direct.thrust,Direct.gravityParameter,Direct.referenceRadius,Direct.angularSpeed]
  have hs : sigma=1/10 := rfl
  nlinarith [norm_nonneg (misalignment f Ω t)]

theorem misalignment_continuous (f : Fin 3 → ℝ) (Ω : ℝ) : Continuous (misalignment f Ω) := by
  change Continuous (fun t => misalignment f Ω t)
  dsimp [misalignment,pack]
  fun_prop

theorem input_continuous (f : Fin 3 → ℝ) (Ω : ℝ) : Continuous (input f Ω) := by
  change Continuous (fun t => turn alpha t (bodyInput f Ω t))
  dsimp [bodyInput,misalignment,turn,HarmonicFrame.turn,SpatialRotatingFrame.mix,pack]
  fun_prop

theorem turn_input (f : Fin 3 → ℝ) (Ω t : ℝ) : turn alpha t (bodyInput f Ω t)=input f Ω t := rfl

structure Motion (f : Fin 3 → ℝ) (Ω : ℝ) where
  p : ℝ → E3
  v : ℝ → E3
  continuous_p : Continuous p
  continuous_v : Continuous v
  initial_p : p 0=reference alpha 0
  initial_v : v 0=referenceVelocity alpha 0
  derivative_p : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt p (v t) t
  derivative_v : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt v (acceleration f Ω t (p t)) t

theorem exists_motion {f : Fin 3 → ℝ} (hf : f 0^2+f 1^2+f 2^2≤sigma^2) (Ω : ℝ) :
    ∃ X : Motion f Ω, ∀ t ∈ Icc (0:ℝ) 1, (6800000:ℝ)≤‖X.p t‖ := by
  have hs : 0≤scale alpha := by rw [scale_alpha]; norm_num
  obtain ⟨x,hx,hx0,hradius,hderiv⟩ := ForcedOrbitExistence.exists_relative_four_gain
    (μ := mu) (scale := scale alpha) (r := 6800000) (R := 100000)
    (by norm_num [mu]) hs (by norm_num) (by norm_num)
    (by rw [scale_alpha]; norm_num [mu,Direct.gravityParameter])
    (reference alpha) (input f Ω) (PointingCapBurn.reference_continuous alpha) (input_continuous f Ω)
    (by intro t; rw [reference_norm]; norm_num)
    (D := 22) (by norm_num) (fun t => input_bound hf Ω t) (by norm_num)
  refine ⟨{
    p := fun t => reference alpha t+(x t).1
    v := fun t => referenceVelocity alpha t+(x t).2
    continuous_p := (PointingCapBurn.reference_continuous alpha).add hx.fst
    continuous_v := (PointingCapBurn.referenceVelocity_continuous alpha).add hx.snd
    initial_p := by simp [hx0]
    initial_v := by simp [hx0]
    derivative_p := fun t ht => (reference_derivative alpha t).add (hderiv t ht).fst
    derivative_v := ?_ },hradius⟩
  intro t ht
  convert (referenceVelocity_derivative alpha t).add (hderiv t ht).snd using 1
  dsimp [acceleration,physicalAcceleration,ForcedOrbitExistence.rate,input,bodyInput,thrust]
  simp only [map_add,map_smul]
  module

abbrev State := E3 × E3
def generator : State →ₗ[ℝ] State where
  toFun x := (x.2,positionOperator alpha x.1+velocityOperator alpha x.2)
  map_add' x y := by simp; abel
  map_smul' c x := by simp

/-- The retained-gradient response to the exact features and exact spin phase. -/
structure Response (f : Fin 3 → ℝ) (Ω : ℝ) where
  p : ℝ → E3
  v : ℝ → E3
  continuous_p : Continuous p
  continuous_v : Continuous v
  initial_p : p 0=0
  initial_v : v 0=0
  derivative_p : ∀ t, HasDerivAt p (v t) t
  derivative_v : ∀ t, HasDerivAt v
    (scale alpha • Gravity.gradient mu (reference alpha t) (p t)+input f Ω t) t

theorem exists_response (f : Fin 3 → ℝ) (Ω : ℝ) : Nonempty (Response f Ω) := by
  let A := generator.toContinuousLinearMap
  let u : ℝ → State := fun t => (0,bodyInput f Ω t)
  have hu : Continuous u := by
    dsimp [u,bodyInput,misalignment,pack]
    fun_prop
  obtain ⟨x,hx,_⟩ := ForcedResponse.exists_unique_response (fun _ => A)
    continuous_const u hu 0
  have hp (t : ℝ) : HasDerivAt (fun s => (x s).1) ((x t).2) t := by
    simpa [A,generator,u] using
      (ContinuousLinearMap.fst ℝ E3 E3).hasFDerivAt.comp_hasDerivAt t (hx.2 t)
  have hv (t : ℝ) : HasDerivAt (fun s => (x s).2)
      (positionOperator alpha (x t).1+velocityOperator alpha (x t).2+bodyInput f Ω t) t := by
    simpa [A,generator,u] using
      (ContinuousLinearMap.snd ℝ E3 E3).hasFDerivAt.comp_hasDerivAt t (hx.2 t)
  let p := fun t => turn alpha t (x t).1
  let v := fun t => turn alpha t ((x t).2+spin alpha (x t).1)
  have hdp (t : ℝ) : HasDerivAt p (v t) t := turn_derivative alpha (hp t)
  have hdv (t : ℝ) : HasDerivAt v
      (scale alpha • Gravity.gradient mu (reference alpha t) (p t)+input f Ω t) t := by
    have hd := turn_derivative alpha ((hv t).add (spin_derivative alpha (hp t)))
    have he := linear_residual_identity alpha t (x t).1 (x t).2
      (positionOperator alpha (x t).1+velocityOperator alpha (x t).2+bodyInput f Ω t) (bodyInput f Ω t)
    have hz : (positionOperator alpha (x t).1+velocityOperator alpha (x t).2+bodyInput f Ω t)-
        positionOperator alpha (x t).1-velocityOperator alpha (x t).2-bodyInput f Ω t=0 := by abel
    rw [hz,map_zero,turn_input] at he
    have heq := sub_eq_iff_eq_add.mp (sub_eq_zero.mp he)
    convert hd using 1
    calc
      _ = turn alpha t (positionOperator alpha (x t).1+velocityOperator alpha (x t).2+
          bodyInput f Ω t+(2:ℝ) • spin alpha (x t).2+spin alpha (spin alpha (x t).1)) := by
        rw [show scale alpha • Gravity.gradient mu (reference alpha t) (p t)+input f Ω t =
          input f Ω t+scale alpha • Gravity.gradient mu (reference alpha t) (turn alpha t (x t).1) by
            simp only [p]; exact add_comm _ _, heq]
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

def response (f : Fin 3 → ℝ) (Ω : ℝ) : Response f Ω := Classical.choice (exists_response f Ω)

theorem gradient_bound (t : ℝ) (d : E3) :
    ‖scale alpha • Gravity.gradient mu (reference alpha t) d‖≤(1/25)*‖d‖ := by
  have h := Gravity.gradient_bound mu (by norm_num [mu]) (reference alpha t) d
  rw [reference_norm] at h
  rw [norm_smul,scale_alpha]
  norm_num only [Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<14400)]
  have hg : 14400*(2*mu/7000000^3)≤(1/25:ℝ) := by norm_num [mu,Direct.gravityParameter]
  nlinarith [mul_le_mul_of_nonneg_left h (by norm_num : (0:ℝ)≤14400),
    mul_le_mul_of_nonneg_right hg (norm_nonneg d)]

/-- The retained-gradient displacement stays below 12 m for every feature
vector in the ball and every spin rate. -/
theorem response_bound {f : Fin 3 → ℝ} (hf : f 0^2+f 1^2+f 2^2≤sigma^2) (Ω : ℝ)
    (Y : Response f Ω) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) : ‖Y.p t‖≤12 := by
  have h := ConstantSecondOrderBound.endpoint_bounds Y.p Y.v
    (fun t => scale alpha • Gravity.gradient mu (reference alpha t) (Y.p t)+input f Ω t)
    (κ := 1/25) (F := 22) (by norm_num) (by norm_num) (by norm_num)
    Y.continuous_p Y.continuous_v (fun t _ => Y.derivative_p t)
    (fun t _ => Y.derivative_v t) Y.initial_p Y.initial_v (fun t _ =>
      (norm_add_le _ _).trans (add_le_add (gradient_bound t (Y.p t)) (input_bound hf Ω t))) t ht
  norm_num [PolynomialSupersolution.value,PolynomialSupersolution.polynomial] at h
  linarith [h.1]

def gravityBudget : ℝ := scale alpha*Gravity.remainderBound mu 7000000 12
def positionError : ℝ := gravityBudget*PolynomialSupersolution.value (1/25) 1
def velocityError : ℝ := gravityBudget*PolynomialSupersolution.velocity (1/25) 1/120

theorem budget_nonnegative : 0≤gravityBudget := by
  norm_num [gravityBudget,scale,alpha,Gravity.remainderBound,mu,Direct.gravityParameter]

/-- Certified constants: below 0.52 micrometres and 8.7 nanometres per second. -/
theorem error_numbers : 0≤positionError ∧ positionError<52/100000000 ∧
    0≤velocityError ∧ velocityError<87/10000000000 := by
  norm_num [positionError,velocityError,gravityBudget,scale,alpha,Gravity.remainderBound,mu,
    Direct.gravityParameter,PolynomialSupersolution.value,PolynomialSupersolution.velocity,
    PolynomialSupersolution.polynomial,Polynomial.derivative_add,Polynomial.derivative_mul,
    Polynomial.derivative_pow]

/-- Every physical solution of the spinning-cone family is within 0.52 μm and
8.7 nm/s of the exact retained-gradient response, for every real spin rate,
every feature vector in the ball, and every time in the burn. -/
theorem physical_prediction {f : Fin 3 → ℝ} (hf : f 0^2+f 1^2+f 2^2≤sigma^2) (Ω : ℝ)
    (X : Motion f Ω) (Y : Response f Ω) :
    ∀ t ∈ Icc (0:ℝ) 1,
      ‖X.p t-(reference alpha t+Y.p t)‖≤positionError ∧
      ‖X.v t-(referenceVelocity alpha t+Y.v t)‖/120≤velocityError := by
  let q := fun t => reference alpha t+Y.p t
  let qv := fun t => referenceVelocity alpha t+Y.v t
  let qa := fun t => physicalAcceleration alpha e0 t (reference alpha t)+
    scale alpha • Gravity.gradient mu (reference alpha t) (Y.p t)+input f Ω t
  have hs : (0:ℝ)≤scale alpha := by rw [scale_alpha]; norm_num
  have hr (t : ℝ) (_ht : t ∈ Icc (0:ℝ) 1) : 6999976+12≤‖q t‖ := by
    have h := norm_sub_le (q t) (Y.p t)
    have he : q t-Y.p t=reference alpha t := by simp [q]
    rw [he,reference_norm] at h
    linarith [response_bound hf Ω Y _ht]
  have hd (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      ‖scale alpha • (Gravity.field mu (q t)+thrust f Ω t)-qa t‖≤gravityBudget := by
    have h := Gravity.remainder_bound_of_norm_le mu (by norm_num [mu]) (reference alpha t)
      (Y.p t) (response_bound hf Ω Y ht) (by rw [reference_norm]; norm_num)
    rw [reference_norm] at h
    have he : scale alpha • (Gravity.field mu (q t)+thrust f Ω t)-qa t =
        scale alpha • (Gravity.field mu (reference alpha t+Y.p t)-Gravity.field mu (reference alpha t)-
          Gravity.gradient mu (reference alpha t) (Y.p t)) := by
      dsimp [q,qa,thrust,physicalAcceleration,input,bodyInput]
      simp only [map_add,map_smul]
      module
    rw [he,norm_smul,Real.norm_eq_abs,abs_of_nonneg hs]
    simpa [gravityBudget] using mul_le_mul_of_nonneg_left h hs
  have h := Gravity.constant_prediction mu (scale alpha) (by norm_num [mu]) hs
    X.p X.v q qv qa (thrust f Ω) (κ := 1/25) (F := gravityBudget) (r := 6999976) (M := 12)
    (by norm_num) (by norm_num) budget_nonnegative (by norm_num)
    (by change positionError<12; linarith [error_numbers.2.1])
    (by rw [scale_alpha]; norm_num [mu,Direct.gravityParameter]) hr
    X.continuous_p X.continuous_v ((PointingCapBurn.reference_continuous alpha).add Y.continuous_p)
    ((PointingCapBurn.referenceVelocity_continuous alpha).add Y.continuous_v)
    X.derivative_p X.derivative_v
    (fun t _ => (reference_derivative alpha t).add (Y.derivative_p t))
    (fun t _ => by
      convert (referenceVelocity_derivative alpha t).add (Y.derivative_v t) using 1
      dsimp [qa]; abel)
    (by simpa [q,Y.initial_p] using X.initial_p)
    (by simpa [qv,Y.initial_v] using X.initial_v) hd
  intro t ht
  exact ⟨(h t ht).1,div_le_div_of_nonneg_right (h t ht).2 (by norm_num)⟩

theorem exists_physical_prediction {f : Fin 3 → ℝ} (hf : f 0^2+f 1^2+f 2^2≤sigma^2) (Ω : ℝ) :
    ∃ X : Motion f Ω, ∃ Y : Response f Ω, ∀ t ∈ Icc (0:ℝ) 1,
      ‖X.p t-(reference alpha t+Y.p t)‖≤positionError ∧
      ‖X.v t-(referenceVelocity alpha t+Y.v t)‖/120≤velocityError := by
  obtain ⟨X,_⟩ := exists_motion hf Ω
  exact ⟨X,response f Ω,physical_prediction hf Ω X (response f Ω)⟩

end GNC.OrbitalComparison.SpinningCone
