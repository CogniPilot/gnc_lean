import GNC.Applications.OrbitalComparison.PointingCapBurn
import GNC.Analysis.ConstantSecondOrderBound
import GNC.Analysis.ForcedOscillator

/-! A 1200-second spin-misalignment family in full inverse-square gravity.
The reference is the existing powered circle. Its radial thrust component is
unchanged; a constant-magnitude small transverse component spins in reference
RTN. Angular rate is a prescribed parameter, not an attitude-control proof.
Time is normalized by 1200 s and velocities here are derivatives in that time.
-/
noncomputable section
namespace GNC.OrbitalComparison.SpinningOrbit
open SpatialBurn UniformCertificate PointingCapFrame Set Real

def duration : ℝ := 1200
def forceAmplitude : ℝ := 1/10000
def phase (ω t : ℝ) : ℝ := duration*ω*t
def direction (ω t : ℝ) : E3 := turn 2 t (pack 0 (sin (phase ω t)) (cos (phase ω t)))
def input (ω t : ℝ) : E3 := (144:ℝ) • direction ω t
def thrust (ω t : ℝ) : E3 :=
  (Direct.thrust:ℝ) • turn 2 t e0+forceAmplitude • direction ω t
def acceleration (ω t : ℝ) (p : E3) : E3 := (1440000:ℝ) • (Gravity.field mu p+thrust ω t)

theorem direction_norm (ω t : ℝ) : ‖direction ω t‖=1 := by
  rw [direction,turn_norm]
  have h := pack_norm_sq 0 (sin (phase ω t)) (cos (phase ω t))
  nlinarith [sin_sq_add_cos_sq (phase ω t),
    norm_nonneg (pack 0 (sin (phase ω t)) (cos (phase ω t)))]

theorem input_norm (ω t : ℝ) : ‖input ω t‖=144 := by
  simp [input,norm_smul,direction_norm]

theorem direction_continuous (ω : ℝ) : Continuous (direction ω) := by
  change Continuous (fun t => turn 2 t (pack 0 (sin (phase ω t)) (cos (phase ω t))))
  dsimp [direction,turn,HarmonicFrame.turn,SpatialRotatingFrame.mix,pack,phase,duration]
  fun_prop

theorem thrust_norm_sq (ω t : ℝ) : ‖thrust ω t‖^2=(Direct.thrust:ℝ)^2+forceAmplitude^2 := by
  have he : thrust ω t = turn 2 t
      (pack (Direct.thrust:ℝ) (forceAmplitude*sin (phase ω t)) (forceAmplitude*cos (phase ω t))) := by
    unfold thrust direction
    rw [← map_smul,← map_smul,← map_add]
    congr 1
    ext i
    fin_cases i <;> simp [pack_eq,e0]
  rw [he,turn_norm,pack_norm_sq]
  nlinarith [sin_sq_add_cos_sq (phase ω t)]

theorem reference_normal (t : ℝ) : reference 2 t 2=0 ∧ referenceVelocity 2 t 2=0 := by
  simp [reference,referenceVelocity,SpatialExactNominal.nominal,
    SpatialExactNominal.plane,PoweredCircle.Plane.radial,PoweredCircle.Plane.tangent,
    PoweredCircle.Plane.reference,PoweredCircle.Plane.velocity,e0,e1]

theorem reference_defect (ω t : ℝ) :
    acceleration ω t (reference 2 t)-physicalAcceleration 2 e0 t (reference 2 t)=input ω t := by
  dsimp [acceleration,physicalAcceleration,thrust,input,scale,forceAmplitude]
  module

structure Motion (ω : ℝ) where
  p : ℝ → E3
  v : ℝ → E3
  continuous_p : Continuous p
  continuous_v : Continuous v
  initial_p : p 0=reference 2 0
  initial_v : v 0=referenceVelocity 2 0
  derivative_p : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt p (v t) t
  derivative_v : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt v (acceleration ω t (p t)) t

theorem exists_motion (ω : ℝ) : ∃ X : Motion ω, ∀ t ∈ Icc (0:ℝ) 1,
    (6800000:ℝ)≤‖X.p t‖ := by
  have hd := (direction_continuous ω).const_smul (144:ℝ)
  obtain ⟨x,hx,hx0,hradius,hderiv⟩ := ForcedOrbitExistence.exists_relative_four_gain
    (μ := mu) (scale := 1440000) (r := 6800000) (R := 100000)
    (by norm_num [mu]) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [mu,Direct.gravityParameter])
    (reference 2) (input ω) (PointingCapBurn.reference_continuous 2) hd
    (by intro t; rw [reference_norm]; norm_num)
    (D := 144) (by norm_num) (fun t => (input_norm ω t).le) (by norm_num)
  refine ⟨{
    p := fun t => reference 2 t+(x t).1
    v := fun t => referenceVelocity 2 t+(x t).2
    continuous_p := (PointingCapBurn.reference_continuous 2).add hx.fst
    continuous_v := (PointingCapBurn.referenceVelocity_continuous 2).add hx.snd
    initial_p := by simp [hx0]
    initial_v := by simp [hx0]
    derivative_p := fun t ht => (reference_derivative 2 t).add (hderiv t ht).fst
    derivative_v := ?_ },hradius⟩
  intro t ht
  convert (referenceVelocity_derivative 2 t).add (hderiv t ht).snd using 1
  dsimp [acceleration,physicalAcceleration,ForcedOrbitExistence.rate,input,thrust,scale,forceAmplitude]
  module

def trajectory (ω : ℝ) : Motion ω := Classical.choose (exists_motion ω)

/-- A first-exit bound on the complete spatial trajectory, valid at every
spin rate. Its 100 m closure is checked, not assumed of the unknown orbit. -/
theorem coarse_prediction (ω : ℝ) (X : Motion ω) : ∀ t ∈ Icc (0:ℝ) 1,
    ‖X.p t-reference 2 t‖≤144*PolynomialSupersolution.value 4 1 ∧
    ‖X.v t-referenceVelocity 2 t‖≤144*PolynomialSupersolution.velocity 4 1 := by
  exact Gravity.constant_prediction mu 1440000 (by norm_num [mu]) (by norm_num)
    X.p X.v (reference 2) (referenceVelocity 2)
    (fun t => physicalAcceleration 2 e0 t (reference 2 t)) (thrust ω)
    (κ := 4) (F := 144) (r := 6999900) (M := 100)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [PolynomialSupersolution.value,PolynomialSupersolution.polynomial])
    (by norm_num [mu,Direct.gravityParameter])
    (by intro t _; rw [reference_norm]; norm_num)
    X.continuous_p X.continuous_v (PointingCapBurn.reference_continuous 2)
    (PointingCapBurn.referenceVelocity_continuous 2) X.derivative_p X.derivative_v
    (fun t _ => reference_derivative 2 t) (fun t _ => referenceVelocity_derivative 2 t)
    X.initial_p X.initial_v (by
      intro t _
      change ‖acceleration ω t (reference 2 t)-_‖≤144
      rw [reference_defect,input_norm])

theorem displacement_bound (ω : ℝ) (X : Motion ω) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ‖X.p t-reference 2 t‖≤100 := by
  have h := (coarse_prediction ω X t ht).1
  norm_num [PolynomialSupersolution.value,PolynomialSupersolution.polynomial] at h
  linarith

def gravityGain : ℝ := 1440000*mu/7000000^3
def gravityFrequency : ℝ := sqrt gravityGain
def gravityBudget : ℝ := 1440000*Gravity.remainderBound mu 7000000 100
def gravityResidual (ω : ℝ) (X : Motion ω) (t : ℝ) : E3 :=
  (1440000:ℝ) • (Gravity.field mu (X.p t)-Gravity.field mu (reference 2 t)-
    Gravity.gradient mu (reference 2 t) (X.p t-reference 2 t))

theorem gravity_numbers : 0<gravityGain ∧ gravityGain<2 ∧
    0≤gravityBudget ∧ gravityBudget<718/100000 := by
  norm_num [gravityGain,gravityBudget,Gravity.remainderBound,mu,Direct.gravityParameter]

theorem residual_bound (ω : ℝ) (X : Motion ω) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ‖gravityResidual ω X t‖≤gravityBudget := by
  have h := Gravity.remainder_bound_of_norm_le mu (by norm_num [mu])
    (reference 2 t) (X.p t-reference 2 t) (displacement_bound ω X ht)
    (by rw [reference_norm]; norm_num)
  rw [reference_norm,add_sub_cancel] at h
  simpa [gravityResidual,gravityBudget,norm_smul] using
    mul_le_mul_of_nonneg_left h (by norm_num : (0:ℝ)≤1440000)

theorem scaled_gradient_normal (t : ℝ) (d : E3) :
    ((1440000:ℝ) • Gravity.gradient mu (reference 2 t) d) 2 = -gravityGain*d 2 := by
  simp [Gravity.gradient,reference_norm,(reference_normal t).1,gravityGain]
  ring

theorem normal_acceleration (ω : ℝ) (X : Motion ω) (t : ℝ) :
    acceleration ω t (X.p t) 2 = -gravityGain*X.p t 2+
      144*cos (phase ω t)+(gravityResidual ω X t) 2 := by
  have hg := scaled_gradient_normal t (X.p t-reference 2 t)
  have hr := reference_normal t
  simp only [PiLp.sub_apply,hr.1,sub_zero] at hg
  dsimp [gravityResidual] at *
  have hfield : Gravity.field mu (reference 2 t) 2=0 := by
    simp [Gravity.field,hr.1]
  simp [acceleration,thrust,direction,turn,HarmonicFrame.turn,SpatialRotatingFrame.mix,
    pack_eq,e0,forceAmplitude,hfield] at *
  linarith

end GNC.OrbitalComparison.SpinningOrbit
