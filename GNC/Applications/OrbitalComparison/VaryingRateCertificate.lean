import GNC.Applications.OrbitalComparison.VaryingRatePolynomial
import GNC.Applications.OrbitalComparison.VaryingRateBurn
import GNC.Analysis.PolynomialPhaseCertificate
import GNC.Applications.OrbitalComparison.HarmonicCertificate

/-! Producer-independent rational records for a varying-rate burn.
The retained and quartic representations use identical physical residual
semantics; only their parameter maps and pointing-source budgets differ.
-/
namespace GNC.OrbitalComparison.VaryingRateCertificate
open ParameterPolynomial PointingCapPolynomial

structure Data where
  μ : ℚ
  r : ℚ
  w0 : ℚ
  slope : ℚ
  duration : ℚ
  sigma : ℚ
  kind : VaryingRatePolynomial.Kind
  phase1 : PolynomialPhaseCertificate.Data
  phase2 : PolynomialPhaseCertificate.Data
  q : PointingCapPolynomial.Vector
  first : PointingCapPolynomial.Vector
  remainder : PointingCapPolynomial.Vector
  witness : PointingCapPolynomial.Vector
  positionBound : ℚ
  firstBound : ℚ
  secondBound : ℚ
  residualBound : ℚ
  firstForceBound : ℚ
  secondForceBound : ℚ

def Data.rate (D : Data) : List ℚ := [D.w0,D.slope]
def Data.K (D : Data) : ℚ := D.μ/D.r^3
def Data.radial (D : Data) : List ℚ :=
  PolynomialBounds.scale D.r (PolynomialBounds.subtract [D.K] (PolynomialBounds.multiply D.rate D.rate))
def Data.tangent (D : Data) : List ℚ := [D.r*D.slope]
def Data.positionOperator (D : Data) (q : PointingCapPolynomial.Vector) : PointingCapPolynomial.Vector :=
  let w := VaryingRatePolynomial.time D.rate
  let w2 := multiply w w
  ![add (multiply (add (constant (2*D.K)) w2) (q 0)) (scale D.slope (q 1)),
    subtract (multiply (add (constant (-D.K)) w2) (q 1)) (scale D.slope (q 0)),
    scale (-D.K) (q 2)]
def Data.velocityOperator (D : Data) (v : PointingCapPolynomial.Vector) : PointingCapPolynomial.Vector :=
  ![scale 2 (multiply (VaryingRatePolynomial.time D.rate) (v 1)),
    scale (-2) (multiply (VaryingRatePolynomial.time D.rate) (v 0)),[]]
def Data.quadratic (D : Data) : PointingCapPolynomial.Vector :=
  ![add (scale (-3*D.K/D.r) (multiply (D.first 0) (D.first 0)))
       (scale ((3/2)*D.K/D.r)
         (add (multiply (D.first 1) (D.first 1)) (multiply (D.first 2) (D.first 2)))),
    scale (3*D.K/D.r) (multiply (D.first 0) (D.first 1)),
    scale (3*D.K/D.r) (multiply (D.first 0) (D.first 2))]
def Data.firstForce (D : Data) : PointingCapPolynomial.Vector :=
  let x := VaryingRatePolynomial.time D.radial
  let y := VaryingRatePolynomial.time D.tangent
  let c := VaryingRatePolynomial.time D.phase1.cosine
  let s := VaryingRatePolynomial.time D.phase1.sine
  ![scale (-4/5) y,scale (4/5) x,scale (3/5) (subtract (multiply c x) (multiply s y))]
def Data.secondForce (D : Data) : PointingCapPolynomial.Vector :=
  let x := VaryingRatePolynomial.time D.radial
  let y := VaryingRatePolynomial.time D.tangent
  let c1 := VaryingRatePolynomial.time D.phase1.cosine
  let s1 := VaryingRatePolynomial.time D.phase1.sine
  let c2 := VaryingRatePolynomial.time D.phase2.cosine
  let s2 := VaryingRatePolynomial.time D.phase2.sine
  ![add (subtract (scale (-41/50) x) (scale (9/50) (multiply c2 x))) (scale (9/50) (multiply s2 y)),
    add (add (scale (9/50) (multiply s2 x)) (scale (-41/50) y)) (scale (9/50) (multiply c2 y)),
    scale (-12/25) (add (multiply s1 x) (multiply c1 y))]
def Data.source (D : Data) : PointingCapPolynomial.Vector := fun i =>
  add (multiply (VaryingRatePolynomial.sine D.kind) (D.firstForce i))
    (multiply (VaryingRatePolynomial.cosineLoss D.kind) (D.secondForce i))
def Data.rawResidual (D : Data) : PointingCapPolynomial.Vector :=
  difference (difference (difference (difference
    (PointingCapPolynomial.derivative (PointingCapPolynomial.derivative D.q))
    (D.positionOperator D.q)) (D.velocityOperator (PointingCapPolynomial.derivative D.q)))
    D.source) D.quadratic

def Data.forceBound (D : Data) : ℚ := BernsteinPolynomial.checked D.radial 0 1+
  BernsteinPolynomial.checked D.tangent 0 1
def Data.phaseBudget (D : Data) : ℚ :=
  D.sigma*((3/5)*D.forceBound*D.phase1.error)+
    (D.sigma^2/2)*(D.forceBound*((12/25)*D.phase1.error+(9/25)*D.phase2.error))
def Data.pointingBudget (D : Data) : ℚ := match D.kind with
  | .retained => 0
  | .quartic => D.sigma^5/120*D.firstForceBound+D.sigma^6/720*D.secondForceBound
  | .octic => D.sigma^9/362880*D.firstForceBound+D.sigma^10/3628800*D.secondForceBound
def Data.gravityBudget (D : Data) : ℚ :=
  (3*D.μ/D.r^4)*D.secondBound*(D.positionBound+D.firstBound)+
    (4*D.μ/(D.r-D.positionBound)^5)*D.positionBound^3
def Data.defect (D : Data) : ℚ := D.residualBound+D.phaseBudget+D.pointingBudget+D.gravityBudget
def Data.gain (D : Data) : ℚ := 2*D.μ/(D.r-2*D.positionBound)^3
def Data.positionError (D : Data) : ℚ := D.defect*HarmonicCertificate.positionGain D.gain
def Data.velocityError (D : Data) : ℚ := D.defect*HarmonicCertificate.velocityGain D.gain/D.duration
def Data.existenceForce (D : Data) : ℚ := ((7/5)*D.sigma+(83/100)*D.sigma^2)*D.forceBound
def Data.existenceRadius (D : Data) : ℚ := 10*D.existenceForce
def Data.existenceFloor (D : Data) : ℚ := D.r-2*D.existenceRadius

structure Data.Valid (D : Data) : Prop where
  mu_nonnegative : 0≤D.μ
  radius_pos : 0<D.r
  duration_pos : 0<D.duration
  sigma_nonnegative : 0≤D.sigma
  phase1 : PolynomialPhaseCertificate.Valid D.phase1
  phase2 : PolynomialPhaseCertificate.Valid D.phase2
  phase1_rate : D.phase1.rate=D.rate
  phase2_rate : D.phase2.rate=PolynomialBounds.scale 2 D.rate
  initial_p : ∀ i, initialZero (D.q i)
  initial_v : ∀ i, initialZero (ParameterPolynomial.derivative (D.q i))
  reduction : ∀ i, zero (subtract (D.rawResidual i)
    (add (D.remainder i) (multiply (VaryingRatePolynomial.constraint D.kind) (D.witness i))))
  position : VaryingRatePolynomial.bounded D.q D.sigma D.positionBound
  first : VaryingRatePolynomial.bounded D.first D.sigma D.firstBound
  second : VaryingRatePolynomial.bounded (difference D.q D.first) D.sigma D.secondBound
  residual : VaryingRatePolynomial.bounded D.remainder D.sigma D.residualBound
  first_force : VaryingRatePolynomial.bounded D.firstForce D.sigma D.firstForceBound
  second_force : VaryingRatePolynomial.bounded D.secondForce D.sigma D.secondForceBound
  position_pos : 0<D.positionBound
  position_max : 2*D.positionBound<D.r
  gain_nonnegative : 0≤D.gain
  gain_max : D.gain<56
  defect_nonnegative : 0≤D.defect
  region : D.positionError<D.positionBound
  existence_force : 0≤D.existenceForce
  existence_floor : 0<D.existenceFloor
  existence_gain : (1/4)*(2*D.μ/D.existenceFloor^3)≤1

noncomputable section
open SpatialBurn VaryingRateBurn PolynomialOrder Set

def Data.model (D : Data) : Model := ⟨D.μ,D.r,D.w0,D.slope⟩
def Data.displacement (D : Data) (θ : ℝ) := vectorValue D.q (VaryingRatePolynomial.parameter D.kind θ)
def Data.rotatingVelocity (D : Data) (θ : ℝ) :=
  vectorValue (PointingCapPolynomial.derivative D.q) (VaryingRatePolynomial.parameter D.kind θ)
def Data.rotatingAcceleration (D : Data) (θ : ℝ) :=
  vectorValue (PointingCapPolynomial.derivative (PointingCapPolynomial.derivative D.q))
    (VaryingRatePolynomial.parameter D.kind θ)
def Data.position (D : Data) (θ : ℝ) := VaryingRateFrame.position (D.r:ℝ) D.model.phase (D.displacement θ)
def Data.velocity (D : Data) (θ : ℝ) :=
  VaryingRateFrame.velocity (D.r:ℝ) D.model.phase D.model.rate (D.displacement θ) (D.rotatingVelocity θ)
def Data.acceleration (D : Data) (θ : ℝ) :=
  VaryingRateFrame.acceleration (D.r:ℝ) D.model.phase D.model.rate (fun _ => (D.slope:ℝ))
    (D.displacement θ) (D.rotatingVelocity θ) (D.rotatingAcceleration θ)

theorem Data.rate_value (D : Data) (t : ℝ) : PolynomialOrder.value D.rate t=D.model.rate t := by
  simp [Data.rate,PolynomialOrder.value,Planning.PolynomialKernel.evaluate,Model.rate,Data.model,mul_comm]

theorem Data.radial_value (D : Data) (t : ℝ) : PolynomialOrder.value D.radial t=D.model.radial t := by
  simp only [Data.radial,PolynomialOrder.value_scale,PolynomialOrder.value_subtract]
  have hm (p q : List ℚ) : PolynomialOrder.value (PolynomialBounds.multiply p q) t=
      PolynomialOrder.value p t*PolynomialOrder.value q t := by
    unfold PolynomialOrder.value
    rw [PolynomialBounds.multiply_map,PolynomialBounds.evaluate_multiply]
  rw [hm,D.rate_value]
  simp [PolynomialOrder.value,Planning.PolynomialKernel.evaluate,Data.K,Data.model,Model.radial,pow_two]

theorem Data.tangent_value (D : Data) (t : ℝ) : PolynomialOrder.value D.tangent t=D.model.tangent := by
  simp [Data.tangent,PolynomialOrder.value,Planning.PolynomialKernel.evaluate,Data.model,Model.tangent]

theorem Data.force_bound (D : Data) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    |D.model.radial t|+|D.model.tangent|≤(D.forceBound:ℝ) := by
  simpa only [Data.forceBound,Rat.cast_add,D.radial_value,D.tangent_value] using
    add_le_add (BernsteinPolynomial.checked_sound D.radial (by norm_num : (0:ℚ)<1) (by simpa using ht))
      (BernsteinPolynomial.checked_sound D.tangent (by norm_num : (0:ℚ)<1) (by simpa using ht))

theorem Data.phase1_error (D : Data) (h : D.Valid) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ‖PolynomialPhaseCertificate.candidate D.phase1 t-RotationPhaseCertificate.phase (D.model.phase t)‖≤
      (D.phase1.error:ℝ) := by
  have hb := PolynomialPhaseCertificate.certifies D.phase1 h.phase1 D.model.phase
    (by simp [Model.phase]) (fun s _ => by rw [h.phase1_rate,D.rate_value]; exact D.model.phase_derivative s) ht
  have he : (0:ℝ)≤D.phase1.error := by exact_mod_cast h.phase1.2.2.1
  exact hb.trans (by nlinarith [ht.2])

theorem Data.phase2_error (D : Data) (h : D.Valid) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ‖PolynomialPhaseCertificate.candidate D.phase2 t-RotationPhaseCertificate.phase (2*D.model.phase t)‖≤
      (D.phase2.error:ℝ) := by
  have hb := PolynomialPhaseCertificate.certifies D.phase2 h.phase2 (fun s => 2*D.model.phase s)
    (by simp [Model.phase]) (fun s _ => by
      rw [h.phase2_rate,PolynomialOrder.value_scale,D.rate_value]
      simpa using (D.model.phase_derivative s).const_mul (2:ℝ)) ht
  have he : (0:ℝ)≤D.phase2.error := by exact_mod_cast h.phase2.2.2.1
  exact hb.trans (by nlinarith [ht.2])

theorem Data.firstForce_value (D : Data) (x : Fin 3 → ℝ) (t : ℝ) :
    vectorValue D.firstForce x t=VaryingRateForcing.first (PolynomialPhaseCertificate.candidate D.phase1 t)
      (D.model.radial t) D.model.tangent := by
  ext i
  fin_cases i <;> simp [Data.firstForce,vectorValue,ParameterPolynomial.value_scale,
    ParameterPolynomial.value_subtract,ParameterPolynomial.value_multiply,VaryingRatePolynomial.value_time,
    D.radial_value,D.tangent_value,VaryingRateForcing.first,VaryingRateForcing.s0,VaryingRateForcing.sCos,
    VaryingRateForcing.sSin,PolynomialPhaseCertificate.candidate,PolynomialPhaseCertificate.pair,pack_eq] <;> ring

theorem Data.secondForce_value (D : Data) (x : Fin 3 → ℝ) (t : ℝ) :
    vectorValue D.secondForce x t=VaryingRateForcing.second
      (PolynomialPhaseCertificate.candidate D.phase1 t) (PolynomialPhaseCertificate.candidate D.phase2 t)
      (D.model.radial t) D.model.tangent := by
  ext i
  fin_cases i <;> simp [Data.secondForce,vectorValue,ParameterPolynomial.value_scale,
    ParameterPolynomial.value_subtract,ParameterPolynomial.value_add,ParameterPolynomial.value_multiply,
    VaryingRatePolynomial.value_time,D.radial_value,D.tangent_value,VaryingRateForcing.second,
    VaryingRateForcing.c0,VaryingRateForcing.cCos1,VaryingRateForcing.cSin1,VaryingRateForcing.cCos2,
    VaryingRateForcing.cSin2,PolynomialPhaseCertificate.candidate,PolynomialPhaseCertificate.pair,pack_eq] <;> ring

theorem Data.source_value (D : Data) (x : Fin 3 → ℝ) (t : ℝ) :
    vectorValue D.source x t=
      ParameterPolynomial.value (VaryingRatePolynomial.sine D.kind) x t • vectorValue D.firstForce x t+
      ParameterPolynomial.value (VaryingRatePolynomial.cosineLoss D.kind) x t • vectorValue D.secondForce x t := by
  ext i
  fin_cases i <;> simp [Data.source,vectorValue,ParameterPolynomial.value_add,
    ParameterPolynomial.value_multiply,pack_eq]

def Data.exactPointingSource (D : Data) (θ t : ℝ) : E3 :=
  Real.sin θ • vectorValue D.firstForce (VaryingRatePolynomial.parameter D.kind θ) t+
    (1-Real.cos θ) • vectorValue D.secondForce (VaryingRatePolynomial.parameter D.kind θ) t

theorem Data.pointing_error (D : Data) (h : D.Valid) {θ t : ℝ}
    (hθ : |θ|≤(D.sigma:ℝ)) (ht : t ∈ Icc (0:ℝ) 1) :
    ‖vectorValue D.source (VaryingRatePolynomial.parameter D.kind θ) t-D.exactPointingSource θ t‖≤
      (D.pointingBudget:ℝ) := by
  have hσ : (0:ℝ)≤D.sigma := by exact_mod_cast h.sigma_nonnegative
  rw [D.source_value]
  cases hk : D.kind with
  | retained =>
    simp only [hk,VaryingRatePolynomial.sine_retained,VaryingRatePolynomial.cosine_retained,
      Data.exactPointingSource,Data.pointingBudget]
    simp [hk]
  | quartic =>
    rw [VaryingRatePolynomial.sine_quartic,VaryingRatePolynomial.cosine_quartic]
    have hs := VaryingRatePolynomial.vector_bound D.firstForce h.first_force D.kind hθ ht
    have hc := VaryingRatePolynomial.vector_bound D.secondForce h.second_force D.kind hθ ht
    have hs0 : (0:ℝ)≤D.firstForceBound := by exact_mod_cast h.first_force.1
    have hc0 : (0:ℝ)≤D.secondForceBound := by exact_mod_cast h.second_force.1
    have h5 := div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg θ) hθ 5)
      (by norm_num : (0:ℝ)≤120)
    have h6 := div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg θ) hθ 6)
      (by norm_num : (0:ℝ)≤720)
    have hb := (QuarticPointing.source_bound θ
      (vectorValue D.firstForce (VaryingRatePolynomial.parameter D.kind θ) t)
      (vectorValue D.secondForce (VaryingRatePolynomial.parameter D.kind θ) t)).trans
      (add_le_add (mul_le_mul h5 hs (norm_nonneg _) (by positivity))
        (mul_le_mul h6 hc (norm_nonneg _) (by positivity)))
    rw [norm_sub_rev]
    simpa only [Data.exactPointingSource,Data.pointingBudget,hk,Rat.cast_add,Rat.cast_mul,
      Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat] using hb
  | octic =>
    rw [VaryingRatePolynomial.sine_octic,VaryingRatePolynomial.cosine_octic]
    have hs := VaryingRatePolynomial.vector_bound D.firstForce h.first_force D.kind hθ ht
    have hc := VaryingRatePolynomial.vector_bound D.secondForce h.second_force D.kind hθ ht
    have hs0 : (0:ℝ)≤D.firstForceBound := by exact_mod_cast h.first_force.1
    have hc0 : (0:ℝ)≤D.secondForceBound := by exact_mod_cast h.second_force.1
    have h9 := div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg θ) hθ 9)
      (by norm_num : (0:ℝ)≤362880)
    have h10 := div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg θ) hθ 10)
      (by norm_num : (0:ℝ)≤3628800)
    have hb := (OcticPointing.source_bound θ
      (vectorValue D.firstForce (VaryingRatePolynomial.parameter D.kind θ) t)
      (vectorValue D.secondForce (VaryingRatePolynomial.parameter D.kind θ) t)).trans
      (add_le_add (mul_le_mul h9 hs (norm_nonneg _) (by positivity))
        (mul_le_mul h10 hc (norm_nonneg _) (by positivity)))
    rw [norm_sub_rev]
    simpa only [Data.exactPointingSource,Data.pointingBudget,hk,Rat.cast_add,Rat.cast_mul,
      Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat] using hb

theorem Data.phase_error (D : Data) (h : D.Valid) {θ t : ℝ}
    (hθ : |θ|≤(D.sigma:ℝ)) (ht : t ∈ Icc (0:ℝ) 1) :
    ‖D.exactPointingSource θ t-D.model.source θ t‖≤(D.phaseBudget:ℝ) := by
  have hb := VaryingRateForcing.approximation_error θ (D.model.phase t) (D.model.radial t)
    D.model.tangent (PolynomialPhaseCertificate.candidate D.phase1 t)
    (PolynomialPhaseCertificate.candidate D.phase2 t) hθ (D.force_bound ht)
    (D.phase1_error h ht) (D.phase2_error h ht)
  simpa only [Data.exactPointingSource,D.firstForce_value,D.secondForce_value,
    VaryingRateForcing.approximation,Model.source,Data.phaseBudget,Rat.cast_add,
    Rat.cast_mul,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat] using hb

theorem Data.source_bound (D : Data) (h : D.Valid) {θ t : ℝ}
    (hθ : |θ|≤(D.sigma:ℝ)) (ht : t ∈ Icc (0:ℝ) 1) :
    ‖vectorValue D.source (VaryingRatePolynomial.parameter D.kind θ) t-D.model.source θ t‖≤
      (D.phaseBudget:ℝ)+(D.pointingBudget:ℝ) := by
  have hn := (norm_sub_le_norm_sub_add_norm_sub
    (vectorValue D.source (VaryingRatePolynomial.parameter D.kind θ) t)
    (D.exactPointingSource θ t) (D.model.source θ t)).trans
    (add_le_add (D.pointing_error h hθ ht) (D.phase_error h hθ ht))
  linarith

theorem Data.positionOperator_value (D : Data) (p : PointingCapPolynomial.Vector) (x : Fin 3 → ℝ) (t : ℝ) :
    vectorValue (D.positionOperator p) x t=VaryingRateFrame.positionOperator
      ((D.K:ℚ):ℝ) (D.model.rate t) (D.slope:ℝ) (vectorValue p x t) := by
  ext i
  fin_cases i <;> simp [Data.positionOperator,vectorValue,ParameterPolynomial.value_scale,
    ParameterPolynomial.value_add,ParameterPolynomial.value_subtract,ParameterPolynomial.value_multiply,
    ParameterPolynomial.value_constant,VaryingRatePolynomial.value_time,D.rate_value,
    VaryingRateFrame.positionOperator,pack_eq] <;> ring
  all_goals simp

theorem Data.velocityOperator_value (D : Data) (p : PointingCapPolynomial.Vector) (x : Fin 3 → ℝ) (t : ℝ) :
    vectorValue (D.velocityOperator p) x t=VaryingRateFrame.velocityOperator
      (D.model.rate t) (vectorValue p x t) := by
  ext i
  fin_cases i <;> simp [Data.velocityOperator,vectorValue,ParameterPolynomial.value_scale,
    ParameterPolynomial.value_multiply,VaryingRatePolynomial.value_time,D.rate_value,
    VaryingRateFrame.velocityOperator,pack_eq] <;> ring

theorem Data.quadratic_value (D : Data) (x : Fin 3 → ℝ) (t : ℝ) :
    vectorValue D.quadratic x t=VaryingRateFrame.quadratic (D.K:ℝ) (D.r:ℝ) (vectorValue D.first x t) := by
  ext i
  fin_cases i <;> simp [Data.quadratic,vectorValue,ParameterPolynomial.value_scale,
    ParameterPolynomial.value_add,ParameterPolynomial.value_multiply,VaryingRateFrame.quadratic,pack_eq] <;> ring

theorem Data.rawResidual_value (D : Data) (θ t : ℝ) :
    vectorValue D.rawResidual (VaryingRatePolynomial.parameter D.kind θ) t=
      VaryingRateFrame.residual (D.K:ℝ) (D.r:ℝ) (D.model.rate t) (D.slope:ℝ)
        (D.displacement θ t) (D.rotatingVelocity θ t) (D.rotatingAcceleration θ t)
        (vectorValue D.first (VaryingRatePolynomial.parameter D.kind θ) t)
        (vectorValue D.source (VaryingRatePolynomial.parameter D.kind θ) t) := by
  simp only [Data.rawResidual,vector_difference,D.positionOperator_value,D.velocityOperator_value,
    D.quadratic_value,VaryingRateFrame.residual,Data.displacement,Data.rotatingVelocity,Data.rotatingAcceleration]

theorem Data.complete_defect_of_residual (D : Data) (h : D.Valid) {θ t L : ℝ}
    (hθ : |θ|≤(D.sigma:ℝ)) (ht : t ∈ Icc (0:ℝ) 1)
    (hres : ‖vectorValue D.remainder (VaryingRatePolynomial.parameter D.kind θ) t‖≤L) :
    ‖D.model.acceleration θ t (D.position θ t)-D.acceleration θ t‖≤
      L+(D.phaseBudget:ℝ)+(D.pointingBudget:ℝ)+(D.gravityBudget:ℝ) := by
  have hb (p : PointingCapPolynomial.Vector) (B : ℚ) (hp : VaryingRatePolynomial.bounded p D.sigma B) :=
    VaryingRatePolynomial.vector_bound p hp D.kind hθ ht
  have hr : vectorValue D.rawResidual (VaryingRatePolynomial.parameter D.kind θ) t=
      vectorValue D.remainder (VaryingRatePolynomial.parameter D.kind θ) t := by
    ext i
    fin_cases i <;> simp [vectorValue,pack_eq,VaryingRatePolynomial.reduced_residual _ _ _ _ (h.reduction _) θ t]
  have hL := hres
  rw [←hr,D.rawResidual_value] at hL
  have hK : (D.K:ℝ)=(D.μ:ℝ)/(D.r:ℝ)^3 := by simp [Data.K]
  rw [hK] at hL
  have hP : (D.positionBound:ℝ)<(D.r:ℝ) := by
    have hm : 2*(D.positionBound:ℝ)<(D.r:ℝ) := by exact_mod_cast h.position_max
    have hp : (0:ℝ)<D.positionBound := by exact_mod_cast h.position_pos
    linarith
  have hg := VaryingRateFrame.physical_defect_bound (D.μ:ℝ) (D.r:ℝ)
    (by exact_mod_cast h.mu_nonnegative) (by exact_mod_cast h.radius_pos)
    D.model.phase D.model.rate (fun _ => (D.slope:ℝ)) (D.displacement θ)
    (D.rotatingVelocity θ) (D.rotatingAcceleration θ)
    (vectorValue D.first (VaryingRatePolynomial.parameter D.kind θ))
    (vectorValue D.source (VaryingRatePolynomial.parameter D.kind θ) t) (D.model.source θ t) t
    hP (hb _ _ h.position) (hb _ _ h.first)
    (by simpa only [vector_difference] using hb _ _ h.second) hL (D.source_bound h hθ ht)
  rw [D.model.acceleration_frame]
  convert hg using 1
  simp [Data.gravityBudget]
  ring

theorem Data.complete_defect_bound (D : Data) (h : D.Valid) {θ t : ℝ}
    (hθ : |θ|≤(D.sigma:ℝ)) (ht : t ∈ Icc (0:ℝ) 1) :
    ‖D.model.acceleration θ t (D.position θ t)-D.acceleration θ t‖≤(D.defect:ℝ) := by
  have hb := D.complete_defect_of_residual h hθ ht
    (VaryingRatePolynomial.vector_bound D.remainder h.residual D.kind hθ ht)
  simpa only [Data.defect,Rat.cast_add] using hb

theorem Data.initial (D : Data) (h : D.Valid) (θ : ℝ) :
    D.displacement θ 0=0 ∧ D.rotatingVelocity θ 0=0 := by
  constructor <;> ext i <;> fin_cases i <;>
    simp [Data.displacement,Data.rotatingVelocity,vectorValue,pack_eq,
      initial_value _ (h.initial_p _),PointingCapPolynomial.derivative,
      initial_value _ (h.initial_v _)]

theorem Data.displacement_derivative (D : Data) (θ t : ℝ) :
    HasDerivAt (D.displacement θ) (D.rotatingVelocity θ t) t :=
  vector_derivative D.q (VaryingRatePolynomial.parameter D.kind θ) t
theorem Data.rotatingVelocity_derivative (D : Data) (θ t : ℝ) :
    HasDerivAt (D.rotatingVelocity θ) (D.rotatingAcceleration θ t) t :=
  vector_derivative (PointingCapPolynomial.derivative D.q) (VaryingRatePolynomial.parameter D.kind θ) t
theorem Data.position_derivative (D : Data) (θ t : ℝ) :
    HasDerivAt (D.position θ) (D.velocity θ t) t :=
  VaryingRateFrame.position_derivative _ (D.model.phase_derivative t) (D.displacement_derivative θ t)
theorem Data.velocity_derivative (D : Data) (θ t : ℝ) :
    HasDerivAt (D.velocity θ) (D.acceleration θ t) t :=
  VaryingRateFrame.velocity_derivative _ (D.model.phase_derivative t) (D.model.rate_derivative t)
    (D.displacement_derivative θ t) (D.rotatingVelocity_derivative θ t)

/-- A valid record bounds every full inverse-square solution throughout the
burn and the angle interval. The physical error tube is closed by first exit;
no bound on the unknown physical trajectory is assumed. -/
theorem Data.certifies (D : Data) (h : D.Valid) {θ : ℝ}
    (hθ : |θ|≤(D.sigma:ℝ)) (X : Motion D.model θ) :
    ∀ t ∈ Icc (0:ℝ) 1,
      ‖X.p t-D.position θ t‖≤(D.positionError:ℝ) ∧
      ‖X.v t-D.velocity θ t‖/(D.duration:ℝ)≤(D.velocityError:ℝ) := by
  have hr : (0:ℝ)<D.r := by exact_mod_cast h.radius_pos
  have hmax : 2*(D.positionBound:ℝ)<(D.r:ℝ) := by exact_mod_cast h.position_max
  have hT : (0:ℝ)<D.duration := by exact_mod_cast h.duration_pos
  have hclose : (D.defect:ℝ)*PolynomialSupersolution.value (D.gain:ℝ) 1<(D.positionBound:ℝ) := by
    have hh : (D.positionError:ℝ)<(D.positionBound:ℝ) := by exact_mod_cast h.region
    simpa only [Data.positionError,Rat.cast_mul,HarmonicCertificate.positionGain_cast] using hh
  have hq (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      (D.r:ℝ)-2*(D.positionBound:ℝ)+(D.positionBound:ℝ)≤‖D.position θ t‖ := by
    have hd := VaryingRatePolynomial.vector_bound D.q h.position D.kind hθ ht
    have hn := norm_sub_le (D.position θ t) (VaryingRateFrame.turn (D.model.phase t) (D.displacement θ t))
    have he : D.position θ t-VaryingRateFrame.turn (D.model.phase t) (D.displacement θ t)=
        D.model.reference t := by simp [Data.position,VaryingRateFrame.position,Model.reference,Data.model]
    rw [he,D.model.reference_norm hr.le,VaryingRateFrame.turn_norm] at hn
    change ‖D.displacement θ t‖≤(D.positionBound:ℝ) at hd
    change (D.r:ℝ)≤_ at hn
    linarith
  have hi := D.initial h θ
  have hb := Gravity.constant_prediction (D.μ:ℝ) 1
    (by exact_mod_cast h.mu_nonnegative) (by norm_num)
    X.p X.v (D.position θ) (D.velocity θ) (D.acceleration θ) (D.model.thrust θ)
    (show (0:ℝ)≤D.gain by exact_mod_cast h.gain_nonnegative)
    (show (D.gain:ℝ)<56 by exact_mod_cast h.gain_max)
    (show (0:ℝ)≤D.defect by exact_mod_cast h.defect_nonnegative)
    (r := (D.r:ℝ)-2*(D.positionBound:ℝ)) (by linarith) hclose
    (by simp [Data.gain]) hq X.continuous_p X.continuous_v
    (continuous_iff_continuousAt.mpr fun t => (D.position_derivative θ t).continuousAt)
    (continuous_iff_continuousAt.mpr fun t => (D.velocity_derivative θ t).continuousAt)
    X.derivative_p
    (fun t ht => by simpa [Model.acceleration,Data.model] using X.derivative_v t ht)
    (fun t _ => D.position_derivative θ t) (fun t _ => D.velocity_derivative θ t)
    (by simpa [Data.position,VaryingRateFrame.position,Model.reference,Data.model,hi.1] using X.initial_p)
    (by simpa [Data.velocity,VaryingRateFrame.velocity,Model.referenceVelocity,Data.model,hi.1,hi.2] using X.initial_v)
    (fun t ht => by simpa [Model.acceleration,Data.model] using D.complete_defect_bound h hθ ht)
  intro t ht
  constructor
  · simpa only [Data.positionError,Rat.cast_mul,HarmonicCertificate.positionGain_cast] using (hb t ht).1
  · have hv := div_le_div_of_nonneg_right (hb t ht).2 hT.le
    simpa only [Data.velocityError,Rat.cast_div,Rat.cast_mul,
      HarmonicCertificate.velocityGain_cast] using hv

/-- Existence is established from the same input record. Its coarse radius
is computed from the forcing bound and is separate from the error budget. -/
theorem Data.exists_motion (D : Data) (h : D.Valid) {θ : ℝ}
    (hθ : |θ|≤(D.sigma:ℝ)) :
    ∃ X : Motion D.model θ, ∀ t ∈ Icc (0:ℝ) 1, (D.existenceFloor:ℝ)≤‖X.p t‖ := by
  apply D.model.exists_motion
    (show (0:ℝ)≤D.μ by exact_mod_cast h.mu_nonnegative)
    (show (0:ℝ)<D.r by exact_mod_cast h.radius_pos) θ
    (R := D.existenceRadius) (D := (D.existenceForce:ℝ))
    (by exact_mod_cast h.existence_floor)
    (by dsimp [Data.existenceRadius]; exact mul_nonneg (by norm_num) h.existence_force)
    (by change (1/4:ℝ)*(2*(D.μ:ℝ)/(D.existenceFloor:ℝ)^3)≤1
        have hh : (((1/4)*(2*D.μ/D.existenceFloor^3):ℚ):ℝ)≤((1:ℚ):ℝ) :=
          Rat.cast_le.mpr h.existence_gain
        simpa only [Rat.cast_mul,Rat.cast_div,Rat.cast_pow,Rat.cast_one,Rat.cast_ofNat] using hh)
    (by simp [Data.existenceFloor,Data.model])
    (by exact_mod_cast h.existence_force)
    (fun t ht => ?_) (by simp [Data.existenceRadius])
  have hb := D.model.relativeThrust_bound θ t hθ (D.force_bound ht)
  simpa only [Data.existenceForce,Rat.cast_mul,Rat.cast_add,Rat.cast_div,
    Rat.cast_pow,Rat.cast_ofNat] using hb

/-- Nonvacuous certificate: an actual full-gravity motion exists, and the
same error bounds hold for every motion satisfying the specified ODE. -/
theorem Data.physical_prediction (D : Data) (h : D.Valid) {θ : ℝ}
    (hθ : |θ|≤(D.sigma:ℝ)) :
    (∃ X : Motion D.model θ, ∀ t ∈ Icc (0:ℝ) 1, (D.existenceFloor:ℝ)≤‖X.p t‖) ∧
    (∀ X : Motion D.model θ, ∀ t ∈ Icc (0:ℝ) 1,
      ‖X.p t-D.position θ t‖≤(D.positionError:ℝ) ∧
      ‖X.v t-D.velocity θ t‖/(D.duration:ℝ)≤(D.velocityError:ℝ)) :=
  ⟨D.exists_motion h hθ,fun X => D.certifies h hθ X⟩

end
end GNC.OrbitalComparison.VaryingRateCertificate
