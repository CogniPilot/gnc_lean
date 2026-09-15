import GNC.Dynamics.LieErrorReconstruction
import GNC.Applications.OrbitalComparison.VaryingRateTimeCertificate
import GNC.Analysis.ParameterPolynomialL1

/-! Transfer an independently checked polynomial surrogate to the factored
SE2(3) output. The polynomial expansion is an offline proof witness; neither
coefficient propagation nor a runtime query needs to execute that expansion.
Every discarded time coefficient, rounded coefficient and phase tail is
charged by this transfer. This is a real-arithmetic certificate. -/
namespace GNC.OrbitalComparison.LieSTTOutput
open ParameterPolynomial PointingCapPolynomial VaryingRateCertificate SpatialBurn Set Matrix

def cross (a b : PointingCapPolynomial.Vector) : PointingCapPolynomial.Vector :=
  ![subtract (multiply (a 1) (b 2)) (multiply (a 2) (b 1)),
    subtract (multiply (a 2) (b 0)) (multiply (a 0) (b 2)),
    subtract (multiply (a 0) (b 1)) (multiply (a 1) (b 0))]
def axisPolynomial (D : Data) : PointingCapPolynomial.Vector :=
  ![scale (-3/5) (VaryingRatePolynomial.time D.phase1.sine),
    scale (-3/5) (VaryingRatePolynomial.time D.phase1.cosine),constant (4/5)]
def reconstruction (D : Data) (z : PointingCapPolynomial.Vector) : PointingCapPolynomial.Vector :=
  fun i => add (add (multiply u (z i))
    (multiply (VaryingRatePolynomial.cosineLoss .octic) (cross (axisPolynomial D) z i)))
    (multiply (subtract u (VaryingRatePolynomial.sine .octic))
      (cross (axisPolynomial D) (cross (axisPolynomial D) z) i))
def covariantVelocity (D : Data) (q : PointingCapPolynomial.Vector) : PointingCapPolynomial.Vector :=
  ![subtract (ParameterPolynomial.derivative (q 0)) (multiply (VaryingRatePolynomial.time D.rate) (q 1)),
    add (ParameterPolynomial.derivative (q 1)) (multiply (VaryingRatePolynomial.time D.rate) (q 0)),
    ParameterPolynomial.derivative (q 2)]

structure Slot where
  z : PointingCapPolynomial.Vector
  residual : PointingCapPolynomial.Vector
  zBound : ℚ
  residualBound : ℚ
def tailBounded (p : PointingCapPolynomial.Vector) (σ B : ℚ) : Prop :=
  0≤B ∧ (l1Bound (p 0) (VaryingRatePolynomial.radius σ))^2+
    (l1Bound (p 1) (VaryingRatePolynomial.radius σ))^2+
    (l1Bound (p 2) (VaryingRatePolynomial.radius σ))^2≤B^2
instance (p : PointingCapPolynomial.Vector) (σ B : ℚ) : Decidable (tailBounded p σ B) := by
  unfold tailBounded
  infer_instance
structure Slot.Valid (S : Slot) (D : Data) (q : PointingCapPolynomial.Vector) : Prop where
  identity : ∀ i, zero (subtract (subtract (reconstruction D S.z i) (q i)) (S.residual i))
  z : VaryingRatePolynomial.bounded S.z D.sigma S.zBound
  residual : tailBounded S.residual D.sigma S.residualBound

def axisError (D : Data) : ℚ := (6/5)*D.phase1.error
def cosineBound (D : Data) : ℚ :=
  bound (VaryingRatePolynomial.cosineLoss .octic) (VaryingRatePolynomial.radius D.sigma)
def sineBound (D : Data) : ℚ :=
  bound (subtract u (VaryingRatePolynomial.sine .octic)) (VaryingRatePolynomial.radius D.sigma)
def Slot.error (S : Slot) (D : Data) : ℚ := S.residualBound+
  (D.sigma^9/362880+D.sigma^10/3628800+
    (cosineBound D)*(axisError D)+(sineBound D)*(axisError D)*(2+(axisError D)))*S.zBound

noncomputable section
def value3 (p : PointingCapPolynomial.Vector) (x : Fin 3 → ℝ) (t : ℝ) : Vec3 :=
  fun i => value (p i) x t
def axis (φ : ℝ) : Vec3 := ![-(3/5)*Real.sin φ,-(3/5)*Real.cos φ,4/5]
def Slot.output (S : Slot) (D : Data) (θ t : ℝ) : E3 :=
  WithLp.toLp 2 (factoredTranslation (axis (D.model.phase t))
    (value3 S.z (VaryingRatePolynomial.parameter .octic θ) t) θ)

theorem value3_norm (p : PointingCapPolynomial.Vector) (x : Fin 3 → ℝ) (t : ℝ) :
    enorm (value3 p x t)=‖vectorValue p x t‖ := by
  congr 1
  ext i
  fin_cases i <;> simp [value3,vectorValue,pack,e0,e1,e2]

theorem tailBounded_sound (p : PointingCapPolynomial.Vector) {σ B : ℚ}
    (hp : tailBounded p σ B) {θ t : ℝ} (hθ : |θ|≤(σ:ℝ)) (ht : t ∈ Icc (0:ℝ) 1) :
    ‖vectorValue p (VaryingRatePolynomial.parameter .octic θ) t‖≤(B:ℝ) := by
  have hb (i : Fin 3) := l1Bound_sound (p i) (VaryingRatePolynomial.parameter_bound .octic hθ) ht
  have hs (i : Fin 3) : (value (p i) (VaryingRatePolynomial.parameter .octic θ) t)^2≤
      (l1Bound (p i) (VaryingRatePolynomial.radius σ):ℝ)^2 := by
    have hi := hb i
    nlinarith [abs_nonneg (value (p i) (VaryingRatePolynomial.parameter .octic θ) t),
      sq_abs (value (p i) (VaryingRatePolynomial.parameter .octic θ) t)]
  have hB : (0:ℝ)≤B := by exact_mod_cast hp.1
  have hsum : (l1Bound (p 0) (VaryingRatePolynomial.radius σ):ℝ)^2+
      (l1Bound (p 1) (VaryingRatePolynomial.radius σ):ℝ)^2+
      (l1Bound (p 2) (VaryingRatePolynomial.radius σ):ℝ)^2≤(B:ℝ)^2 := by exact_mod_cast hp.2
  have hn := pack_norm_sq (value (p 0) (VaryingRatePolynomial.parameter .octic θ) t)
    (value (p 1) (VaryingRatePolynomial.parameter .octic θ) t)
    (value (p 2) (VaryingRatePolynomial.parameter .octic θ) t)
  change ‖vectorValue p (VaryingRatePolynomial.parameter .octic θ) t‖^2=_ at hn
  nlinarith [hs 0,hs 1,hs 2,norm_nonneg (vectorValue p (VaryingRatePolynomial.parameter .octic θ) t)]
theorem cross_value (a b : PointingCapPolynomial.Vector) (x : Fin 3 → ℝ) (t : ℝ) :
    value3 (cross a b) x t=value3 a x t ⨯₃ value3 b x t := by
  ext i
  fin_cases i <;> simp [cross,value3,value_subtract,value_multiply,crossProduct]
theorem axis_unit (φ : ℝ) : axis φ ⬝ᵥ axis φ=1 := by
  simp [axis,dotProduct,Fin.sum_univ_succ]
  nlinarith [Real.sin_sq_add_cos_sq φ]
theorem axis_error (D : Data) (hD : D.Valid) {θ t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    enorm (axis (D.model.phase t)-value3 (axisPolynomial D)
      (VaryingRatePolynomial.parameter .octic θ) t)≤((axisError D):ℝ) := by
  have hc := (RotationPhaseCertificate.real_error_le (D.model.phase t)
    (PolynomialPhaseCertificate.candidate D.phase1 t)).trans (D.phase1_error hD ht)
  have hs := (RotationPhaseCertificate.imag_error_le (D.model.phase t)
    (PolynomialPhaseCertificate.candidate D.phase1 t)).trans (D.phase1_error hD ht)
  simp only [PolynomialPhaseCertificate.candidate,PolynomialPhaseCertificate.pair,
    Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,Complex.add_im,Complex.mul_im] at hc hs
  simp only [mul_zero,zero_mul,sub_zero,add_zero,mul_one,zero_add] at hc hs
  have he : axis (D.model.phase t)-value3 (axisPolynomial D)
      (VaryingRatePolynomial.parameter .octic θ) t=
      ![(3/5)*(PolynomialOrder.value D.phase1.sine t-Real.sin (D.model.phase t)),
        (3/5)*(PolynomialOrder.value D.phase1.cosine t-Real.cos (D.model.phase t)),0] := by
    ext i
    fin_cases i <;> simp [axis,value3,axisPolynomial,value_scale,value_constant] <;> ring
  rw [he]
  have hb := pack_norm_le ((3/5)*(PolynomialOrder.value D.phase1.sine t-Real.sin (D.model.phase t)))
    ((3/5)*(PolynomialOrder.value D.phase1.cosine t-Real.cos (D.model.phase t))) 0
  rw [pack_eq] at hb
  change enorm _≤_ at hb
  simp only [abs_mul,abs_zero,add_zero] at hb
  norm_num only [abs_of_pos (by norm_num : (0:ℝ)<3/5)] at hb
  have herr : ((axisError D):ℝ)=(6/5)*(D.phase1.error:ℝ) := by simp [axisError]
  rw [herr]
  linarith

theorem reconstruction_value (D : Data) (z : PointingCapPolynomial.Vector) (θ t : ℝ) :
    value3 (reconstruction D z) (VaryingRatePolynomial.parameter .octic θ) t=
      polynomialTranslation (value3 (axisPolynomial D) (VaryingRatePolynomial.parameter .octic θ) t)
        (value3 z (VaryingRatePolynomial.parameter .octic θ) t) θ := by
  have hparam : VaryingRatePolynomial.parameter .octic θ 0=θ := rfl
  simp only [polynomialTranslation,←cross_value]
  ext i
  simp only [value3,reconstruction,value_add,value_multiply,value_subtract,
    VaryingRatePolynomial.cosine_octic,VaryingRatePolynomial.sine_octic,
    value_u,hparam,
    Pi.add_apply,Pi.smul_apply,smul_eq_mul]

theorem Slot.certifies (S : Slot) (D : Data) (q : PointingCapPolynomial.Vector)
    (hD : D.Valid) (hS : S.Valid D q) {θ t : ℝ}
    (hθ : |θ|≤(D.sigma:ℝ)) (ht : t ∈ Icc (0:ℝ) 1) :
    ‖S.output D θ t-vectorValue q (VaryingRatePolynomial.parameter .octic θ) t‖≤(S.error D:ℝ) := by
  let x := VaryingRatePolynomial.parameter .octic θ
  let z := value3 S.z x t
  let k := axis (D.model.phase t)
  let khat := value3 (axisPolynomial D) x t
  have hz : enorm z≤(S.zBound:ℝ) := by
    rw [value3_norm]
    exact VaryingRatePolynomial.vector_bound S.z hS.z .octic hθ ht
  have hres : enorm (polynomialTranslation khat z θ-value3 q x t)≤(S.residualBound:ℝ) := by
    have he : polynomialTranslation khat z θ-value3 q x t=value3 S.residual x t := by
      rw [←reconstruction_value]
      ext i
      have hh := ParameterPolynomial.identity (subtract (reconstruction D S.z i) (q i))
        (S.residual i) (hS.identity i) x t
      simpa only [value_subtract] using hh
    rw [he,value3_norm]
    exact tailBounded_sound S.residual hS.residual hθ ht
  have hC : |OcticPointing.cosineLoss θ|≤((cosineBound D):ℝ) := by
    simpa only [VaryingRatePolynomial.cosine_octic] using
      ParameterPolynomial.bound_sound (VaryingRatePolynomial.cosineLoss .octic)
        (VaryingRatePolynomial.parameter_bound .octic hθ) ht
  have hparam : VaryingRatePolynomial.parameter .octic θ 0=θ := rfl
  have hH : |θ-OcticPointing.sine θ|≤((sineBound D):ℝ) := by
    simpa only [value_subtract,value_u,hparam,VaryingRatePolynomial.sine_octic] using
      ParameterPolynomial.bound_sound (subtract u (VaryingRatePolynomial.sine .octic))
        (VaryingRatePolynomial.parameter_bound .octic hθ) ht
  have ht1 := factoredTranslation_polynomial_bound k z (axis_unit _) θ
  have ht2 := polynomialTranslation_axis_bound k khat z θ
    (le_of_eq (Gravity.unit_enorm k (axis_unit _))) (axis_error D hD ht) hC hH
  have hσ0 : (0:ℝ)≤D.sigma := (abs_nonneg θ).trans hθ
  have h9 := pow_le_pow_left₀ (abs_nonneg θ) hθ 9
  have h10 := pow_le_pow_left₀ (abs_nonneg θ) hθ 10
  have hd0 : (0:ℝ)≤(axisError D) := (enorm_nonneg _).trans (axis_error D hD (θ:=θ) ht)
  have hc0 : (0:ℝ)≤(cosineBound D) := (abs_nonneg _).trans hC
  have hh0 : (0:ℝ)≤(sineBound D) := (abs_nonneg _).trans hH
  have ht1' : enorm (factoredTranslation k z θ-polynomialTranslation k z θ)≤
      ((D.sigma:ℝ)^9/362880+(D.sigma:ℝ)^10/3628800)*(S.zBound:ℝ) := by
    exact ht1.trans (mul_le_mul (by linarith) hz (enorm_nonneg z) (by positivity))
  have ht2' := ht2.trans (mul_le_mul_of_nonneg_left hz (by positivity))
  have ha := (enorm_add_le (factoredTranslation k z θ-polynomialTranslation k z θ)
    (polynomialTranslation k z θ-polynomialTranslation khat z θ)).trans (add_le_add ht1' ht2')
  have hb := (enorm_add_le ((factoredTranslation k z θ-polynomialTranslation k z θ)+
    (polynomialTranslation k z θ-polynomialTranslation khat z θ))
    (polynomialTranslation khat z θ-value3 q x t)).trans (add_le_add ha hres)
  have he : (factoredTranslation k z θ-polynomialTranslation k z θ)+
      (polynomialTranslation k z θ-polynomialTranslation khat z θ)+
      (polynomialTranslation khat z θ-value3 q x t)=factoredTranslation k z θ-value3 q x t := by module
  rw [he] at hb
  have hv : vectorValue q x t=WithLp.toLp 2 (value3 q x t) := by
    ext i
    fin_cases i <;> simp [vectorValue,value3,pack,e0,e1,e2]
  rw [hv]
  change enorm (factoredTranslation k z θ-value3 q x t)≤_
  convert hb using 1 <;> simp [Slot.error] <;> ring

theorem covariantVelocity_value (D : Data) (q : PointingCapPolynomial.Vector)
    (x : Fin 3 → ℝ) (t : ℝ) :
    vectorValue (covariantVelocity D q) x t=vectorValue (PointingCapPolynomial.derivative q) x t+
      VaryingRateFrame.spin (D.model.rate t) (vectorValue q x t) := by
  ext i
  fin_cases i <;> simp [vectorValue,covariantVelocity,PointingCapPolynomial.derivative,
    value_add,value_subtract,value_multiply,D.rate_value,VaryingRateFrame.spin,pack_eq] <;> ring

def Slot.physicalPosition (S : Slot) (D : Data) (θ t : ℝ) : E3 :=
  D.model.reference t+VaryingRateFrame.turn (D.model.phase t) (S.output D θ t)
def Slot.physicalVelocity (S : Slot) (D : Data) (θ t : ℝ) : E3 :=
  D.model.referenceVelocity t+VaryingRateFrame.turn (D.model.phase t) (S.output D θ t)

theorem physical_certificate (P V : Slot) (D : Data) (M : VaryingRateTimeCertificate.Profile)
    (hD : D.Valid) (hM : M.Valid D) (hk : D.kind=.octic)
    (hP : P.Valid D D.q) (hV : V.Valid D (covariantVelocity D D.q))
    {θ : ℝ} (hθ : |θ|≤(D.sigma:ℝ)) (X : VaryingRateBurn.Motion D.model θ)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ‖X.p t-P.physicalPosition D θ t‖≤((M.positionError+P.error D:ℚ):ℝ) ∧
    ‖X.v t-V.physicalVelocity D θ t‖/(D.duration:ℝ)≤
      ((M.velocityError D+V.error D/D.duration:ℚ):ℝ) := by
  have hbase := M.certifies D hD hM hθ X t ht
  have hp := P.certifies D D.q hD hP hθ ht
  have hv := V.certifies D (covariantVelocity D D.q) hD hV hθ ht
  have hp' : ‖D.position θ t-P.physicalPosition D θ t‖≤(P.error D:ℝ) := by
    simpa only [Slot.physicalPosition,Data.position,VaryingRateFrame.position,
      VaryingRateBurn.Model.reference,Data.model,Data.displacement,hk,
      add_sub_add_left_eq_sub,←map_sub,VaryingRateFrame.turn_norm,norm_sub_rev] using hp
  have hv' : ‖D.velocity θ t-V.physicalVelocity D θ t‖≤(V.error D:ℝ) := by
    rw [covariantVelocity_value] at hv
    simpa only [Slot.physicalVelocity,Data.velocity,VaryingRateFrame.velocity,
      VaryingRateBurn.Model.referenceVelocity,Data.model,Data.displacement,Data.rotatingVelocity,hk,
      add_sub_add_left_eq_sub,←map_sub,VaryingRateFrame.turn_norm,norm_sub_rev] using hv
  have hT : (0:ℝ)≤D.duration := by exact_mod_cast hD.duration_pos.le
  have tri (a b c : E3) : ‖a-c‖≤‖a-b‖+‖b-c‖ := by
    simpa only [dist_eq_norm] using dist_triangle a b c
  constructor
  · exact (tri _ _ _).trans (by simpa only [Rat.cast_add] using add_le_add hbase.1 hp')
  · have ha := div_le_div_of_nonneg_right (tri (X.v t) (D.velocity θ t)
        (V.physicalVelocity D θ t)) hT
    rw [add_div] at ha
    exact ha.trans (by
      simpa only [Rat.cast_add,Rat.cast_div] using
        add_le_add hbase.2 (div_le_div_of_nonneg_right hv' hT))

end
end GNC.OrbitalComparison.LieSTTOutput
