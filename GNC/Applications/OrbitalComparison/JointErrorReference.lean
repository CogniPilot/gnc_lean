import GNC.Applications.OrbitalComparison.JointErrorData.Model
import GNC.Applications.OrbitalComparison.LieSTTData.Phase
import GNC.Applications.OrbitalComparison.VaryingRateReference

/-! Connect the all-axis candidate to the already checked reference phase.
The earlier experiment uses the identical 120-second nominal. Reuse its
cached oscillator certificate after checking equality of the actual inputs;
no integration tolerance is introduced as an error allowance. -/
namespace GNC.OrbitalComparison.JointErrorData
open ParameterPolynomial PolynomialPhaseCertificate LieSTTOutput Set Matrix

theorem reference_phase_checked :
    referenceRate=LieSTTData.Phase.harmonic1.rate ∧
    referenceCosine=LieSTTData.Phase.harmonic1.cosine ∧
    referenceSine=LieSTTData.Phase.harmonic1.sine := by
  exact ⟨rfl,rfl,rfl⟩

noncomputable section

def phase (t : ℝ) : ℝ := (3231/25000)*t+(1/200000)*t^2/2
def exactReference (t : ℝ) : Vec3 := ![Real.cos (phase t),Real.sin (phase t),0]

theorem phase_derivative (t : ℝ) :
    HasDerivAt phase (PolynomialOrder.value referenceRate t) t := by
  convert ((hasDerivAt_id t).const_mul (3231/25000:ℝ)).add
    ((((hasDerivAt_id t).pow 2).const_mul (1/200000:ℝ)).div_const 2) using 1
  norm_num [referenceRate,PolynomialOrder.value,Planning.PolynomialKernel.evaluate]
  ring

theorem phase_error {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ‖candidate LieSTTData.Phase.harmonic1 t-RotationPhaseCertificate.phase (phase t)‖≤
      (LieSTTData.Phase.harmonic1.error:ℝ)*t := by
  apply PolynomialPhaseCertificate.certifies _ LieSTTData.Phase.harmonic1_valid
    phase (by simp [phase]) _ ht
  intro s _
  exact phase_derivative s

theorem exactReference_norm (t : ℝ) : enorm (exactReference t)=1 := by
  have hs := enorm_sq (exactReference t)
  change enorm (exactReference t)^2=Real.cos (phase t)^2+Real.sin (phase t)^2+0^2 at hs
  nlinarith [Real.sin_sq_add_cos_sq (phase t),enorm_nonneg (exactReference t)]

/-- The spatial error equals the complex phase error, so there is no
sqrt(2) loss from separate cosine and sine bounds. -/
theorem reference_error (x : Fin 3 → ℝ) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    enorm (exactReference t-value3 modelInput.reference x t)≤
      (LieSTTData.Phase.harmonic1.error:ℝ)*t := by
  have he : enorm (exactReference t-value3 modelInput.reference x t)=
      ‖candidate LieSTTData.Phase.harmonic1 t-RotationPhaseCertificate.phase (phase t)‖ := by
    apply (sq_eq_sq₀ (enorm_nonneg _) (norm_nonneg _)).mp
    rw [enorm_sq,Complex.sq_norm]
    simp [exactReference,lengthSq,value3,modelInput,VaryingRatePolynomial.value_time,
      candidate,pair,RotationPhaseCertificate.phase,Complex.normSq_apply,
      ←reference_phase_checked.2.1,←reference_phase_checked.2.2]
    ring
  rw [he]
  exact phase_error ht

def planarSpin (v : Vec3) : Vec3 := ![-v 1,v 0,0]
def radialForce (t : ℝ) : ℝ := (modelInput.K:ℝ)-(PolynomialOrder.value referenceRate t)^2
def exactForce (t : ℝ) : Vec3 :=
  radialForce t • exactReference t+(1/200000:ℝ) • planarSpin (exactReference t)

theorem planarSpin_bound (v : Vec3) : enorm (planarSpin v)≤enorm v := by
  have hs := enorm_sq (planarSpin v)
  have hv := enorm_sq v
  simp [planarSpin,lengthSq] at hs hv
  change enorm (planarSpin v)^2=v 1^2+v 0^2 at hs
  nlinarith [enorm_nonneg (planarSpin v),enorm_nonneg v,sq_nonneg (v 2)]

theorem force_value (x : Fin 3 → ℝ) (t : ℝ) :
    value3 modelInput.force x t=radialForce t • value3 modelInput.reference x t+
      (1/200000:ℝ) • planarSpin (value3 modelInput.reference x t) := by
  have hv : value3 modelInput.force x t=value3 forceFormula x t := by
    ext i
    exact ParameterPolynomial.identity _ _ (force_checked i) x t
  rw [hv]
  ext i
  fin_cases i <;>
    norm_num [forceFormula,value3,value_subtract,value_add,value_multiply,value_scale,
      value_constant,VaryingRatePolynomial.value_time,radialForce,planarSpin]
  all_goals try ring
  all_goals simp [modelInput]

/-- The changing thrust inherits the same phase certificate. Both the
radial balance and tangential angular-acceleration term are included. -/
theorem force_error (x : Fin 3 → ℝ) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    enorm (exactForce t-value3 modelInput.force x t)≤
      (|radialForce t|+1/200000)*(LieSTTData.Phase.harmonic1.error:ℝ)*t := by
  rw [force_value]
  let e := exactReference t-value3 modelInput.reference x t
  have he : exactForce t-(radialForce t • value3 modelInput.reference x t+
      (1/200000:ℝ) • planarSpin (value3 modelInput.reference x t))=
      radialForce t • e+(1/200000:ℝ) • planarSpin e := by
    ext i
    fin_cases i <;> simp [exactForce,e,planarSpin,vecHead,vecTail,
      Pi.smul_apply,smul_eq_mul] <;> ring
  rw [he]
  have h := enorm_add_le (radialForce t • e) ((1/200000:ℝ) • planarSpin e)
  rw [enorm_smul,enorm_smul,abs_of_pos (by norm_num : (0:ℝ)<1/200000)] at h
  calc
    _≤|radialForce t| * enorm e+(1/200000)*enorm (planarSpin e) := h
    _≤(|radialForce t|+1/200000)*enorm e := by
      have hb := mul_le_mul_of_nonneg_left (planarSpin_bound e)
        (by norm_num : (0:ℝ)≤1/200000)
      nlinarith
    _≤(|radialForce t|+1/200000)*((LieSTTData.Phase.harmonic1.error:ℝ)*t) :=
      mul_le_mul_of_nonneg_left (reference_error x ht) (by positivity)
    _=_ := by ring

theorem exactReference_model (t : ℝ) :
    (WithLp.toLp 2 (exactReference t) : SpatialBurn.E3)=
      VaryingRateReference.position 1 (phase t) := by
  simp [VaryingRateReference.position,SpatialRotatingFrame.mix,
    SpatialBurn.pack_eq,exactReference]

theorem exactForce_model (t : ℝ) :
    (WithLp.toLp 2 (exactForce t) : SpatialBurn.E3)=
      VaryingRateReference.thrust (modelInput.K:ℝ) 1 (phase t)
        (PolynomialOrder.value referenceRate t) (1/200000) := by
  rw [VaryingRateReference.thrust,SpatialRotatingFrame.mix,SpatialBurn.pack_eq]
  ext i
  fin_cases i <;>
    simp [exactForce,radialForce,planarSpin,exactReference,vecHead,vecTail] <;> ring

def referenceVelocity (t : ℝ) : SpatialBurn.E3 :=
  VaryingRateReference.velocity 1 (phase t) (PolynomialOrder.value referenceRate t)

theorem reference_position_derivative (t : ℝ) :
    HasDerivAt (fun s => (WithLp.toLp 2 (exactReference s) : SpatialBurn.E3))
      (referenceVelocity t) t := by
  simp_rw [exactReference_model]
  exact VaryingRateReference.position_derivative 1 (phase_derivative t)

/-- The nominal is a trajectory of the complete normalized inverse-square
field with the declared time-varying force, not a fitted source curve. -/
theorem reference_velocity_derivative (t : ℝ) :
    HasDerivAt referenceVelocity
      (Gravity.field (modelInput.K:ℝ) (WithLp.toLp 2 (exactReference t) : SpatialBurn.E3)+
        WithLp.toLp 2 (exactForce t)) t := by
  rw [exactReference_model,exactForce_model]
  apply VaryingRateReference.physical_velocity_derivative (modelInput.K:ℝ) 1
    (by norm_num) (phase_derivative t)
  convert ((hasDerivAt_id t).const_mul (1/200000:ℝ)).const_add (3231/25000:ℝ) using 1
  · funext s
    norm_num [referenceRate,PolynomialOrder.value,Planning.PolynomialKernel.evaluate]
    ring
  · norm_num

end
end GNC.OrbitalComparison.JointErrorData
