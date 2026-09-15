import GNC.Applications.OrbitalComparison.VaryingRateCertificate
import GNC.Analysis.DiskTimePolynomial
import GNC.Dynamics.PolynomialForcingCertificate

/-! One time-profile checker for every varying-rate predictor. The residual
profile may retain growth in time; physical gravity, existence and first-exit
closure are identical for Lie-generated and Cartesian-generated candidates. -/
namespace GNC.OrbitalComparison.VaryingRateTimeCertificate
open VaryingRateCertificate PointingCapPolynomial VaryingRateBurn SpatialBurn Set
open Planning.PolynomialKernel

structure Profile where
  residual : DiskTimePolynomial.Certificate 3
  envelope : List ℚ

def Profile.forcing (M : Profile) (D : Data) : List ℚ :=
  PolynomialBounds.add (M.residual.bound (D.sigma^2/2))
    [D.phaseBudget+D.pointingBudget+D.gravityBudget]
def Profile.positionError (M : Profile) : ℚ := evaluate M.envelope 1
def Profile.velocityError (M : Profile) (D : Data) : ℚ :=
  evaluate (differentiate M.envelope) 1/D.duration
structure Profile.Valid (M : Profile) (D : Data) : Prop where
  residual : M.residual.Valid D.remainder D.sigma
  envelope : PolynomialForcing.Valid D.gain (M.forcing D) M.envelope
  region : evaluate (M.forcing D) 1*HarmonicCertificate.positionGain D.gain<D.positionBound

noncomputable section
theorem Profile.residual_bound (M : Profile) (D : Data) (hM : M.Valid D)
    {θ t : ℝ} (hθ : |θ|≤(D.sigma:ℝ)) (ht : t ∈ Icc (0:ℝ) 1) :
    ‖vectorValue D.remainder (VaryingRatePolynomial.parameter D.kind θ) t‖≤
      PolynomialOrder.value (M.residual.bound (D.sigma^2/2)) t := by
  have hb := VaryingRatePolynomial.parameter_bound D.kind hθ
  have h0 := hb 0
  have hz : VaryingRatePolynomial.parameter D.kind θ 1=0 := by cases D.kind <;> rfl
  have hr : VaryingRatePolynomial.parameter D.kind θ 0^2+
      VaryingRatePolynomial.parameter D.kind θ 1^2≤(D.sigma:ℝ)^2 := by
    rw [hz]
    simpa [VaryingRatePolynomial.radius,sq_abs] using
      pow_le_pow_left₀ (abs_nonneg _) h0 2
  have hc : |VaryingRatePolynomial.parameter D.kind θ 2|≤((D.sigma^2/2:ℚ):ℝ) := by
    simpa [VaryingRatePolynomial.radius] using hb 2
  have he : DiskPolynomial.vectorValue D.remainder (VaryingRatePolynomial.parameter D.kind θ) t=
      vectorValue D.remainder (VaryingRatePolynomial.parameter D.kind θ) t := by
    ext i
    fin_cases i <;> simp [DiskPolynomial.vectorValue,vectorValue,pack_eq]
  simpa only [he] using M.residual.certifies D.remainder hM.residual hr hc ht

theorem Profile.complete_defect (M : Profile) (D : Data) (hD : D.Valid) (hM : M.Valid D)
    {θ t : ℝ} (hθ : |θ|≤(D.sigma:ℝ)) (ht : t ∈ Icc (0:ℝ) 1) :
    ‖D.model.acceleration θ t (D.position θ t)-D.acceleration θ t‖≤
      PolynomialOrder.value (M.forcing D) t := by
  have hb := D.complete_defect_of_residual hD hθ ht (M.residual_bound D hM hθ ht)
  convert hb using 1
  rw [Profile.forcing,PolynomialOrder.value_add]
  simp [PolynomialOrder.value,evaluate]
  ring

theorem Profile.certifies (M : Profile) (D : Data) (hD : D.Valid) (hM : M.Valid D)
    {θ : ℝ} (hθ : |θ|≤(D.sigma:ℝ)) (X : Motion D.model θ) :
    ∀ t ∈ Icc (0:ℝ) 1, ‖X.p t-D.position θ t‖≤(M.positionError:ℝ) ∧
      ‖X.v t-D.velocity θ t‖/(D.duration:ℝ)≤(M.velocityError D:ℝ) := by
  have hr : (0:ℝ)<D.r := by exact_mod_cast hD.radius_pos
  have hmax : 2*(D.positionBound:ℝ)<(D.r:ℝ) := by exact_mod_cast hD.position_max
  have hT : (0:ℝ)<D.duration := by exact_mod_cast hD.duration_pos
  have hclose : PolynomialOrder.value (M.forcing D) 1*
      PolynomialSupersolution.value (D.gain:ℝ) 1<(D.positionBound:ℝ) := by
    have hh : ((evaluate (M.forcing D) 1:ℚ):ℝ)*
        (HarmonicCertificate.positionGain D.gain:ℝ)<(D.positionBound:ℝ) := by exact_mod_cast hM.region
    have hv := PolynomialOrder.value_at_rational (M.forcing D) 1
    simp only [Rat.cast_one] at hv
    simpa only [hv,HarmonicCertificate.positionGain_cast] using hh
  have hq (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      (D.r:ℝ)-2*(D.positionBound:ℝ)+(D.positionBound:ℝ)≤‖D.position θ t‖ := by
    have hd := VaryingRatePolynomial.vector_bound D.q hD.position D.kind hθ ht
    have hn := norm_sub_le (D.position θ t) (VaryingRateFrame.turn (D.model.phase t) (D.displacement θ t))
    have he : D.position θ t-VaryingRateFrame.turn (D.model.phase t) (D.displacement θ t)=
        D.model.reference t := by simp [Data.position,VaryingRateFrame.position,Model.reference,Data.model]
    rw [he,D.model.reference_norm hr.le,VaryingRateFrame.turn_norm] at hn
    change ‖D.displacement θ t‖≤(D.positionBound:ℝ) at hd
    change (D.r:ℝ)≤_ at hn
    linarith
  have hi := D.initial hD θ
  have hb := Gravity.polynomial_prediction (D.μ:ℝ) 1
    (by exact_mod_cast hD.mu_nonnegative) (by norm_num)
    X.p X.v (D.position θ) (D.velocity θ) (D.acceleration θ) (D.model.thrust θ)
    (M.forcing D) M.envelope hM.envelope hD.gain_nonnegative hD.gain_max
    (r := (D.r:ℝ)-2*(D.positionBound:ℝ)) (by linarith) hclose
    (by simp [Data.gain]) hq X.continuous_p X.continuous_v
    (continuous_iff_continuousAt.mpr fun t => (D.position_derivative θ t).continuousAt)
    (continuous_iff_continuousAt.mpr fun t => (D.velocity_derivative θ t).continuousAt)
    X.derivative_p
    (fun t ht => by simpa [Model.acceleration,Data.model] using X.derivative_v t ht)
    (fun t _ => D.position_derivative θ t) (fun t _ => D.velocity_derivative θ t)
    (by simpa [Data.position,VaryingRateFrame.position,Model.reference,Data.model,hi.1] using X.initial_p)
    (by simpa [Data.velocity,VaryingRateFrame.velocity,Model.referenceVelocity,Data.model,hi.1,hi.2] using X.initial_v)
    (fun t ht => by simpa [Model.acceleration,Data.model] using M.complete_defect D hD hM hθ ht)
  intro t ht
  constructor
  · exact (hb t ht).1
  · have hv := div_le_div_of_nonneg_right (hb t ht).2 hT.le
    simpa only [Profile.velocityError,Rat.cast_div] using hv

theorem Profile.physical_prediction (M : Profile) (D : Data) (hD : D.Valid) (hM : M.Valid D)
    {θ : ℝ} (hθ : |θ|≤(D.sigma:ℝ)) :
    (∃ X : Motion D.model θ, ∀ t ∈ Icc (0:ℝ) 1, (D.existenceFloor:ℝ)≤‖X.p t‖) ∧
    (∀ X : Motion D.model θ, ∀ t ∈ Icc (0:ℝ) 1,
      ‖X.p t-D.position θ t‖≤(M.positionError:ℝ) ∧
      ‖X.v t-D.velocity θ t‖/(D.duration:ℝ)≤(M.velocityError D:ℝ)) :=
  ⟨D.exists_motion hD hθ,fun X => M.certifies D hD hM hθ X⟩

end
end GNC.OrbitalComparison.VaryingRateTimeCertificate
