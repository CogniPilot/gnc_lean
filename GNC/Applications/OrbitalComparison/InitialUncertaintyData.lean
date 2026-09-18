import GNC.Applications.OrbitalComparison.InitialUncertainty
import GNC.Applications.OrbitalComparison.LieSTTData.LinearComponents
import GNC.Applications.OrbitalComparison.LieSTTData.Output

/-! Same independent 10 m and 0.01 m/s initial balls, 120 s burn, and
|theta| <= 0.35 for both predictors. All coefficients below are rational.
The velocity radius in normalized time is 120 * 0.01 = 6/5 m. -/
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace GNC.OrbitalComparison.InitialUncertaintyData
open Planning.PolynomialKernel InitialUncertainty VaryingRateCertificate Set

def initialEnvelope (κ p₀ v₀ : ℚ) : List ℚ :=
  [p₀,v₀,κ*p₀/2,κ*v₀/6,κ^2*p₀/24,κ^2*v₀/120,
    κ^3*p₀/720,κ^3*v₀/5040,κ^4*p₀/(720*(56-κ)),κ^4*v₀/(5040*(72-κ))]

def constantEnvelope (κ F : ℚ) : List ℚ :=
  [0,0,F/2,0,F*κ/24,0,F*κ^2/720,0,F*κ^3/(720*(56-κ))]

namespace RDR
abbrev data := LieSTTData.LinearComponents.record
def forcing : List ℚ := [data.defect]
def base : List ℚ := constantEnvelope data.gain data.defect
def growth : List ℚ := initialEnvelope data.gain 10 (6/5)
def envelope : List ℚ := PolynomialBounds.add base growth

theorem valid : InitialPolynomialForcing.Valid data.gain 10 (6/5) forcing envelope := by decide +kernel
theorem region : evaluate envelope 1<data.positionBound := by decide +kernel

theorem position_display : evaluate envelope 1≤(11374524/1000000:ℚ) := by decide +kernel
theorem velocity_display : evaluate (differentiate envelope) 1/120≤(12972589/1000000000:ℚ) := by decide +kernel

theorem exists_motion {θ : ℝ} (hθ : |θ|≤(data.sigma:ℝ)) (a b : SpatialBurn.E3)
    (ha : ‖a‖≤10) (hb : ‖b‖≤6/5) :
    ∃ X : Motion data θ 10 (6/5),
      X.p 0=data.position θ 0+a ∧ X.v 0=data.velocity θ 0+b ∧
      ∀ t ∈ Icc (0:ℝ) 1, (existenceFloor data 10 (6/5):ℝ)≤‖X.p t‖ := by
  apply exists_for_initial_offsets data LieSTTData.LinearComponents.valid
    (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel) hθ a b
  · simpa using ha
  · simpa using hb

theorem prediction {θ : ℝ} (hθ : |θ|≤(data.sigma:ℝ)) (X : Motion data θ 10 (6/5)) :
    ∀ t ∈ Icc (0:ℝ) 1,
      ‖X.p t-data.position θ t‖≤PolynomialOrder.value envelope t ∧
      ‖X.v t-data.velocity θ t‖≤PolynomialOrder.value (differentiate envelope) t := by
  apply InitialUncertainty.curve data LieSTTData.LinearComponents.valid forcing envelope valid region hθ X
  intro t ht
  simpa [forcing,PolynomialOrder.value,evaluate] using
    data.complete_defect_bound LieSTTData.LinearComponents.valid hθ ht
end RDR

namespace Lie3
abbrev data := LieSTTData.Lie3.record
def forcing : List ℚ := LieSTTProfile.Lie3.profile.forcing data
def base : List ℚ := LieSTTProfile.Lie3.profile.envelope
def growth : List ℚ := initialEnvelope data.gain 10 (6/5)
def envelope : List ℚ := PolynomialBounds.add base growth

theorem valid : InitialPolynomialForcing.Valid data.gain 10 (6/5) forcing envelope := by decide +kernel
theorem region : evaluate envelope 1<data.positionBound := by decide +kernel

theorem position_display : evaluate envelope 1+LieSTTData.Output.position.error data≤
    (11375191/1000000:ℚ) := by decide +kernel
theorem velocity_display :
    (evaluate (differentiate envelope) 1+LieSTTData.Output.velocity.error data)/120≤
      (12995152/1000000000:ℚ) := by decide +kernel

theorem exists_motion {θ : ℝ} (hθ : |θ|≤(data.sigma:ℝ)) (a b : SpatialBurn.E3)
    (ha : ‖a‖≤10) (hb : ‖b‖≤6/5) :
    ∃ X : Motion data θ 10 (6/5),
      X.p 0=data.position θ 0+a ∧ X.v 0=data.velocity θ 0+b ∧
      ∀ t ∈ Icc (0:ℝ) 1, (existenceFloor data 10 (6/5):ℝ)≤‖X.p t‖ := by
  apply exists_for_initial_offsets data LieSTTData.Lie3.valid
    (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel) hθ a b
  · simpa using ha
  · simpa using hb

theorem polynomial_prediction {θ : ℝ} (hθ : |θ|≤(data.sigma:ℝ)) (X : Motion data θ 10 (6/5)) :
    ∀ t ∈ Icc (0:ℝ) 1,
      ‖X.p t-data.position θ t‖≤PolynomialOrder.value envelope t ∧
      ‖X.v t-data.velocity θ t‖≤PolynomialOrder.value (differentiate envelope) t := by
  apply InitialUncertainty.curve data LieSTTData.Lie3.valid forcing envelope valid region hθ X
  exact fun t ht => LieSTTProfile.Lie3.profile.complete_defect data LieSTTData.Lie3.valid
    LieSTTProfile.Lie3.valid hθ ht

/-- The actual Lie predictor retains its exact Jacobian, with the checked
polynomial-to-exact-output transfer added to the growing tube. -/
theorem prediction {θ : ℝ} (hθ : |θ|≤(data.sigma:ℝ)) (X : Motion data θ 10 (6/5))
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ‖X.p t-LieSTTData.Output.position.physicalPosition data θ t‖≤
      PolynomialOrder.value envelope t+(LieSTTData.Output.position.error data:ℝ) ∧
    ‖X.v t-LieSTTData.Output.velocity.physicalVelocity data θ t‖≤
      PolynomialOrder.value (differentiate envelope) t+(LieSTTData.Output.velocity.error data:ℝ) := by
  have hb := polynomial_prediction hθ X t ht
  have hp := LieSTTData.Output.position.certifies data data.q LieSTTData.Lie3.valid
    LieSTTData.Output.position_valid hθ ht
  have hv := LieSTTData.Output.velocity.certifies data (LieSTTOutput.covariantVelocity data data.q)
    LieSTTData.Lie3.valid LieSTTData.Output.velocity_valid hθ ht
  have hp' : ‖data.position θ t-LieSTTData.Output.position.physicalPosition data θ t‖≤
      (LieSTTData.Output.position.error data:ℝ) := by
    simpa only [LieSTTOutput.Slot.physicalPosition,Data.position,VaryingRateFrame.position,
      VaryingRateBurn.Model.reference,Data.model,Data.displacement,
      add_sub_add_left_eq_sub,←map_sub,VaryingRateFrame.turn_norm,norm_sub_rev] using hp
  have hv' : ‖data.velocity θ t-LieSTTData.Output.velocity.physicalVelocity data θ t‖≤
      (LieSTTData.Output.velocity.error data:ℝ) := by
    rw [LieSTTOutput.covariantVelocity_value] at hv
    simpa only [LieSTTOutput.Slot.physicalVelocity,Data.velocity,VaryingRateFrame.velocity,
      VaryingRateBurn.Model.referenceVelocity,Data.model,Data.displacement,Data.rotatingVelocity,
      add_sub_add_left_eq_sub,←map_sub,VaryingRateFrame.turn_norm,norm_sub_rev] using hv
  have tri (a b c : SpatialBurn.E3) : ‖a-c‖≤‖a-b‖+‖b-c‖ := by
    simpa only [dist_eq_norm] using dist_triangle a b c
  exact ⟨(tri _ _ _).trans (add_le_add hb.1 hp'),(tri _ _ _).trans (add_le_add hb.2 hv')⟩
end Lie3
end GNC.OrbitalComparison.InitialUncertaintyData
