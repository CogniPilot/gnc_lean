import GNC.Applications.OrbitalComparison.PlanarResponseApproximation
import GNC.Applications.OrbitalComparison.TangentialSharedComparison
import GNC.Applications.OrbitalComparison.SharedResponseData.Input

/-! Transfer of reference and sparse response errors to physical predictions.
The response-identification and coefficient-error hypotheses are explicit:
checking the polynomial data alone does not discharge them. Evaluation of
the output and rotation map is over the reals, not IEEE arithmetic.
-/
noncomputable section
namespace GNC.OrbitalComparison.SharedResponseTransfer
open Set Matrix TangentialReferenceMotion TangentialSharedInput
open TangentialMountingMotion (angleRadius)
open PlanarResponseReduction
open LieRadiusFrame (left)

theorem geometric_prediction (r : Reference) (φ : Vec3) (hφ : enorm φ≤angleRadius)
    (X : Motion r φ) (S : Response r φ) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1)
    (qhat : E) (x xhat : Fin 4 → ℝ) {ε δ : ℝ} (hδ : 0≤δ)
    (hq : ‖r.q t-qhat‖≤ε) (hx : S.p t=WithLp.toLp 2 (geometric x *ᵥ φ))
    (herror : ∀ i, |x i-xhat i|≤δ) :
    ‖X.p t-(qhat+left φ (WithLp.toLp 2 (geometric xhat *ᵥ φ)))‖≤
      positionError t+ε+4*δ*angleRadius := by
  have hp := (TangentialSharedInput.prediction r φ hφ X S t ht).1
  have hr := geometric_reconstruction_error x xhat φ hδ (by norm_num [angleRadius])
    (by norm_num [angleRadius]; linarith [Real.pi_gt_three]) herror hφ
  rw [←hx] at hr
  have he : X.p t-(qhat+left φ (WithLp.toLp 2 (geometric xhat *ᵥ φ)))=
      (X.p t-(r.q t+left φ (S.p t)))+(r.q t-qhat)+
      (left φ (S.p t)-left φ (WithLp.toLp 2 (geometric xhat *ᵥ φ))) := by abel
  rw [he]
  exact (norm_add_le _ _).trans
    (add_le_add ((norm_add_le _ _).trans (add_le_add hp hq)) hr)

theorem cartesian_prediction (r : Reference) (φ : Vec3) (hφ : enorm φ≤angleRadius)
    (X : Motion r φ) (S : TangentialSharedComparison.ComponentResponse r φ)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1)
    (qhat : E) (x xhat : Fin 10 → ℝ) {ε δ : ℝ} (hδ : 0≤δ)
    (hq : ‖r.q t-qhat‖≤ε)
    (hx : S.p t=WithLp.toLp 2 (cartesian x *ᵥ componentWeights (rotationExp φ)))
    (herror : ∀ i, |x i-xhat i|≤δ) :
    ‖X.p t-(qhat+WithLp.toLp 2 (cartesian xhat *ᵥ componentWeights (rotationExp φ)))‖≤
      TangentialResponseCertificate.positionError t+ε+8*δ*angleRadius := by
  have hp := (TangentialSharedComparison.prediction r φ hφ X S t ht).1
  have hr := cartesian_reconstruction_error x xhat φ hδ (by norm_num [angleRadius])
    (by norm_num [angleRadius]; linarith [Real.pi_gt_three]) herror hφ
  change ‖WithLp.toLp 2 (cartesian x *ᵥ componentWeights (rotationExp φ))-
    WithLp.toLp 2 (cartesian xhat *ᵥ componentWeights (rotationExp φ))‖≤_ at hr
  rw [←hx] at hr
  have he : X.p t-(qhat+WithLp.toLp 2 (cartesian xhat *ᵥ componentWeights (rotationExp φ)))=
      (X.p t-(r.q t+S.p t))+(r.q t-qhat)+
      (S.p t-WithLp.toLp 2 (cartesian xhat *ᵥ componentWeights (rotationExp φ))) := by abel
  rw [he]
  exact (norm_add_le _ _).trans
    (add_le_add ((norm_add_le _ _).trans (add_le_add hp hq)) hr)

def geometricBudget (t : ℝ) : ℝ := positionError t+
  2*(TangentialReferenceData.errorBound:ℝ)+4*(SharedResponseData.geometricError:ℝ)*angleRadius
def cartesianBudget (t : ℝ) : ℝ := TangentialResponseCertificate.positionError t+
  2*(TangentialReferenceData.errorBound:ℝ)+8*(SharedResponseData.cartesianError:ℝ)*angleRadius

/-- Outward rounding of the computed budget, not an extra allowance.
The transfer hypotheses must still be supplied for a particular predictor. -/
theorem reported_budgets : (7000000:ℝ)*geometricBudget 1<686/1000000 ∧
    (7000000:ℝ)*cartesianBudget 1<323/1000000 := by
  norm_num [geometricBudget,cartesianBudget,positionError,gradientBudget,curvatureBudget,
    TangentialResponseCertificate.positionError,TangentialResponseCertificate.gravityBudget,
    TangentialResponseCertificate.responseRadius,TangentialReferenceMotion.mu,horizon,
    TangentialReferenceMotion.lowerRadius,TangentialReferenceData.inverseBound,angleRadius,acceleration,
    TangentialReferenceData.alpha,PolynomialSupersolution.value,PolynomialSupersolution.polynomial,
    MonomialSupersolution.value,MonomialSupersolution.polynomial,MonomialSupersolution.pair,
    MonomialSupersolution.four,MonomialSupersolution.six,TangentialReferenceData.errorBound,
    SharedResponseData.geometricError,SharedResponseData.cartesianError]

end GNC.OrbitalComparison.SharedResponseTransfer
