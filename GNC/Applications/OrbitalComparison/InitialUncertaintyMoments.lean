import GNC.Applications.OrbitalComparison.InitialUncertaintyData
import GNC.Estimation.PredictionMoments

/-! Physical prediction and full covariance-error certificates for both
orbital methods. Covariance bounds retain explicit predictor-moment and
square-integrability hypotheses; floating quadrature is not substituted
for them. State coordinates are inertial position and physical velocity.
Any supported initial/pointing law is allowed, including correlations. -/
noncomputable section
namespace GNC.OrbitalComparison.InitialUncertaintyMoments
open SpatialBurn InitialUncertainty InitialUncertaintyData
open MeasureTheory ProbabilityTheory Set Planning.PolynomialKernel
open GNC.Estimation GNC.Estimation.CovariancePropagation

abbrev Index := Bool × Fin 3

def state (T : ℝ) (p v : E3) (i : Index) : ℝ :=
  if i.1 then v i.2/T else p i.2

def radii (T P V : ℝ) (i : Index) : ℝ := if i.1 then V/T else P

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- Converts all-time physical norm certificates to statistical bounds on
all six components and all 36 covariance entries at an arbitrary time. -/
theorem of_tube (T P V : ℝ) (hT : 0<T) (hP : 0≤P) (hV : 0≤V)
    (p v q qv : Ω → E3) (σ : Index → ℝ)
    (htube : ∀ᵐ ω ∂μ, ‖p ω-q ω‖≤P ∧ ‖v ω-qv ω‖≤V)
    (hX : ∀ i, MemLp (fun ω => state T (p ω) (v ω) i) 2 μ)
    (hY : ∀ i, MemLp (fun ω => state T (q ω) (qv ω) i) 2 μ)
    (hσ : ∀ i, 0≤σ i)
    (hv : ∀ i, variance (fun ω => state T (q ω) (qv ω) i) μ≤σ i^2) :
    (∀ i, |(∫ ω, state T (p ω) (v ω) i ∂μ)-
      (∫ ω, state T (q ω) (qv ω) i ∂μ)|≤radii T P V i) ∧
    (∀ i j, |covarianceMatrix μ (fun ω => state T (p ω) (v ω)) i j-
      covarianceMatrix μ (fun ω => state T (q ω) (qv ω)) i j|≤
      σ i*radii T P V j+σ j*radii T P V i+radii T P V i*radii T P V j) := by
  apply PredictionMoments.prediction_and_moments μ _ _ _ σ hX hY
  · intro i
    cases h : i.1 <;> simp only [radii,h,Bool.false_eq_true,↓reduceIte]
    · exact hP
    · exact div_nonneg hV hT.le
  · exact hσ
  · intro i
    filter_upwards [htube] with ω hω
    have hp : |p ω i.2-q ω i.2|≤P := by
      simpa only [PiLp.sub_apply,Real.norm_eq_abs] using
        (PiLp.norm_apply_le (p ω-q ω) i.2).trans hω.1
    have hv : |v ω i.2-qv ω i.2|≤V := by
      simpa only [PiLp.sub_apply,Real.norm_eq_abs] using
        (PiLp.norm_apply_le (v ω-qv ω) i.2).trans hω.2
    cases h : i.1 <;> simp only [state,radii,h,Bool.false_eq_true,↓reduceIte]
    · exact hp
    · rw [← sub_div,abs_div,abs_of_pos hT]
      exact div_le_div_of_nonneg_right hv hT.le
  · exact hv

/-- A direct composition of the checked physical RDR orbit theorem with
the moment theorem. Initial position/velocity support is in `Motion`;
pointing support is almost sure. No independent-residual assumption. -/
theorem rdr_prediction_and_covariance (θ : Ω → ℝ)
    (X : ∀ ω, Motion RDR.data (θ ω) 10 (6/5))
    (hθ : ∀ᵐ ω ∂μ, |θ ω|≤(RDR.data.sigma:ℝ))
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) (σ : Index → ℝ)
    (hX : ∀ i, MemLp (fun ω => state 120 ((X ω).p t) ((X ω).v t) i) 2 μ)
    (hY : ∀ i, MemLp (fun ω => state 120 (RDR.data.position (θ ω) t)
      (RDR.data.velocity (θ ω) t) i) 2 μ)
    (hσ : ∀ i, 0≤σ i)
    (hv : ∀ i, variance (fun ω => state 120 (RDR.data.position (θ ω) t)
      (RDR.data.velocity (θ ω) t) i) μ≤σ i^2) :
    let P := PolynomialOrder.value RDR.envelope t
    let V := PolynomialOrder.value (differentiate RDR.envelope) t
    (∀ i, |(∫ ω, state 120 ((X ω).p t) ((X ω).v t) i ∂μ)-
      (∫ ω, state 120 (RDR.data.position (θ ω) t) (RDR.data.velocity (θ ω) t) i ∂μ)|≤
      radii 120 P V i) ∧
    (∀ i j, |covarianceMatrix μ (fun ω => state 120 ((X ω).p t) ((X ω).v t)) i j-
      covarianceMatrix μ (fun ω => state 120 (RDR.data.position (θ ω) t)
        (RDR.data.velocity (θ ω) t)) i j|≤
      σ i*radii 120 P V j+σ j*radii 120 P V i+radii 120 P V i*radii 120 P V j) := by
  apply of_tube μ 120 _ _ (by norm_num)
    (PolynomialOrder.value_nonnegative _ RDR.valid.position_nonnegative ht.1)
    (PolynomialOrder.value_nonnegative _ RDR.valid.velocity_nonnegative ht.1)
    _ _ _ _ σ _ hX hY hσ hv
  filter_upwards [hθ] with ω hω
  exact RDR.prediction hω (X ω) t ht

/-- The Lie-STT certificate uses its exact reconstructed output and
explicitly adds the polynomial-to-output transfer in both radii. -/
theorem lie_prediction_and_covariance (θ : Ω → ℝ)
    (X : ∀ ω, Motion Lie3.data (θ ω) 10 (6/5))
    (hθ : ∀ᵐ ω ∂μ, |θ ω|≤(Lie3.data.sigma:ℝ))
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) (σ : Index → ℝ)
    (hX : ∀ i, MemLp (fun ω => state 120 ((X ω).p t) ((X ω).v t) i) 2 μ)
    (hY : ∀ i, MemLp (fun ω => state 120
      (LieSTTData.Output.position.physicalPosition Lie3.data (θ ω) t)
      (LieSTTData.Output.velocity.physicalVelocity Lie3.data (θ ω) t) i) 2 μ)
    (hσ : ∀ i, 0≤σ i)
    (hv : ∀ i, variance (fun ω => state 120
      (LieSTTData.Output.position.physicalPosition Lie3.data (θ ω) t)
      (LieSTTData.Output.velocity.physicalVelocity Lie3.data (θ ω) t) i) μ≤σ i^2) :
    let P := PolynomialOrder.value Lie3.envelope t+(LieSTTData.Output.position.error Lie3.data:ℝ)
    let V := PolynomialOrder.value (differentiate Lie3.envelope) t+
      (LieSTTData.Output.velocity.error Lie3.data:ℝ)
    let Y := fun ω => state 120
      (LieSTTData.Output.position.physicalPosition Lie3.data (θ ω) t)
      (LieSTTData.Output.velocity.physicalVelocity Lie3.data (θ ω) t)
    (∀ i, |(∫ ω, state 120 ((X ω).p t) ((X ω).v t) i ∂μ)-
      (∫ ω, Y ω i ∂μ)|≤radii 120 P V i) ∧
    (∀ i j, |covarianceMatrix μ (fun ω => state 120 ((X ω).p t) ((X ω).v t)) i j-
      covarianceMatrix μ Y i j|≤
      σ i*radii 120 P V j+σ j*radii 120 P V i+radii 120 P V i*radii 120 P V j) := by
  have hpe : (0:ℝ)≤(LieSTTData.Output.position.error Lie3.data:ℝ) := by
    exact_mod_cast (show (0:ℚ)≤LieSTTData.Output.position.error Lie3.data by decide +kernel)
  have hve : (0:ℝ)≤(LieSTTData.Output.velocity.error Lie3.data:ℝ) := by
    exact_mod_cast (show (0:ℚ)≤LieSTTData.Output.velocity.error Lie3.data by decide +kernel)
  apply of_tube μ 120 _ _ (by norm_num)
    (add_nonneg (PolynomialOrder.value_nonnegative _ Lie3.valid.position_nonnegative ht.1) hpe)
    (add_nonneg (PolynomialOrder.value_nonnegative _ Lie3.valid.velocity_nonnegative ht.1) hve)
    _ _ _ _ σ _ hX hY hσ hv
  filter_upwards [hθ] with ω hω
  exact Lie3.prediction hω (X ω) ht

end GNC.OrbitalComparison.InitialUncertaintyMoments
