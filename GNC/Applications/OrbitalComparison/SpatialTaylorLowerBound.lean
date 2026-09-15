import GNC.Analysis.CircleEvaluation
import GNC.Applications.OrbitalComparison.SpatialTerminalCertificate
import GNC.Applications.OrbitalComparison.SpatialData.RTNFrameCircleTime14
import GNC.Applications.OrbitalComparison.SpatialData.RTNFrameSTT7Time14

/-! A physical lower bound for the stored seventh-order RTN predictor.
The rational point witness uses the same coefficients as the full-domain
certificates. It includes trigonometric evaluation error and both physical
trajectory errors. It is not a lower bound for every degree-seven fitting
scheme, nor for higher-order or rotation-preserving Cartesian methods. -/
namespace GNC.OrbitalComparison.SpatialTaylorLowerBound
open SpatialBurn SpatialFieldCertificate SpatialData CircleEvaluation Set

def pointDifference : PolynomialODE.Expr 2 := difference
  (RTNFrameCircleTime14.data.q 0) (RTNFrameSTT7Time14.data.q 0) 1 (7/20) 7000000

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem point_certificate :
    pointDifference.differenceMajorant (fun _ => 1) (fun _ => radius (7/20))+
      |pointDifference.ratValue (center (7/20))-3881/250000000| ≤ 1/1000000000 := by
  decide +kernel

noncomputable section

def structured (θ t : ℝ) : E3 :=
  position SpatialSources.circle RTNFrameCircleTime14.data.q θ t-
    position SpatialSources.circle RTNFrameCircleTime14.data.q 0 t

def ordinary (θ t : ℝ) : E3 :=
  position SpatialSources.ordinary RTNFrameSTT7Time14.data.q θ t-
    position SpatialSources.ordinary RTNFrameSTT7Time14.data.q 0 t

theorem ordinary_component (q : Fin 3 → BivariatePolynomial.Coefficients)
    (θ t : ℝ) (i : Fin 3) :
    (position SpatialSources.ordinary q θ t) i =
      7000000*BivariatePolynomial.value (q i) t θ := by
  change ((7000000:ℝ) • pack (BivariatePolynomial.value (q 0) t θ)
    (BivariatePolynomial.value (q 1) t θ) (BivariatePolynomial.value (q 2) t θ)) i = _
  fin_cases i <;> simp [pack_eq]

theorem point_difference :
    |(structured (7/20) 1-ordinary (7/20) 1) 0-3881/250000000| ≤ 1/1000000000 := by
  have h := difference_error (RTNFrameCircleTime14.data.q 0)
    (RTNFrameSTT7Time14.data.q 0) 1 (7/20) 7000000 (3881/250000000)
    (1/1000000000) (fun _ => 1) (fun _ => by norm_num)
    (by intro i; fin_cases i <;> decide +kernel) point_certificate
  norm_num only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_one] at h
  change |((position SpatialSources.circle RTNFrameCircleTime14.data.q (7/20) 1) 0-
    (position SpatialSources.circle RTNFrameCircleTime14.data.q 0 1) 0)-
    ((position SpatialSources.ordinary RTNFrameSTT7Time14.data.q (7/20) 1) 0-
    (position SpatialSources.ordinary RTNFrameSTT7Time14.data.q 0 1) 0)-3881/250000000| ≤ _
  rw [SpatialTerminalCertificate.position_component,SpatialTerminalCertificate.position_component,
    ordinary_component,ordinary_component]
  convert h using 1 <;> ring

/-- At the 600-second, +0.35-radian endpoint, this stored STT7 predictor
has actual relative-position error greater than 15 micrometres. -/
theorem seventh_order_error_gt
    (X : PhysicalOrbit .rtnReferenceOffset (7/20))
    (X₀ : PhysicalOrbit .rtnReferenceOffset 0) :
    (15/1000000:ℝ) < ‖(X.p 1-X₀.p 1)-ordinary (7/20) 1‖ := by
  have hc := RTNFrameCircleTime14.relative_prediction X X₀ (by norm_num) 1 (by norm_num)
  have hcomponent := (PiLp.norm_apply_le ((X.p 1-X₀.p 1)-structured (7/20) 1) 0).trans hc.1
  change |(X.p 1-X₀.p 1) 0-structured (7/20) 1 0| ≤ _ at hcomponent
  have hp := abs_le.mp point_difference
  have hn := PiLp.norm_apply_le ((X.p 1-X₀.p 1)-ordinary (7/20) 1) 0
  change |(X.p 1-X₀.p 1) 0-ordinary (7/20) 1 0| ≤ _ at hn
  have hlow := (abs_le.mp hcomponent).1
  have hdiff : -(1/1000000000:ℝ) ≤
      structured (7/20) 1 0-ordinary (7/20) 1 0-3881/250000000 := hp.1
  have habs := le_abs_self ((X.p 1-X₀.p 1) 0-ordinary (7/20) 1 0)
  linarith

theorem structured_error_lt
    {θ : ℝ} (X : PhysicalOrbit .rtnReferenceOffset θ)
    (X₀ : PhysicalOrbit .rtnReferenceOffset 0) (hθ : |θ| ≤ 7/20) :
    ∀ t ∈ Icc (0:ℝ) 1,
      ‖(X.p t-X₀.p t)-structured θ t‖ < (1/2000000:ℝ) := by
  intro t ht
  exact (RTNFrameCircleTime14.relative_prediction X X₀ hθ t ht).1.trans_lt (by norm_num)

end
end GNC.OrbitalComparison.SpatialTaylorLowerBound
