import GNC.Analysis.PolynomialLieConvergence
import GNC.Applications.ApproachGate.Invariant

/-! Convergence of the explicit nonlinear Lie series for the spatial orbital
model already connected to physical inverse-square motion. Its exact phase
states retain time-varying inertial/RTN transformations. No constant-gradient
replacement is made. This theorem inherits explicit smoothness and region
conditions; it is not an unconditional long-horizon convergence claim.
-/
noncomputable section
namespace GNC.OrbitalComparison.ExactLieSeries
open PolynomialODE PolynomialODE.Expr Set Filter
open scoped Topology ContDiff

theorem physical_lift_series (mode : ApproachGate.Law) (u : Fin 2 → ℚ)
    {w : ℝ → Fin 6 → ℝ} {S : Set ℝ} {θ start T : ℝ}
    (hS : IsOpen S)
    (hw : ∀ t ∈ S, HasDerivAt w (CircularRendezvous3D.physicalRate
      (ApproachGate.source mode θ (start+t) (fun j => (u j:ℝ))) (w t)) t)
    (hr : ∀ t ∈ S, 0 < CircularRendezvous3D.radius (w t))
    (hsmooth : ContDiffOn ℝ ∞ (fun t => ApproachGate.lift θ (start+t) (w t)) S)
    (hT : 0 < T) (hstep : Icc 0 T ⊆ S)
    (hregion : ∀ t ∈ Icc 0 T, ∀ i, |ApproachGate.lift θ (start+t) (w t) i| ≤ 1)
    (hradius : (fieldMajorant (ApproachGate.field mode u):ℝ)*
      fieldDegree (ApproachGate.field mode u)*T < 1) (i : Fin 11) :
    Tendsto (fun N => partialFlow (ApproachGate.field mode u)
      (ApproachGate.lift θ start (w 0)) N T i) atTop
      (𝓝 (ApproachGate.lift θ (start+T) (w T) i)) := by
  let f := ApproachGate.field mode u
  let z := fun t => ApproachGate.lift θ (start+t) (w t)
  have hz : ∀ t ∈ S, HasDerivAt z (fun i => (f i).value (z t)) t := by
    intro t ht
    simpa only [f, ApproachGate.field_value] using
      ApproachGate.lift_derivative (θ := θ) (start := start) (hw t ht) (hr t ht)
  simpa only [z, add_zero] using partialFlow_tendsto f (fieldMajorant_nonneg f)
    (fieldDegree_pos f) (le_fieldMajorant f) (le_fieldDegree f)
    hS hz hsmooth hT hstep hregion hradius i

end GNC.OrbitalComparison.ExactLieSeries
