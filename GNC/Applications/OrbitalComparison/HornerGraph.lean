import GNC.Analysis.ParameterPolynomialDegree
import GNC.Applications.OrbitalComparison.PointingCapSetBounds
import GNC.Applications.OrbitalComparison.PointingCapData.HornerTime12Burn1200
import GNC.Applications.OrbitalComparison.PointingCapData.HornerTaylor4Time12Burn1200

/-! The new optimized records retain their stated approximation classes.
Their imported physical certificates check the changed binary64 proposals.
This module does not verify the external graph optimizer or its FLOP count. -/
namespace GNC.OrbitalComparison.HornerGraph
open ParameterPolynomial
set_option maxHeartbeats 0

theorem geometric_coefficients : ∀ j,
    ∀ a ∈ PointingCapData.HornerTime12Burn1200.data.q j, a.u+a.v+a.c≤2 := by
  decide +kernel

theorem quartic_coefficients : ∀ j,
    ∀ a ∈ PointingCapData.HornerTaylor4Time12Burn1200.data.q j, a.c=0 ∧ a.u+a.v≤4 := by
  decide +kernel

theorem quartic_degree (t : ℝ) (j : Fin 3) :
    (transversePolynomial (PointingCapData.HornerTaylor4Time12Burn1200.data.q j) t).totalDegree≤4 :=
  transversePolynomial_degree _ _ _ (fun a ha => (quartic_coefficients j a ha).2)

theorem quartic_value (x : Fin 3 → ℝ) (t : ℝ) (j : Fin 3) :
    MvPolynomial.eval ![x 0,x 1]
      (transversePolynomial (PointingCapData.HornerTaylor4Time12Burn1200.data.q j) t)=
        value (PointingCapData.HornerTaylor4Time12Burn1200.data.q j) x t :=
  transversePolynomial_value _ _ _ (fun a ha => (quartic_coefficients j a ha).1)

theorem geometric_hausdorff {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    1000 * Metric.hausdorffDist (PointingCapSetBounds.physical t)
      (PointingCapData.HornerTime12Burn1200.data.predictedPositions t) ≤ 3.120 := by
  have h := PointingCapData.HornerTime12Burn1200.data.position_hausdorff
    PointingCapData.HornerTime12Burn1200.valid ht
  have he := PointingCapCertificate.Data.reachablePositions_eq
    (D₁ := PointingCapData.HornerTime12Burn1200.data)
    (D₂ := PointingCapData.ComponentTime12Burn1200.data) rfl rfl t
  rw [he] at h
  have hb : (PointingCapData.HornerTime12Burn1200.data.positionError:ℝ) ≤
      ((194953/62500000:ℚ):ℝ) := by
    exact_mod_cast PointingCapData.HornerTime12Burn1200.position_limit
  norm_num at hb
  change 1000 * Metric.hausdorffDist
    (PointingCapData.ComponentTime12Burn1200.data.reachablePositions t) _ ≤ _
  linarith

theorem quartic_hausdorff {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    1000 * Metric.hausdorffDist (PointingCapSetBounds.physical t)
      (PointingCapData.HornerTaylor4Time12Burn1200.data.predictedPositions t) ≤ 4.217 := by
  have h := PointingCapData.HornerTaylor4Time12Burn1200.data.position_hausdorff
    PointingCapData.HornerTaylor4Time12Burn1200.valid ht
  have he := PointingCapCertificate.Data.reachablePositions_eq
    (D₁ := PointingCapData.HornerTaylor4Time12Burn1200.data)
    (D₂ := PointingCapData.ComponentTime12Burn1200.data) rfl rfl t
  rw [he] at h
  have hb : (PointingCapData.HornerTaylor4Time12Burn1200.data.positionError:ℝ) ≤
      ((4216001/1000000000:ℚ):ℝ) := by
    exact_mod_cast PointingCapData.HornerTaylor4Time12Burn1200.position_limit
  norm_num at hb
  change 1000 * Metric.hausdorffDist
    (PointingCapData.ComponentTime12Burn1200.data.reachablePositions t) _ ≤ _
  linarith

end GNC.OrbitalComparison.HornerGraph
