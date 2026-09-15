import GNC.Applications.OrbitalComparison.PointingCapReachable
import GNC.Applications.OrbitalComparison.PointingCapData.ComponentTime12Burn1200
import GNC.Applications.OrbitalComparison.PointingCapData.SphereTime12Burn1200
import GNC.Applications.OrbitalComparison.PointingCapData.Taylor4Time12Burn1200

/-! All three main-table predictions enclose the same physical position
family. The displayed Hausdorff bounds are in millimetres. These are upper
bounds; the pointwise cubic obstruction is not a set-distance lower bound. -/
namespace GNC.OrbitalComparison.PointingCapSetBounds
open PointingCapCertificate Set
noncomputable section

def physical (t : ℝ) := PointingCapData.ComponentTime12Burn1200.data.reachablePositions t

theorem component {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    1000 * Metric.hausdorffDist (physical t)
      (PointingCapData.ComponentTime12Burn1200.data.predictedPositions t) ≤ 3.120 := by
  have h := PointingCapData.ComponentTime12Burn1200.data.position_hausdorff
    PointingCapData.ComponentTime12Burn1200.valid ht
  have hb : (PointingCapData.ComponentTime12Burn1200.data.positionError:ℝ) ≤
      ((194953/62500000:ℚ):ℝ) := by
    exact_mod_cast PointingCapData.ComponentTime12Burn1200.position_limit
  norm_num at hb
  change 1000 * Metric.hausdorffDist
    (PointingCapData.ComponentTime12Burn1200.data.reachablePositions t) _ ≤ _
  linarith

theorem sphere {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    1000 * Metric.hausdorffDist (physical t)
      (PointingCapData.SphereTime12Burn1200.data.predictedPositions t) ≤ 3.120 := by
  have h := PointingCapData.SphereTime12Burn1200.data.position_hausdorff
    PointingCapData.SphereTime12Burn1200.valid ht
  have he := Data.reachablePositions_eq
    (D₁ := PointingCapData.SphereTime12Burn1200.data)
    (D₂ := PointingCapData.ComponentTime12Burn1200.data) rfl rfl t
  rw [he] at h
  have hb : (PointingCapData.SphereTime12Burn1200.data.positionError:ℝ) ≤
      ((194953/62500000:ℚ):ℝ) := by
    exact_mod_cast PointingCapData.SphereTime12Burn1200.position_limit
  norm_num at hb
  change 1000 * Metric.hausdorffDist
    (PointingCapData.ComponentTime12Burn1200.data.reachablePositions t) _ ≤ _
  linarith

theorem quartic {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    1000 * Metric.hausdorffDist (physical t)
      (PointingCapData.Taylor4Time12Burn1200.data.predictedPositions t) ≤ 4.217 := by
  have h := PointingCapData.Taylor4Time12Burn1200.data.position_hausdorff
    PointingCapData.Taylor4Time12Burn1200.valid ht
  have he := Data.reachablePositions_eq
    (D₁ := PointingCapData.Taylor4Time12Burn1200.data)
    (D₂ := PointingCapData.ComponentTime12Burn1200.data) rfl rfl t
  rw [he] at h
  have hb : (PointingCapData.Taylor4Time12Burn1200.data.positionError:ℝ) ≤
      ((4216001/1000000000:ℚ):ℝ) := by
    exact_mod_cast PointingCapData.Taylor4Time12Burn1200.position_limit
  norm_num at hb
  change 1000 * Metric.hausdorffDist
    (PointingCapData.ComponentTime12Burn1200.data.reachablePositions t) _ ≤ _
  linarith

end
end GNC.OrbitalComparison.PointingCapSetBounds
