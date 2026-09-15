import GNC.Applications.OrbitalComparison.PointingCapPolytopeData.SweepHornerTime12Burn1200
import GNC.Applications.OrbitalComparison.PointingCapPolytopeData.SweepHornerTaylor4Time12Burn1200
import GNC.Analysis.RadialQuartic

/-! Both 54-direction constructions certify the same physical reachable
family. Matching normals and interval widths are checked, so a difference
in parameterization cannot change the task being compared. -/
namespace GNC.OrbitalComparison.PointingCapPolytopeComparison
open PointingCapPolytope PointingCapCertificate Set

abbrev geometricQueries := PointingCapPolytopeData.SweepHornerTime12Burn1200.queries
abbrev quarticQueries := PointingCapPolytopeData.SweepHornerTaylor4Time12Burn1200.queries
abbrev geometricData := PointingCapData.HornerTime12Burn1200.data
abbrev quarticData := PointingCapData.HornerTaylor4Time12Burn1200.data

theorem same_normals (i : Fin 54) : (geometricQueries i).normal=(quarticQueries i).normal := by
  fin_cases i <;> decide +kernel

theorem requested_widths (i : Fin 54) :
    (geometricQueries i).upper-(geometricQueries i).lower≤1/100 ∧
    (quarticQueries i).upper-(quarticQueries i).lower≤1/100 :=
  ⟨PointingCapPolytopeData.SweepHornerTime12Burn1200.interval_widths i,
    PointingCapPolytopeData.SweepHornerTaylor4Time12Burn1200.interval_widths i⟩

noncomputable section

theorem common_support_intervals (i : Fin 54) :
    (((geometricQueries i).lower:ℝ)≤support geometricData (geometricQueries i).normal ∧
      support geometricData (geometricQueries i).normal≤((geometricQueries i).upper:ℝ)) ∧
    (((quarticQueries i).lower:ℝ)≤support geometricData (geometricQueries i).normal ∧
      support geometricData (geometricQueries i).normal≤((quarticQueries i).upper:ℝ)) := by
  have h := PointingCapPolytopeData.SweepHornerTaylor4Time12Burn1200.support_intervals i
  rw [support_eq (D₁ := quarticData) (D₂ := geometricData) rfl rfl,←same_normals i] at h
  exact ⟨PointingCapPolytopeData.SweepHornerTime12Burn1200.support_intervals i,h⟩

theorem common_physical_enclosure :
    geometricData.reachablePositions 1 ⊆ polytope geometricQueries ∩ polytope quarticQueries := by
  intro z hz
  have hs : geometricData.reachablePositions 1=quarticData.reachablePositions 1 :=
    Data.reachablePositions_eq (D₁ := geometricData) (D₂ := quarticData) rfl rfl 1
  exact ⟨PointingCapPolytopeData.SweepHornerTime12Burn1200.physical_enclosure hz,
    PointingCapPolytopeData.SweepHornerTaylor4Time12Burn1200.physical_enclosure (hs ▸ hz)⟩

end
end GNC.OrbitalComparison.PointingCapPolytopeComparison
