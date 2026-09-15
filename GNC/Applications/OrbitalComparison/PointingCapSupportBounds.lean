import GNC.Applications.OrbitalComparison.PointingCapSupportData.HornerTime12Burn1200
import GNC.Applications.OrbitalComparison.PointingCapSupportData.HornerTaylor4Time12Burn1200

/-! Two independently checked enclosures of one physical terminal support.
These are bounds on the largest directional displacement, not lower bounds
on the displacement of every reachable position. -/
namespace GNC.OrbitalComparison.PointingCapSupportBounds
open PointingCapClearance SpatialBurn Set
noncomputable section

def physicalSupport : ℝ := support PointingCapData.HornerTime12Burn1200.data

theorem geometric_interval :
    847.145577≤physicalSupport ∧ physicalSupport≤847.151817 := by
  have h := PointingCapSupportData.HornerTime12Burn1200.support_display
  rw [PointingCapSupportData.HornerTime12Burn1200.display_values.1,
    PointingCapSupportData.HornerTime12Burn1200.display_values.2] at h
  norm_num at h
  dsimp only [physicalSupport]
  constructor <;> linarith [h.1,h.2]

theorem quartic_interval :
    847.144156≤physicalSupport ∧ physicalSupport≤847.152589 := by
  have h := PointingCapSupportData.HornerTaylor4Time12Burn1200.support_display
  rw [PointingCapSupportData.HornerTaylor4Time12Burn1200.display_values.1,
    PointingCapSupportData.HornerTaylor4Time12Burn1200.display_values.2] at h
  have he := support_eq (D₁ := PointingCapData.HornerTaylor4Time12Burn1200.data)
    (D₂ := PointingCapData.HornerTime12Burn1200.data) rfl rfl
  rw [he] at h
  norm_num at h
  dsimp only [physicalSupport]
  constructor <;> linarith [h.1,h.2]

/-- A synthetic 850 m terminal halfspace query. This is an example of the
certificate interface, not a spacecraft mission clearance requirement. -/
def exampleForbidden : Set E3 :=
  {z | 850≤observable (PointingCapObstruction.framed z)}

theorem geometric_clearance :
    Disjoint (PointingCapData.HornerTime12Burn1200.data.reachablePositions 1)
      exampleForbidden := by
  apply halfspace_clearance _ PointingCapData.HornerTime12Burn1200.valid rfl
    PointingCapSupportData.HornerTime12Burn1200.certificate
    PointingCapSupportData.HornerTime12Burn1200.checked rfl 850
  have h : PointingCapSupportData.HornerTime12Burn1200.upper<850 := by decide +kernel
  exact_mod_cast h

theorem quartic_clearance :
    Disjoint (PointingCapData.HornerTaylor4Time12Burn1200.data.reachablePositions 1)
      exampleForbidden := by
  apply halfspace_clearance _ PointingCapData.HornerTaylor4Time12Burn1200.valid rfl
    PointingCapSupportData.HornerTaylor4Time12Burn1200.certificate
    PointingCapSupportData.HornerTaylor4Time12Burn1200.checked rfl 850
  have h : PointingCapSupportData.HornerTaylor4Time12Burn1200.upper<850 := by decide +kernel
  exact_mod_cast h

end
end GNC.OrbitalComparison.PointingCapSupportBounds
