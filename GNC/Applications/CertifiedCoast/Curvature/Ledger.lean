import GNC.Applications.CertifiedCoast.Curvature.Step

/-! Initial radii and node error bounds of the curvature certificate chain. -/
namespace GNC.Applications.CertifiedCoast.Curvature.Ledger
open GNC.Applications.CertifiedCoast.Curvature
/-- Initial position error radius (normalized length). -/
def e0p : ℚ := 0
/-- Initial velocity error radius (normalized velocity). -/
def e0v : ℚ := (967140655691703339764941/21778071482940061661655974875633165533184)
/-- Certified terminal position error bound (normalized length). -/
def posBound : ℚ := (104130290736131653788839632763601777871649135514546973719797717152939393/971334446112864535459730953411759453321203419526069760625906204869452142602604249088)
/-- Certified terminal velocity error bound (normalized velocity), including
the kinematic mismatch of the stored velocity polynomial. -/
def velBound : ℚ := (394314318949455734714537733216170353635360402554625685363210910615734339/3885337784451458141838923813647037813284813678104279042503624819477808570410416996352)
/-- Kinematic mismatch of the final step's stored velocity polynomial. -/
def velKinematic : ℚ := (266240924009902603872205/87112285931760246646623899502532662132736)
end GNC.Applications.CertifiedCoast.Curvature.Ledger
