import GNC.Applications.CertifiedCoast.Curvature.Step

/-! Initial radii and node error bounds of the curvature certificate chain. -/
namespace GNC.Applications.CertifiedCoast.Curvature.LedgerInit
open GNC.Applications.CertifiedCoast.Curvature
/-- Initial position error radius (normalized length). -/
def e0p : ℚ := (1/1000000)
/-- Initial velocity error radius (normalized velocity). -/
def e0v : ℚ := (340282366936050036208557472115595414581/340282366920938463463374607431768211456000000)
/-- Certified terminal position error bound (normalized length). -/
def posBound : ℚ := (1631303505889985021029292105675097184682644862894369484890508944729164490117841215651/30354201441027016733116592294117482916287606860189680019559568902170379456331382784000000)
/-- Certified terminal velocity error bound (normalized velocity), including
the kinematic mismatch of the stored velocity polynomial. -/
def velBound : ℚ := (3130496547218934925878533487172227548159997661886779240309760956449793971204496753811/60708402882054033466233184588234965832575213720379360039119137804340758912662765568000000)
/-- Kinematic mismatch of the final step's stored velocity polynomial. -/
def velKinematic : ℚ := (266240924009902603872205/87112285931760246646623899502532662132736)
end GNC.Applications.CertifiedCoast.Curvature.LedgerInit
