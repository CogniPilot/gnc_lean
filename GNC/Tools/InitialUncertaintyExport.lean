import GNC.Applications.OrbitalComparison.InitialUncertaintyData
import Lean.Data.Json

/-! Export the actual checked rational records for plotting. Floating
plotting and moment quadrature are outside the mathematical proof claim. -/
namespace GNC.Tools.InitialUncertaintyExport
open Lean GNC.OrbitalComparison InitialUncertaintyData

def rationals (xs : List ℚ) : Json := toJson (xs.map toString)
def vector (x : PointingCapPolynomial.Vector) : Json :=
  toJson ((List.finRange 3).map fun i => (x i).map fun a =>
    Json.mkObj [("u",toJson a.u),("v",toJson a.v),("c",toJson a.c),("time",rationals a.time)])

def payload : Json := Json.mkObj [
  ("status",toJson "Rational records: validity and tube containment proved in InitialUncertaintyData"),
  ("duration_s",toJson (120 : Nat)), ("initial_position_radius_m",toJson (10 : Nat)),
  ("initial_velocity_radius_m_s",toJson "1/100"), ("pointing_half_angle_rad",toJson "7/20"),
  ("rdr",Json.mkObj [("gain",toJson (toString RDR.data.gain)),
    ("region_radius_m",toJson (toString RDR.data.positionBound)),
    ("forcing",rationals RDR.forcing),("base",rationals RDR.base),
    ("growth",rationals RDR.growth),("envelope",rationals RDR.envelope),
    ("position_transfer",toJson "0"),("velocity_transfer",toJson "0"),
    ("q",vector RDR.data.q)]),
  ("lie3",Json.mkObj [("gain",toJson (toString Lie3.data.gain)),
    ("region_radius_m",toJson (toString Lie3.data.positionBound)),
    ("forcing",rationals Lie3.forcing),("base",rationals Lie3.base),
    ("growth",rationals Lie3.growth),("envelope",rationals Lie3.envelope),
    ("position_transfer",toJson (toString (LieSTTData.Output.position.error Lie3.data))),
    ("velocity_transfer",toJson (toString (LieSTTData.Output.velocity.error Lie3.data))),
    ("z",vector LieSTTData.Output.position.z),
    ("zv",vector LieSTTData.Output.velocity.z)])]

end GNC.Tools.InitialUncertaintyExport
