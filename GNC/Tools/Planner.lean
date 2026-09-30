import GNC.Planning.Hermite
import Lean.Data.Json.FromToJson
import GNC.Tools.InitialUncertaintyExport
import GNC.Applications.OrbitalComparison.FiniteEvaluation
import GNC.Applications.OrbitalComparison.FiniteBatchEvaluation

/-! Exact rational Dubins-polynomial seed and nominal-distance derivatives.
Run inside the pinned flake:
  lake env lean --run GNC/Tools/Planner.lean -1/4 -1/4 10 5 4
Arguments are a, b, positive length, nominal distance, maximum derivative order.
General endpoint interpolation:
  lake env lean --run GNC/Tools/Planner.lean hermite 0,0,-1/4,0 0,0,-1/4,0 10 5 4
Each endpoint argument is value, first, second, third nominal-distance derivative.
The arithmetic is covered by PolynomialKernel; the CLI parser and JSON I/O
are ordinary executable code, not a verified translation or rounding layer.
-/
open GNC.Planning.PolynomialKernel
open Lean

private def parseRational (s : String) : Except String ℚ := do
  let parseInt (s : String) : Except String Int :=
    match s.toInt? with
    | some n => .ok n
    | none => .error s!"Expected integer, got {s}"
  match s.splitOn "/" with
  | [n] => return (← parseInt n : Int)
  | [n, d] =>
    let n ← parseInt n
    let d ← parseInt d
    if d == 0 then throw "A rational denominator cannot be zero"
    return (n : ℚ) / (d : ℚ)
  | _ => throw s!"Expected an integer or numerator/denominator, got {s}"

private def seedReport (args : List String) : Except String Lean.Json := do
  let [a, b, length, distance, order] := args |
    throw "Usage: Planner.lean a b length distance maxDerivative (exact integers/fractions)"
  let a ← parseRational a
  let b ← parseRational b
  let length ← parseRational length
  let distance ← parseRational distance
  let some order := order.toNat? | throw "Derivative order must be a natural number"
  if length ≤ 0 then throw "Segment length must be positive"
  if order > 32 then throw "This CLI limits derivative order to 32"
  let rational (x : ℚ) := Lean.Json.str (toString x)
  let values := (List.range (order+1)).map fun n =>
    Lean.Json.mkObj [("order", toJson n), ("value", rational (physicalJet a b length distance n))]
  return Lean.Json.mkObj [
    ("arithmetic", .str "exact rational"),
    ("a", rational a), ("b", rational b),
    ("length", rational length), ("nominal_distance", rational distance),
    ("normalized_coefficients", toJson ((seedCoefficients a b).map rational)),
    ("physical_jets", toJson values)]

private def parseEndpoint (s : String) : Except String (Fin 4 → ℚ) := do
  let [a, b, c, d] ← (s.splitOn ",").mapM parseRational |
    throw "An endpoint must have four comma-separated values: value,first,second,third"
  return ![a, b, c, d]

private def hermiteReport (args : List String) : Except String Lean.Json := do
  let [start, finish, length, distance, order] := args |
    throw "Usage: Planner.lean hermite startJet endJet length distance maxDerivative"
  let start ← parseEndpoint start
  let finish ← parseEndpoint finish
  let length ← parseRational length
  let distance ← parseRational distance
  let some order := order.toNat? | throw "Derivative order must be a natural number"
  if length ≤ 0 then throw "Segment length must be positive"
  if order > 32 then throw "This CLI limits derivative order to 32"
  let rational (x : ℚ) := Lean.Json.str (toString x)
  let values := (List.range (order+1)).map fun n =>
    Lean.Json.mkObj [("order", toJson n),
      ("value", rational (GNC.Planning.Hermite.physicalJet start finish length distance n))]
  return Lean.Json.mkObj [
    ("arithmetic", .str "exact rational"),
    ("construction", .str "septic Hermite"),
    ("start_jet", toJson ((List.ofFn start).map rational)),
    ("end_jet", toJson ((List.ofFn finish).map rational)),
    ("length", rational length), ("nominal_distance", rational distance),
    ("normalized_coefficients", toJson
      ((GNC.Planning.Hermite.coefficients start finish length).map rational)),
    ("physical_jets", toJson values)]

private def orbitEvaluationReport (args : List String) : Except String Lean.Json := do
  let [time, px, py, pz] := args |
    throw "Usage: Planner.lean orbit-evaluation time_seconds phi_x phi_y phi_z (exact integers/fractions)"
  let time ← parseRational time
  let px ← parseRational px
  let py ← parseRational py
  let pz ← parseRational pz
  if time < 0 || 600 < time then throw "Certified burn time is 0 through 600 seconds"
  if (1:ℚ)/2500 < px^2+py^2+pz^2 then throw "Certified rotation-vector norm is at most 1/50 radian"
  let phi : Fin 3 → ℚ := ![px,py,pz]
  let t := time/600
  let rational (q : ℚ) := Lean.Json.str (toString q)
  let vector (v : Fin 3 → ℚ) := toJson ((List.ofFn v).map rational)
  let geom := GNC.OrbitalComparison.FiniteEvaluation.physicalPrediction
    GNC.OrbitalComparison.FiniteQueryGraphData.geometric
    GNC.OrbitalComparison.FiniteQueryGraphData.geometricOutputs t phi
  let cart := GNC.OrbitalComparison.FiniteEvaluation.physicalPrediction
    GNC.OrbitalComparison.FiniteQueryGraphData.cartesian
    GNC.OrbitalComparison.FiniteQueryGraphData.cartesianOutputs t phi
  return Json.mkObj [
    ("arithmetic",toJson "nearest dyadic, 53 normalized fractional bits, ties upward; rational SI output"),
    ("time_s",rational time),("normalized_time",rational t),("rotation_vector_rad",vector phi),
    ("geometric_position_m",vector geom),("cartesian_position_m",vector cart),
    ("geometric_error_bound_m",rational (913/1000000)),
    ("cartesian_error_bound_m",rational (313/1000000)),
    ("proof",toJson "GNC.OrbitalComparison.FiniteEvaluation.certificates"),
    ("scope",toJson "Stated shared-input inverse-square model and initial conditions; not IEEE, compiler or hardware verification")]

private def parseRotation (s : String) : Except String (Fin 3 → ℚ) := do
  let [x, y, z] ← (s.splitOn ",").mapM parseRational |
    throw "A rotation vector needs three comma-separated rational components"
  if (1:ℚ)/2500 < x^2+y^2+z^2 then throw "Certified rotation-vector norm is at most 1/50 radian"
  return ![x,y,z]

private def orbitBatchReport (args : List String) : Except String Lean.Json := do
  let time :: rotations := args |
    throw "Usage: Planner.lean orbit-batch-evaluation time_seconds x,y,z [x,y,z ...]"
  if rotations.isEmpty then throw "Provide at least one rotation vector"
  let time ← parseRational time
  if time < 0 || 600 < time then throw "Certified burn time is 0 through 600 seconds"
  let angles ← rotations.mapM parseRotation
  let t := time/600
  let rational (q : ℚ) := Lean.Json.str (toString q)
  let vector (v : Fin 3 → ℚ) := toJson ((List.ofFn v).map rational)
  let geoCache := GNC.OrbitalComparison.FiniteBatchEvaluation.prepare
    GNC.OrbitalComparison.FiniteBatchData.geometricPrepare t
  let cartCache := GNC.OrbitalComparison.FiniteBatchEvaluation.prepare
    GNC.OrbitalComparison.FiniteBatchData.cartesianPrepare t
  let queries := angles.map fun phi => Json.mkObj [
    ("rotation_vector_rad",vector phi),
    ("geometric_position_m",vector (GNC.OrbitalComparison.FiniteBatchEvaluation.physicalPrediction
      GNC.OrbitalComparison.FiniteBatchData.geometricQuery
      GNC.OrbitalComparison.FiniteBatchData.geometricOutputs geoCache phi)),
    ("cartesian_position_m",vector (GNC.OrbitalComparison.FiniteBatchEvaluation.physicalPrediction
      GNC.OrbitalComparison.FiniteBatchData.cartesianQuery
      GNC.OrbitalComparison.FiniteBatchData.cartesianOutputs cartCache phi))]
  return Json.mkObj [
    ("arithmetic",toJson "nearest dyadic, 53 normalized fractional bits, ties upward; rational SI output"),
    ("time_s",rational time),("normalized_time",rational t),
    ("query_count",toJson angles.length),("queries",toJson queries),
    ("geometric_arithmetic",toJson (GNC.ArithmeticProgram.batchArithmetic
      GNC.OrbitalComparison.FiniteBatchData.geometricPrepare
      GNC.OrbitalComparison.FiniteBatchData.geometricQuery angles.length)),
    ("cartesian_arithmetic",toJson (GNC.ArithmeticProgram.batchArithmetic
      GNC.OrbitalComparison.FiniteBatchData.cartesianPrepare
      GNC.OrbitalComparison.FiniteBatchData.cartesianQuery angles.length)),
    ("geometric_error_bound_m",rational (913/1000000)),
    ("cartesian_error_bound_m",rational (313/1000000)),
    ("proof",toJson "GNC.OrbitalComparison.FiniteBatchEvaluation.certificates"),
    ("scope",toJson "Immutable preparation; shared-input inverse-square model and initial conditions. Counts exclude rounding, reference evaluation and memory; not IEEE, compiler or hardware verification")]

private def report (args : List String) : Except String Lean.Json :=
  match args with
  | "orbit-batch-evaluation" :: rest => orbitBatchReport rest
  | "orbit-evaluation" :: rest => orbitEvaluationReport rest
  | ["orbit-uncertainty"] => .ok GNC.Tools.InitialUncertaintyExport.payload
  | "hermite" :: rest => hermiteReport rest
  | _ => seedReport args

def main (args : List String) : IO UInt32 := do
  match report args with
  | .ok result => IO.println result.pretty; return 0
  | .error message => IO.eprintln message; return 1
