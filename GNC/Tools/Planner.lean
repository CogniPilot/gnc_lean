import GNC.Planning.Hermite
import Lean.Data.Json.FromToJson

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

private def report (args : List String) : Except String Lean.Json :=
  match args with
  | "hermite" :: rest => hermiteReport rest
  | _ => seedReport args

def main (args : List String) : IO UInt32 := do
  match report args with
  | .ok result => IO.println result.pretty; return 0
  | .error message => IO.eprintln message; return 1
