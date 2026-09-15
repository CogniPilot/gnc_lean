import GNC.Applications.OrbitalFuel.BurnTheory
import GNC.Applications.OrbitalFuel.BurnSensitivityFormula
import GNC.Applications.OrbitalFuel.BurnSchedule
import GNC.Applications.OrbitalFuel.RetainedNormData
import GNC.Analysis.PolynomialAccumulation

/-! Independently checkable coefficients for the accumulated solar forcing.
The four columns are the free response and the three common body-pointing
components. The six pulled-back rows are plane position/velocity followed
by normal position/velocity; output rows use Cartesian position then velocity.
-/
namespace GNC.Applications.OrbitalFuel.RetainedPrefix
open GNC GNC.PolynomialODE GNC.PolynomialBounds GNC.Planning.PolynomialKernel
open PolynomialBurn PolynomialTransition

def beta : ℚ := 50*BurnSensitivity.burnScale

def burn (arc : Fin 37) : Option (Fin 18) :=
  if h : arc.val%2 = 1 then some ⟨arc.val/2,by omega⟩ else none

def forcing (arc : Fin 37) (i : Fin 6) (k : Fin 4) : Expr 25 :=
  if hk : k.val = 0 then
    if hi : i.val < 4 then
      (Expr.constant (-alpha)).multiply (observable ⟨2*i.val+1,by omega⟩)
    else Expr.constant 0
  else match burn arc with
    | none => Expr.constant 0
    | some j =>
      let c : Fin 3 := ⟨k.val-1,by omega⟩
      let s := beta*RetainedNormData.fractions j
      if hi : i.val < 4 then
        (Expr.constant s).multiply
          (((Expr.constant (BurnSensitivity.rotation j 0 c)).multiply
              (observable ⟨2*i.val,by omega⟩)).add
            ((Expr.constant (BurnSensitivity.rotation j 1 c)).multiply
              (observable ⟨2*i.val+1,by omega⟩)))
      else (Expr.constant (s*BurnSensitivity.rotation j 2 c)).multiply
        (observable ⟨i.val+4,by omega⟩)

abbrev Columns := Fin 6 → Fin 4 → List ℚ

def forward (step : Fin 32) (pulled : Columns) (i : Fin 6) (k : Fin 4) : List ℚ :=
  let cs := (steps step).coefficients
  if hi : i.val%3 < 2 then
    let r : Fin 4 := ⟨2*(i.val/3)+i.val%3,by omega⟩
    add (add (multiply (cs (GNC.PolynomialOrbitTransition.planeIndex r 0)) (pulled 0 k))
        (multiply (cs (GNC.PolynomialOrbitTransition.planeIndex r 1)) (pulled 1 k)))
      (add (multiply (cs (GNC.PolynomialOrbitTransition.planeIndex r 2)) (pulled 2 k))
        (multiply (cs (GNC.PolynomialOrbitTransition.planeIndex r 3)) (pulled 3 k)))
  else
    let r : Fin 2 := ⟨i.val/3,by omega⟩
    add (multiply (cs (GNC.PolynomialOrbitTransition.normalIndex r 0)) (pulled 4 k))
      (multiply (cs (GNC.PolynomialOrbitTransition.normalIndex r 1)) (pulled 5 k))

def output (p : RetainedNorm.Piece) (i : Fin 6) (k : Fin 4) : List ℚ :=
  p.columns ⟨i.val/3,by omega⟩ k ⟨i.val%3,by omega⟩

structure Data where
  arc : Fin 37
  pulled : Columns

def Data.Valid (d : Data) (p : RetainedNorm.Piece) : Prop :=
  BurnSchedule.time d.arc.val ≤ p.start ∧ p.finish ≤ BurnSchedule.time (d.arc.val+1) ∧
  ∀ i k,
    (forcing d.arc i k).differenceMajorant (steps p.referenceStep).region
      (steps p.referenceStep).error ≤ 1/10^14 ∧
    bound (subtract (differentiate (d.pulled i k))
      ((forcing d.arc i k).coefficients (steps p.referenceStep).coefficients)) (3/160) ≤ 1/10^18 ∧
    bound (d.pulled i k) (3/160) ≤ 1 ∧
    bound (subtract (forward p.referenceStep d.pulled i k) (output p i k)) (3/160) ≤ 1/10^18

instance (d : Data) (p : RetainedNorm.Piece) : Decidable (d.Valid p) := by
  unfold Data.Valid; infer_instance

def Data.Compatible (d e : Data) (p q : RetainedNorm.Piece) : Prop :=
  p.finish = q.start ∧ ∀ i k,
    |evaluate (d.pulled i k) (p.finish-p.offset)-
      evaluate (e.pulled i k) (q.start-q.offset)| ≤ 1/10^18

instance (d e : Data) (p q : RetainedNorm.Piece) : Decidable (d.Compatible e p q) := by
  unfold Data.Compatible; infer_instance

end GNC.Applications.OrbitalFuel.RetainedPrefix
