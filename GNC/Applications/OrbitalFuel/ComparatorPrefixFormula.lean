import GNC.Applications.OrbitalFuel.RetainedNormData
import GNC.Applications.OrbitalFuel.SolarComparatorData
import GNC.Applications.OrbitalFuel.BurnFormula

/-! Exact scalar checks for transferring a candidate prefix enclosure to
the independent-burn comparator. Their dynamical use is proved separately.
The nominal polynomial is the existing candidate at the pointing-cap axis.
-/
namespace GNC.Applications.OrbitalFuel.ComparatorPrefix
open GNC PolynomialAffine PolynomialBounds PolynomialTranslation
open PolynomialBurn RetainedNorm

def pointingRadius : ℚ := 437/100000
def proposedPosition : ℚ := 10170000
def beta : ℚ := 50*BurnSensitivity.burnScale
def rate (j : Fin 18) : ℚ := beta*(|SolarComparatorData.y j-RetainedNormData.fractions j|+
  SolarComparatorData.y j*pointingRadius)
def impulse (t : ℚ) : ℚ :=
  ∑ j : Fin 18, (min t (burnFinish j)-min t (burnStart j))*rate j
def nominal (n : Fin 68) : VectorPolynomial :=
  plus ((RetainedNormData.pieces n).columns 0 0) ((RetainedNormData.pieces n).columns 0 3)
def center (n : Fin 68) : ℚ :=
  ((RetainedNormData.pieces n).start+(RetainedNormData.pieces n).finish)/2-
    (RetainedNormData.pieces n).offset
def radius (n : Fin 68) : ℚ :=
  ((RetainedNormData.pieces n).finish-(RetainedNormData.pieces n).start)/2

def Valid (n : Fin 68) (nominalMetres : ℚ) : Prop :=
  0 ≤ nominalMetres ∧
  bound (translate (center n) (pairing (nominal n) (nominal n))) (radius n) ≤
    (nominalMetres/lengthScale)^2 ∧
  nominalMetres+1+3250+
    4*(RetainedNormData.pieces n).finish*impulse (RetainedNormData.pieces n).finish*lengthScale <
      proposedPosition

instance (n : Fin 68) (r : ℚ) : Decidable (Valid n r) := by unfold Valid; infer_instance

end GNC.Applications.OrbitalFuel.ComparatorPrefix
