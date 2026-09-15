import GNC.Applications.OrbitalFuel.RetainedPrefixData.Block0
import GNC.Applications.OrbitalFuel.RetainedPrefixData.Block1
import GNC.Applications.OrbitalFuel.RetainedPrefixData.Block2
import GNC.Applications.OrbitalFuel.RetainedPrefixData.Block3

namespace GNC.Applications.OrbitalFuel.RetainedPrefixData
open RetainedPrefix

def initial : Fin 6 → ℚ := ![0, (-100000/1495978707), (153093108923948631137330254669/1495978707000000000000000000000000), 0, (10000/1495978707), 0]

def pieces (i : Fin 68) : Data :=
  if h : i.val < 17 then Block0.pieces ⟨i.val,h⟩ else
  if h : i.val < 34 then Block1.pieces ⟨i.val-17,by omega⟩ else
  if h : i.val < 51 then Block2.pieces ⟨i.val-34,by omega⟩ else
  Block3.pieces ⟨i.val-51,by omega⟩

set_option maxRecDepth 100000 in
theorem valid (i : Fin 68) : (pieces i).Valid (RetainedNormData.pieces i) := by
  fin_cases i
  · exact Block0.valid0
  · exact Block0.valid1
  · exact Block0.valid2
  · exact Block0.valid3
  · exact Block0.valid4
  · exact Block0.valid5
  · exact Block0.valid6
  · exact Block0.valid7
  · exact Block0.valid8
  · exact Block0.valid9
  · exact Block0.valid10
  · exact Block0.valid11
  · exact Block0.valid12
  · exact Block0.valid13
  · exact Block0.valid14
  · exact Block0.valid15
  · exact Block0.valid16
  · exact Block1.valid0
  · exact Block1.valid1
  · exact Block1.valid2
  · exact Block1.valid3
  · exact Block1.valid4
  · exact Block1.valid5
  · exact Block1.valid6
  · exact Block1.valid7
  · exact Block1.valid8
  · exact Block1.valid9
  · exact Block1.valid10
  · exact Block1.valid11
  · exact Block1.valid12
  · exact Block1.valid13
  · exact Block1.valid14
  · exact Block1.valid15
  · exact Block1.valid16
  · exact Block2.valid0
  · exact Block2.valid1
  · exact Block2.valid2
  · exact Block2.valid3
  · exact Block2.valid4
  · exact Block2.valid5
  · exact Block2.valid6
  · exact Block2.valid7
  · exact Block2.valid8
  · exact Block2.valid9
  · exact Block2.valid10
  · exact Block2.valid11
  · exact Block2.valid12
  · exact Block2.valid13
  · exact Block2.valid14
  · exact Block2.valid15
  · exact Block2.valid16
  · exact Block3.valid0
  · exact Block3.valid1
  · exact Block3.valid2
  · exact Block3.valid3
  · exact Block3.valid4
  · exact Block3.valid5
  · exact Block3.valid6
  · exact Block3.valid7
  · exact Block3.valid8
  · exact Block3.valid9
  · exact Block3.valid10
  · exact Block3.valid11
  · exact Block3.valid12
  · exact Block3.valid13
  · exact Block3.valid14
  · exact Block3.valid15
  · exact Block3.valid16

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem joins (i : Fin 67) :
    (pieces i.castSucc).Compatible (pieces i.succ)
      (RetainedNormData.pieces i.castSucc) (RetainedNormData.pieces i.succ) := by
  fin_cases i <;> decide +kernel

set_option maxRecDepth 100000 in
theorem initial_error : ∀ i : Fin 6, ∀ k : Fin 4,
    |(if k = 0 then initial i else 0)-
      GNC.Planning.PolynomialKernel.evaluate ((pieces 0).pulled i k) 0| ≤ (1/10^18:ℚ) := by
  decide +kernel

end GNC.Applications.OrbitalFuel.RetainedPrefixData
