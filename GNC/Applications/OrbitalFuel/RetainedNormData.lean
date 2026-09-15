import GNC.Applications.OrbitalFuel.RetainedNormData.Block0
import GNC.Applications.OrbitalFuel.RetainedNormData.Block1
import GNC.Applications.OrbitalFuel.RetainedNormData.Block2
import GNC.Applications.OrbitalFuel.RetainedNormData.Block3

namespace GNC.Applications.OrbitalFuel.RetainedNormData
open GNC GNC.ThrustSupport RetainedNorm

def fractions : Fin 18 → ℚ := ![0, (201118470833/500000000000), 0, (6371636931/20000000000), 0, (11331126277/250000000000), 0, 0, 0, 0, 0, 0, 0, 0, (50903536401/1000000000000), (46964340107/200000000000), (157607254421/500000000000), 0]

def pieces (i : Fin 68) : Piece :=
  if h : i.val < 17 then Block0.pieces ⟨i.val,h⟩ else
  if h : i.val < 34 then Block1.pieces ⟨i.val-17,by omega⟩ else
  if h : i.val < 51 then Block2.pieces ⟨i.val-34,by omega⟩ else
  Block3.pieces ⟨i.val-51,by omega⟩

theorem valid (i : Fin 68) : (pieces i).Valid := by
  unfold pieces
  split_ifs
  · exact Block0.valid _
  · exact Block1.valid _
  · exact Block2.valid _
  · exact Block3.valid _

set_option maxRecDepth 100000 in
theorem joins : ∀ i : Fin 67, (pieces i.castSucc).finish = (pieces i.succ).start := by
  decide +kernel

theorem initial : (pieces 0).start = 0 := by decide +kernel
theorem final : (pieces 67).finish = 3/5 := by decide +kernel

theorem coverage {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) (3/5)) :
    ∃ i : Fin 68, t ∈ Set.Icc ((pieces i).start:ℝ) ((pieces i).finish:ℝ) := by
  have hi : ((pieces 0).start:ℝ) = 0 := by exact_mod_cast initial
  have hf : ((pieces (Fin.last 67)).finish:ℝ) = 3/5 := by
    change ((pieces 67).finish:ℝ) = 3/5
    rw [final]
    norm_num
  apply interval_chain_covers (fun i => ((pieces i).start:ℝ))
    (fun i => ((pieces i).finish:ℝ)) (fun i => by dsimp only; exact_mod_cast joins i)
  simpa only [hi,hf] using ht

/-- Uniform polynomial-family bounds, with no time or pointing sampling.
This does not assert the missing physical coefficient/flow correspondence. -/
theorem enclosure {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) (3/5)) (q : Vec3)
    (hq : q ∈ Cap pointingAxis (kappa:ℝ)) :
    ∃ i : Fin 68, t ∈ Set.Icc ((pieces i).start:ℝ) ((pieces i).finish:ℝ) ∧
      ∀ j, GNC.enorm ((pieces i).response j t q)*(scale j:ℝ) ≤ (bound j:ℝ) := by
  obtain ⟨i,hi⟩ := coverage ht
  exact ⟨i,hi,fun j => (pieces i).enclosure (valid i) j hi q hq⟩

end GNC.Applications.OrbitalFuel.RetainedNormData
