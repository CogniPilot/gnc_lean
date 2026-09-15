import GNC.Applications.OrbitalFuel.BurnSensitivityGeometry
import GNC.Applications.OrbitalFuel.ValidatedBurns
import GNC.Applications.OrbitalFuel.ValidatedFreeResponse

/-! Assemble the certified continuous burn means and terminal quantities
into the input box used by the solar coefficient evaluator. -/
noncomputable section
namespace GNC.Applications.OrbitalFuel.BurnSensitivity
open GNC.PolynomialODE GNC.PolynomialOrbitTransition

def means (z : ℝ → Fin 5 → ℝ) (F : ℝ → Matrix (Fin 4) (Fin 4) ℝ)
    (H : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (j : Fin 18) (o : Fin 10) : ℝ :=
  if h : o.val < 8 then
    50*(∫ t in (PolynomialBurn.burnStart j:ℝ)..(PolynomialBurn.burnFinish j:ℝ),
      ((F t)⁻¹ * planeInjection (z t)) ⟨o.val/2,by omega⟩ ⟨o.val%2,by omega⟩)
  else 50*(∫ t in (PolynomialBurn.burnStart j:ℝ)..(PolynomialBurn.burnFinish j:ℝ),
      (H t)⁻¹ ⟨o.val-8,by omega⟩ 1)

def terminalInput (z : ℝ → Fin 5 → ℝ) (F : ℝ → Matrix (Fin 4) (Fin 4) ℝ)
    (H : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (j : Fin 18) : Fin 41 → ℝ :=
  packedInput (FreeResponse.terminalInput z F H) (means z F H j)

def physicalH (z : ℝ → Fin 5 → ℝ) (F : ℝ → Matrix (Fin 4) (Fin 4) ℝ)
    (H : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (i : Fin 12) (j : Fin 18) : GNC.Vec3 :=
  physicalCoefficient (z (3/5)) (F (3/5)) (H (3/5))
    (Real.sqrt (TerminalData.speedSquared:ℝ)) (means z F H j) i j

section Flow
variable (z : ℝ → Fin 5 → ℝ)
    (F : ℝ → Matrix (Fin 4) (Fin 4) ℝ) (H : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hz : Continuous z) (hF : Continuous F) (hH : Continuous H)
    (hdz : ∀ t ∈ Set.Icc (0:ℝ) (3/5),
      HasDerivAt z (GNC.PolynomialOrbit.rate PolynomialTransition.alpha (z t)) t)
    (hdF : ∀ t ∈ Set.Icc (0:ℝ) (3/5), HasDerivAt F (planeGenerator (z t)*F t) t)
    (hdH : ∀ t ∈ Set.Icc (0:ℝ) (3/5), HasDerivAt H (normalGenerator (z t)*H t) t)
    (hiz : z 0 = ValidatedReference.initial) (hiF : F 0 = 1) (hiH : H 0 = 1)
include hz hF hH hdz hdF hdH hiz hiF hiH

theorem means_enclosure (j : Fin 18) (o : Fin 10) :
    |means z F H j o-(PolynomialBurn.centers j o:ℝ)| ≤ (2/10^14:ℝ) := by
  by_cases ho : o.val < 8
  · have h := PolynomialBurn.flow_plane z F H hz hF hH hdz hdF hdH hiz hiF hiH
      j ⟨o.val/2,by omega⟩ ⟨o.val%2,by omega⟩
    have he : PolynomialBurn.planeSlot ⟨o.val/2,by omega⟩ ⟨o.val%2,by omega⟩ = o := by
      ext
      simp only [PolynomialBurn.planeSlot]
      omega
    rw [he] at h
    simpa [means, ho] using h
  · have h := PolynomialBurn.flow_normal z F H hz hF hH hdz hdF hdH hiz hiF hiH
      j ⟨o.val-8,by omega⟩
    have he : PolynomialBurn.normalSlot ⟨o.val-8,by omega⟩ = o := by
      ext
      simp only [PolynomialBurn.normalSlot]
      omega
    rw [he] at h
    simpa [means, ho] using h

theorem input_enclosure (j : Fin 18) (i : Fin 41) :
    |terminalInput z F H j i-(center j i:ℝ)| ≤ (allowance i:ℝ) := by
  by_cases hi : i.val < 31
  · simpa [terminalInput, packedInput, center, allowance, hi] using
      FreeResponse.input_enclosure z F H hz hF hH hdz hdF hdH hiz hiF hiH ⟨i.val,hi⟩
  · have h := means_enclosure z F H hz hF hH hdz hdF hdH hiz hiF hiH j ⟨i.val-31,by omega⟩
    norm_num [terminalInput, packedInput, center, allowance, hi] at h ⊢
    exact h

end Flow
end GNC.Applications.OrbitalFuel.BurnSensitivity
