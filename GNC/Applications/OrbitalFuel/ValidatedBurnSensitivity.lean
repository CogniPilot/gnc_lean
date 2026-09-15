import GNC.Applications.OrbitalFuel.BurnSensitivityInputs
import GNC.Applications.OrbitalFuel.BurnSensitivityData
import GNC.Analysis.EuclideanBox

/-! Exact data certificates and continuous input enclosures validate the
solar terminal coefficient vectors. Nonlinear reserve closure and physical
attitude realization remain separate obligations. -/
noncomputable section
namespace GNC.Applications.OrbitalFuel.BurnSensitivity
open GNC.PolynomialODE GNC.PolynomialOrbitTransition

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

theorem entry_enclosure (i : Fin 12) (j : Fin 18) (k : Fin 3) :
    |physicalH z F H i j k-SharedBiasCertificates.Solar.h i j k| ≤ (entryAllowance i j k:ℝ) := by
  have h := (coefficient i j k).rounded_evaluation_error (center j) (region j) allowance
    (region_nonneg j) allowance_nonneg (fun _ => le_rfl) (reported i j k) (entryAllowance i j k)
    (output_certificate i j k) (terminalInput z F H j)
    (input_enclosure z F H hz hF hH hdz hdF hdH hiz hiF hiH j)
  dsimp only [terminalInput, FreeResponse.terminalInput] at h
  rwa [coefficient_correct, reported_matches] at h

theorem vector_enclosure (i : Fin 12) (j : Fin 18) :
    GNC.enorm (physicalH z F H i j-SharedBiasCertificates.Solar.h i j) ≤ (vectorAllowance i j:ℝ) := by
  apply GNC.enorm_le_of_component_bounds _ (fun k => (entryAllowance i j k:ℝ))
    (entry_enclosure z F H hz hF hH hdz hdF hdH hiz hiF hiH i j)
  · exact_mod_cast (vector_certificate i j).1
  · exact_mod_cast (vector_certificate i j).2

end Flow
end GNC.Applications.OrbitalFuel.BurnSensitivity
