import GNC.Applications.OrbitalFuel.FreeResponseData
import GNC.Applications.OrbitalFuel.FreeResponseGeometry
import GNC.Applications.OrbitalFuel.ValidatedTerminalData
import GNC.Applications.OrbitalFuel.ValidatedTargetThrust

/-! Solar free-response correspondence with the existing rational fuel
program. The normalized RHS error is at most 10^-10, including certified
reference/transition, target-thrust, SI conversion and rounding errors.
The nonlinear residual reserve is a separate physical obligation.
-/
noncomputable section
namespace GNC.Applications.OrbitalFuel.FreeResponse
open GNC.PolynomialODE GNC.PolynomialOrbitTransition PolynomialBurn

def pullbackIntegrals (z : ℝ → Fin 5 → ℝ) (F : ℝ → Matrix (Fin 4) (Fin 4) ℝ) (i : Fin 4) : ℝ :=
  ∫ t in (0:ℝ)..(3/5), ((F t)⁻¹ * planeInjection (z t)) i 1

def terminalInput (z : ℝ → Fin 5 → ℝ) (F : ℝ → Matrix (Fin 4) (Fin 4) ℝ)
    (H : ℝ → Matrix (Fin 2) (Fin 2) ℝ) : Fin 31 → ℝ :=
  packedInput (z (3/5)) (F (3/5)) (H (3/5))
    (Real.sqrt (TerminalData.speedSquared:ℝ)) (Real.sqrt (3/2)) (pullbackIntegrals z F)

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

theorem input_enclosure (i : Fin 31) :
    |terminalInput z F H i-(center i:ℝ)| ≤ (allowance i:ℝ) := by
  by_cases h25 : i.val < 25
  · have h := TerminalData.endpoint_enclosure
      (Trajectory.ofFlow z F H hz hF hH hdz hdF hdH hiz hiF hiH) ⟨i.val,h25⟩
    change |pack (z (3/5)) (F (3/5)) (H (3/5)) ⟨i.val,h25⟩-
      (TerminalData.endpoint ⟨i.val,h25⟩:ℝ)| ≤ _ at h
    by_cases h5 : i.val < 5 <;>
      simpa [terminalInput, packedInput, center, allowance, h25, h5, TerminalData.endpointError] using h
  · have h5 : ¬i.val < 5 := by omega
    by_cases he25 : i.val = 25
    · have h27 : i.val < 27 := by omega
      simpa [terminalInput, packedInput, center, allowance, h5, h25, he25, h27] using
        TerminalData.speed_enclosure
    · by_cases he26 : i.val = 26
      · have h27 : i.val < 27 := by omega
        simpa [terminalInput, packedInput, center, allowance, h5, h25, he25, he26, h27] using
          TerminalData.initialSpeed_enclosure
      · have h27 : ¬i.val < 27 := by omega
        have h := TargetThrust.flow_enclosure z F H hz hF hH hdz hdF hdH hiz hiF hiH ⟨i.val-27,by omega⟩
        simpa [terminalInput, packedInput, center, allowance, pullbackIntegrals,
          h5, h25, he25, he26, h27] using h

theorem expression_enclosure (i : Fin 6) :
    |(constraintOutput i).value (terminalInput z F H)-(reported i:ℝ)| ≤ (1/10^10:ℝ) := by
  have h := (constraintOutput i).rounded_evaluation_error center region allowance
    region_nonneg allowance_nonneg (fun _ => le_rfl) (reported i) (1/10^10)
    (output_certificate i) (terminalInput z F H)
    (input_enclosure z F H hz hF hH hdz hdF hdH hiz hiF hiH)
  norm_num at h ⊢
  exact h

/-- Physical terminal RTN position/velocity, normalized by the actual mission
tolerances, agrees with the free response encoded by the two signed LP rows.
-/
theorem physical_enclosure (i : Fin 6) :
    |physicalOutput (z (3/5)) (F (3/5)) (H (3/5))
        (Real.sqrt (TerminalData.speedSquared:ℝ)) (Real.sqrt (3/2)) (pullbackIntegrals z F) i /
      (tolerance i:ℝ)-(reported i:ℝ)| ≤ (1/10^10:ℝ) := by
  have h := expression_enclosure z F H hz hF hH hdz hdF hdH hiz hiF hiH i
  dsimp only [terminalInput] at h
  rwa [constraintOutput_correct] at h

def beta (i : Fin 6) : ℝ :=
  (SharedBiasCertificates.Solar.b (negativeRow i)+SharedBiasCertificates.Solar.b (positiveRow i))/2

/-- Preserve the declared symmetric terminal reserve while replacing the
numerical free response by the certified physical expression. Both signed
right-hand sides move by at most 10^-10. This does not prove the reserve's
nonlinear regional closure, nor the burn-sensitivity coefficient enclosure.
-/
theorem rhs_enclosure (i : Fin 6) :
    |beta i+(constraintOutput i).value (terminalInput z F H)-
      SharedBiasCertificates.Solar.b (negativeRow i)| ≤ (1/10^10:ℝ) ∧
    |beta i-(constraintOutput i).value (terminalInput z F H)-
      SharedBiasCertificates.Solar.b (positiveRow i)| ≤ (1/10^10:ℝ) := by
  have h := expression_enclosure z F H hz hF hH hdz hdF hdH hiz hiF hiH i
  have he : beta i+(constraintOutput i).value (terminalInput z F H)-
      SharedBiasCertificates.Solar.b (negativeRow i) =
      (constraintOutput i).value (terminalInput z F H)-(reported i:ℝ) := by
    rw [reported_matches]
    unfold beta
    ring
  have hp : beta i-(constraintOutput i).value (terminalInput z F H)-
      SharedBiasCertificates.Solar.b (positiveRow i) =
      -((constraintOutput i).value (terminalInput z F H)-(reported i:ℝ)) := by
    rw [reported_matches]
    unfold beta
    ring
  rw [he,hp,abs_neg]
  exact ⟨h,h⟩

end Flow

theorem beta_bounds (i : Fin 6) : 0 < beta i ∧ beta i < 1 := by
  fin_cases i <;> norm_num [beta, negativeRow, positiveRow, SharedBiasCertificates.Solar.b,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

/-- Specialization to the original noncolliding physical planar reference.
The inverse-radius lift, its derivative and initialization are discharged
using the previously verified physical-model bridge.
-/
theorem physical_model_enclosure (w : ℝ → Fin 4 → ℝ)
    (F : ℝ → Matrix (Fin 4) (Fin 4) ℝ) (H : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hw : Continuous w) (hF : Continuous F) (hH : Continuous H)
    (hr : ∀ t, 0 < GNC.PolynomialOrbit.radius (w t))
    (hdw : ∀ t ∈ Set.Icc (0:ℝ) (3/5),
      HasDerivAt w (GNC.PolynomialOrbit.physicalRate PolynomialTransition.alpha (w t)) t)
    (hdF : ∀ t ∈ Set.Icc (0:ℝ) (3/5),
      HasDerivAt F (planeGenerator (GNC.PolynomialOrbit.lift (w t))*F t) t)
    (hdH : ∀ t ∈ Set.Icc (0:ℝ) (3/5),
      HasDerivAt H (normalGenerator (GNC.PolynomialOrbit.lift (w t))*H t) t)
    (hiw : w 0 = ![4/5,0,0,Real.sqrt (3/2)]) (hiF : F 0 = 1) (hiH : H 0 = 1) (i : Fin 6) :
    |physicalOutput (GNC.PolynomialOrbit.lift (w (3/5))) (F (3/5)) (H (3/5))
        (Real.sqrt (TerminalData.speedSquared:ℝ)) (Real.sqrt (3/2))
        (pullbackIntegrals (fun t => GNC.PolynomialOrbit.lift (w t)) F) i /
      (tolerance i:ℝ)-(reported i:ℝ)| ≤ (1/10^10:ℝ) := by
  apply physical_enclosure (fun t => GNC.PolynomialOrbit.lift (w t)) F H
    (GNC.PolynomialOrbit.lift_continuous hw hr) hF hH
    (fun t ht => GNC.PolynomialOrbit.lift_derivative (hdw t ht) (hr t)) hdF hdH ?_ hiF hiH i
  change GNC.PolynomialOrbit.lift (w 0) = ValidatedReference.initial
  rw [hiw]
  norm_num [GNC.PolynomialOrbit.lift, GNC.PolynomialOrbit.radius, ValidatedReference.initial]
  exact ⟨rfl,rfl⟩

end GNC.Applications.OrbitalFuel.FreeResponse
