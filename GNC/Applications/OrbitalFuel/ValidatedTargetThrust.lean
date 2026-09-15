import GNC.Applications.OrbitalFuel.TargetThrustData
import GNC.Applications.OrbitalFuel.TargetThrustTheory

/-! The four whole-mission target-thrust integrals have proved rational
centers. The error allowance includes ODE error, integration and rounding.
-/
noncomputable section
namespace GNC.Applications.OrbitalFuel.TargetThrust
open GNC.PolynomialODE GNC.PolynomialOrbitTransition PolynomialBurn

theorem enclosure (x : Trajectory) (i : Fin 4) :
    |(∫ t in (0:ℝ)..(3/5), (observable (tangentSlot i)).value (x.state t))-
      (centers i:ℝ)| ≤ (1/10^14:ℝ) := by
  have h := integral_error x i
  have hr : |(integralSum i:ℝ)-(centers i:ℝ)| ≤ (1/10^25:ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr (centers_error i)
    norm_num at hc ⊢
    exact hc
  have ha := abs_sub_le
    (∫ t in (0:ℝ)..(3/5), (observable (tangentSlot i)).value (x.state t))
    (integralSum i:ℝ) (centers i:ℝ)
  linarith

theorem flow_enclosure (z : ℝ → Fin 5 → ℝ)
    (F : ℝ → Matrix (Fin 4) (Fin 4) ℝ) (H : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hz : Continuous z) (hF : Continuous F) (hH : Continuous H)
    (hdz : ∀ t ∈ Set.Icc (0:ℝ) (3/5),
      HasDerivAt z (GNC.PolynomialOrbit.rate PolynomialTransition.alpha (z t)) t)
    (hdF : ∀ t ∈ Set.Icc (0:ℝ) (3/5), HasDerivAt F (planeGenerator (z t)*F t) t)
    (hdH : ∀ t ∈ Set.Icc (0:ℝ) (3/5), HasDerivAt H (normalGenerator (z t)*H t) t)
    (hiz : z 0 = ValidatedReference.initial) (hiF : F 0 = 1) (hiH : H 0 = 1) (i : Fin 4) :
    |(∫ t in (0:ℝ)..(3/5), ((F t)⁻¹ * planeInjection (z t)) i 1)-(centers i:ℝ)| ≤ (1/10^14:ℝ) := by
  have h := enclosure (Trajectory.ofFlow z F H hz hF hH hdz hdF hdH hiz hiF hiH) i
  change |(∫ t in (0:ℝ)..(3/5),
    (observable (tangentSlot i)).value (pack (z t) (F t) (H t)))-(centers i:ℝ)| ≤ _ at h
  have he : (∫ t in (0:ℝ)..(3/5),
      (observable (tangentSlot i)).value (pack (z t) (F t) (H t))) =
      ∫ t in (0:ℝ)..(3/5), ((F t)⁻¹ * planeInjection (z t)) i 1 := by
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [tangentSlot_correct, plane_inverse z F hdF hiF t
      (by norm_num [Set.uIcc_of_le] at ht ⊢; exact ht)]
    exact planeObservable_correct (z t) (F t) (H t) i 1
  rwa [he] at h

end GNC.Applications.OrbitalFuel.TargetThrust
