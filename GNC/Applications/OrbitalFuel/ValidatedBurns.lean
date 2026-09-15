import GNC.Applications.OrbitalFuel.PolynomialBurns
import GNC.Applications.OrbitalFuel.BurnTheory

/-! All 18 normalized solar burn pullback means are enclosed against their
reported rational values. This includes the physical RTN injection and actual
inverse fundamental matrices. Terminal multiplication and SI conversion are
subsequent operations, not silently included in this entrywise allowance.
-/
noncomputable section
namespace GNC.Applications.OrbitalFuel.PolynomialBurn
open GNC.PolynomialODE GNC.PolynomialOrbitTransition

theorem enclosure (x : Trajectory) (j : Fin 18) (o : Fin 10) :
    |50*(∫ t in (burnStart j:ℝ)..(burnFinish j:ℝ), (observable o).value (x.state t)) -
      (centers j o:ℝ)| ≤ 2/10^14 := by
  have h := x.rounded_mean (cells j) o (centers j o) (cells_valid j) (cells_join j)
    (by rw [cells_finish, cells_start]; exact burn_duration j) (centers_error j o)
  simpa only [cells_start, cells_finish] using h

def planeSlot (i : Fin 4) (k : Fin 2) : Fin 10 := ⟨2*i.val+k.val,by omega⟩
def normalSlot (i : Fin 2) : Fin 10 := ⟨8+i.val,by omega⟩

theorem observable_plane (i : Fin 4) (k : Fin 2) :
    observable (planeSlot i k) = planeObservable i k := by
  fin_cases i <;> fin_cases k <;> rfl

theorem observable_normal (i : Fin 2) : observable (normalSlot i) = normalObservable i := by
  fin_cases i <;> rfl

theorem burn_domain (j : Fin 18) {t : ℝ}
    (ht : t ∈ Set.uIcc (burnStart j:ℝ) (burnFinish j:ℝ)) : t ∈ Set.Icc (0:ℝ) (3/5) := by
  obtain ⟨ha,hab,hb⟩ := burn_range j
  have habR : (burnStart j:ℝ) ≤ (burnFinish j:ℝ) := by exact_mod_cast hab
  have hbR : (burnFinish j:ℝ) ≤ 3/5 := by
    have hcast := (Rat.cast_le (K := ℝ)).mpr hb
    norm_num at hcast ⊢
    exact hcast
  rw [Set.uIcc_of_le habR] at ht
  exact ⟨le_trans (by exact_mod_cast ha) ht.1, ht.2.trans hbR⟩

section Flow
variable (z : ℝ → Fin 5 → ℝ)
    (F : ℝ → Matrix (Fin 4) (Fin 4) ℝ) (H : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hz : Continuous z) (hF : Continuous F) (hH : Continuous H)
    (hdz : ∀ t ∈ Set.Icc (0:ℝ) (3/5), HasDerivAt z (GNC.PolynomialOrbit.rate PolynomialTransition.alpha (z t)) t)
    (hdF : ∀ t ∈ Set.Icc (0:ℝ) (3/5), HasDerivAt F (planeGenerator (z t) * F t) t)
    (hdH : ∀ t ∈ Set.Icc (0:ℝ) (3/5), HasDerivAt H (normalGenerator (z t) * H t) t)
    (hiz : z 0 = ValidatedReference.initial) (hiF : F 0 = 1) (hiH : H 0 = 1)

include z F H hz hF hH hdz hdF hdH hiz hiF hiH

theorem flow_plane (j : Fin 18) (i : Fin 4) (k : Fin 2) :
    |50*(∫ t in (burnStart j:ℝ)..(burnFinish j:ℝ), ((F t)⁻¹ * planeInjection (z t)) i k) -
      (centers j (planeSlot i k):ℝ)| ≤ 2/10^14 := by
  have h := enclosure (Trajectory.ofFlow z F H hz hF hH hdz hdF hdH hiz hiF hiH) j (planeSlot i k)
  change |50*(∫ t in (burnStart j:ℝ)..(burnFinish j:ℝ),
    (observable (planeSlot i k)).value (pack (z t) (F t) (H t))) - _| ≤ _ at h
  have he : (∫ t in (burnStart j:ℝ)..(burnFinish j:ℝ),
      (observable (planeSlot i k)).value (pack (z t) (F t) (H t))) =
      ∫ t in (burnStart j:ℝ)..(burnFinish j:ℝ), ((F t)⁻¹ * planeInjection (z t)) i k := by
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [observable_plane, plane_inverse z F hdF hiF t (burn_domain j ht)]
    exact planeObservable_correct (z t) (F t) (H t) i k
  rwa [he] at h

theorem flow_normal (j : Fin 18) (i : Fin 2) :
    |50*(∫ t in (burnStart j:ℝ)..(burnFinish j:ℝ), (H t)⁻¹ i 1) -
      (centers j (normalSlot i):ℝ)| ≤ 2/10^14 := by
  have h := enclosure (Trajectory.ofFlow z F H hz hF hH hdz hdF hdH hiz hiF hiH) j (normalSlot i)
  change |50*(∫ t in (burnStart j:ℝ)..(burnFinish j:ℝ),
    (observable (normalSlot i)).value (pack (z t) (F t) (H t))) - _| ≤ _ at h
  have he : (∫ t in (burnStart j:ℝ)..(burnFinish j:ℝ),
      (observable (normalSlot i)).value (pack (z t) (F t) (H t))) =
      ∫ t in (burnStart j:ℝ)..(burnFinish j:ℝ), (H t)⁻¹ i 1 := by
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [observable_normal, normal_inverse z H hdH hiH t (burn_domain j ht)]
    exact normalObservable_correct (z t) (F t) (H t) i
  rwa [he] at h
end Flow

/-- The original physical planar reference, including its RTN frame orientation.
As in the earlier trajectory certificate, solution existence/noncollision is
explicit; the approximation and integration error allowances are proved. -/
theorem physical_enclosure (w : ℝ → Fin 4 → ℝ)
    (F : ℝ → Matrix (Fin 4) (Fin 4) ℝ) (H : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hw : Continuous w) (hF : Continuous F) (hH : Continuous H)
    (hr : ∀ t, 0 < GNC.PolynomialOrbit.radius (w t))
    (hdw : ∀ t ∈ Set.Icc (0:ℝ) (3/5),
      HasDerivAt w (GNC.PolynomialOrbit.physicalRate PolynomialTransition.alpha (w t)) t)
    (hdF : ∀ t ∈ Set.Icc (0:ℝ) (3/5),
      HasDerivAt F (planeGenerator (GNC.PolynomialOrbit.lift (w t)) * F t) t)
    (hdH : ∀ t ∈ Set.Icc (0:ℝ) (3/5),
      HasDerivAt H (normalGenerator (GNC.PolynomialOrbit.lift (w t)) * H t) t)
    (hiw : w 0 = ![4/5,0,0,Real.sqrt (3/2)]) (hiF : F 0 = 1) (hiH : H 0 = 1) :
    (∀ j : Fin 18, ∀ i : Fin 4, ∀ k : Fin 2,
      |50*(∫ t in (burnStart j:ℝ)..(burnFinish j:ℝ), ((F t)⁻¹ * physicalPlaneInjection (w t)) i k) -
        (centers j (planeSlot i k):ℝ)| ≤ 2/10^14) ∧
    (∀ j : Fin 18, ∀ i : Fin 2,
      |50*(∫ t in (burnStart j:ℝ)..(burnFinish j:ℝ), (H t)⁻¹ i 1) -
        (centers j (normalSlot i):ℝ)| ≤ 2/10^14) := by
  have hz := GNC.PolynomialOrbit.lift_continuous hw hr
  have hdz := fun t ht => GNC.PolynomialOrbit.lift_derivative (hdw t ht) (hr t)
  have hiz : (fun t => GNC.PolynomialOrbit.lift (w t)) 0 = ValidatedReference.initial := by
    change GNC.PolynomialOrbit.lift (w 0) = _
    rw [hiw]
    norm_num [GNC.PolynomialOrbit.lift, GNC.PolynomialOrbit.radius, ValidatedReference.initial]
    exact ⟨rfl,rfl⟩
  have hmoment : ∀ t ∈ Set.Icc (0:ℝ) (3/5), 0 < angularMomentum (w t) := by
    apply angularMomentum_positive w hw (by norm_num [PolynomialTransition.alpha]) (fun t _ => hr t) hdw
    rw [hiw]
    simp [angularMomentum]
  constructor
  · intro j i k
    have h := flow_plane (fun t => GNC.PolynomialOrbit.lift (w t)) F H hz hF hH
      hdz hdF hdH hiz hiF hiH j i k
    have he : (∫ t in (burnStart j:ℝ)..(burnFinish j:ℝ),
        ((F t)⁻¹ * planeInjection (GNC.PolynomialOrbit.lift (w t))) i k) =
        ∫ t in (burnStart j:ℝ)..(burnFinish j:ℝ), ((F t)⁻¹ * physicalPlaneInjection (w t)) i k := by
      apply intervalIntegral.integral_congr
      intro t ht
      dsimp only
      rw [planeInjection_physical (w t) (hmoment t (burn_domain j ht))]
    rwa [he] at h
  · exact flow_normal (fun t => GNC.PolynomialOrbit.lift (w t)) F H hz hF hH
      hdz hdF hdH hiz hiF hiH

end GNC.Applications.OrbitalFuel.PolynomialBurn
