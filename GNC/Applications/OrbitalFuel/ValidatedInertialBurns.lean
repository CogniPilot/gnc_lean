import GNC.Applications.OrbitalFuel.InertialBurnData
import GNC.Applications.OrbitalFuel.ValidatedBurns
import GNC.Applications.OrbitalFuel.ReferenceFlowExistence

/-! Continuous validation of all 180 inertial burn pullback means.
The existing ODE defect and jump certificates are reused through generic
observable integration. This is not yet a new terminal/fuel certificate. -/
noncomputable section
set_option autoImplicit false
namespace GNC.Applications.OrbitalFuel.InertialBurn
open GNC.PolynomialODE GNC.PolynomialOrbitTransition PolynomialBurn

theorem enclosure (x : PolynomialBurn.Trajectory) (j : Fin 18) (o : Fin 10) :
    |50*(∫ t in (burnStart j:ℝ)..(burnFinish j:ℝ), (observable o).value (x.state t)) -
      (centers j o:ℝ)| ≤ 2/10^14 := by
  have h := x.observable_mean_error (cells j) (observable o) (1/10^14)
    (fun k => observation_errors k o) (cells_valid j) (cells_join j)
    (by rw [cells_finish, cells_start]; exact burn_duration j)
  change |50*(∫ t in ((cells j 0).start:ℝ)..((cells j 2).finish:ℝ),
    (observable o).value (x.state t))-(mean j o:ℝ)| ≤ ((1/10^14:ℚ):ℝ) at h
  rw [cells_start, cells_finish] at h
  norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat] at h
  have hr : |(mean j o:ℝ)-(centers j o:ℝ)| ≤ (1/10^25:ℝ) := by
    have hcast := (Rat.cast_le (K := ℝ)).mpr (centers_error j o)
    norm_num at hcast ⊢
    exact hcast
  have ht := abs_sub_le
    (50*(∫ t in (burnStart j:ℝ)..(burnFinish j:ℝ), (observable o).value (x.state t)))
    (mean j o:ℝ) (centers j o:ℝ)
  linarith

theorem observable_plane (i : Fin 4) (k : Fin 2) :
    observable (planeSlot i k) = inverseColumn i k := by
  fin_cases i <;> fin_cases k <;> rfl

theorem observable_normal (i : Fin 2) : observable (normalSlot i) = normalObservable i := by
  fin_cases i <;> rfl

def trajectory (r : ReferenceFlowExistence.Flow) : PolynomialBurn.Trajectory :=
  PolynomialBurn.Trajectory.ofFlow (fun t => GNC.PolynomialOrbit.lift (r.w t)) r.F r.H
    (GNC.PolynomialOrbit.lift_continuous r.hw r.hr) r.hF r.hH
    (fun t ht => GNC.PolynomialOrbit.lift_derivative (r.hdw t ht) (r.hr t)) r.hdF r.hdH
    (by
      change GNC.PolynomialOrbit.lift (r.w 0) = ValidatedReference.initial
      rw [r.hiw]
      norm_num [GNC.PolynomialOrbit.lift, GNC.PolynomialOrbit.radius, ValidatedReference.initial]
      exact ⟨rfl,rfl⟩) r.hiF r.hiH

/-- Mean columns of the actual inverse fundamental matrix for a fixed
inertial acceleration, before terminal multiplication or attitude rotation. -/
theorem plane_enclosure (r : ReferenceFlowExistence.Flow) (j : Fin 18) (i : Fin 4) (k : Fin 2) :
    |50*(∫ t in (burnStart j:ℝ)..(burnFinish j:ℝ), (r.F t)⁻¹ i ⟨2+k.val,by omega⟩) -
      (centers j (planeSlot i k):ℝ)| ≤ 2/10^14 := by
  have h := enclosure (trajectory r) j (planeSlot i k)
  change |50*(∫ t in (burnStart j:ℝ)..(burnFinish j:ℝ),
    (observable (planeSlot i k)).value (pack (GNC.PolynomialOrbit.lift (r.w t)) (r.F t) (r.H t)))-_|≤_ at h
  have he : (∫ t in (burnStart j:ℝ)..(burnFinish j:ℝ),
      (observable (planeSlot i k)).value (pack (GNC.PolynomialOrbit.lift (r.w t)) (r.F t) (r.H t))) =
      ∫ t in (burnStart j:ℝ)..(burnFinish j:ℝ), (r.F t)⁻¹ i ⟨2+k.val,by omega⟩ := by
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [observable_plane, inverseColumn_correct,
      plane_inverse _ r.F r.hdF r.hiF t (burn_domain j ht)]
  rwa [he] at h

theorem normal_enclosure (r : ReferenceFlowExistence.Flow) (j : Fin 18) (i : Fin 2) :
    |50*(∫ t in (burnStart j:ℝ)..(burnFinish j:ℝ), (r.H t)⁻¹ i 1) -
      (centers j (normalSlot i):ℝ)| ≤ 2/10^14 := by
  have h := enclosure (trajectory r) j (normalSlot i)
  change |50*(∫ t in (burnStart j:ℝ)..(burnFinish j:ℝ),
    (observable (normalSlot i)).value (pack (GNC.PolynomialOrbit.lift (r.w t)) (r.F t) (r.H t)))-_|≤_ at h
  have he : (∫ t in (burnStart j:ℝ)..(burnFinish j:ℝ),
      (observable (normalSlot i)).value (pack (GNC.PolynomialOrbit.lift (r.w t)) (r.F t) (r.H t))) =
      ∫ t in (burnStart j:ℝ)..(burnFinish j:ℝ), (r.H t)⁻¹ i 1 := by
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [observable_normal, normalObservable_correct,
      normal_inverse _ r.H r.hdH r.hiH t (burn_domain j ht)]
  rwa [he] at h

end GNC.Applications.OrbitalFuel.InertialBurn
