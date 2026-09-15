import GNC.Applications.OrbitalFuel.ComparatorPrefixTheory
import GNC.Applications.OrbitalFuel.ExistingSolarCertificate

/-! A time-resolved enclosure for the actual nominal candidate, obtained
from the existing polynomial response and already certified gravity reserve.
This reference motion anchors the independent-comparator comparison proof.
-/
noncomputable section
set_option autoImplicit false
namespace GNC.Applications.OrbitalFuel.ComparatorPrefix
open GNC PolynomialOrbit PolynomialOrbitTransition PolynomialBurn Set Matrix
open ChaserReferenceData ChaserExistence

theorem candidate_region (r : Flow)
    (m : Motion r (RetainedPhysical.commands SharedBiasExample.axis))
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) (3/5)) :
    GNC.enorm ((RetainedNorm.lengthScale:ℝ) • (m.p t-position (r.w t))) ≤ (proposedPosition:ℝ) := by
  have h := SolarRegion.continuous_nonlinear_enclosure r.w m.p m.v r.F r.H SharedBiasExample.axis
    r.hw m.hp m.hv r.hF r.hH r.hr m.noncollision r.hdw r.hdF r.hdH r.hiw r.hiF r.hiH
    m.initialPlane m.initialNormal m.position_derivative m.velocity_derivative axis_in_cap t ht
  exact h.1.trans (by norm_num [proposedPosition])

theorem nominal_candidate (r : Flow)
    (m : Motion r (RetainedPhysical.commands SharedBiasExample.axis))
    (n : Fin 68) {t : ℝ} (ht : t ∈ Icc (0:ℝ) (3/5))
    (hn : t ∈ Icc ((RetainedNormData.pieces n).start:ℝ) ((RetainedNormData.pieces n).finish:ℝ)) :
    GNC.enorm ((RetainedNorm.lengthScale:ℝ) • (m.p t-position (r.w t))) ≤
      (ComparatorPrefixData.nominalMetres n:ℝ)+1+3250 := by
  let z := fun s => lift (r.w s)
  have hz : Continuous z := lift_continuous r.hw r.hr
  have hdz := fun s hs => lift_derivative (r.hdw s hs) (r.hr s)
  have hiz : z 0 = ValidatedReference.initial := by
    change lift (r.w 0) = ValidatedReference.initial
    rw [r.hiw]
    norm_num [lift,PolynomialOrbit.radius,ValidatedReference.initial]
    exact ⟨rfl,rfl⟩
  let x := Trajectory.ofFlow z r.F r.H hz r.hF r.hH hdz r.hdF r.hdH hiz r.hiF r.hiH
  let retained := RetainedPhysical.retained z r.F r.H (Real.sqrt (3/2:ℝ)) SharedBiasExample.axis t 0
  let polynomial := (RetainedNormData.pieces n).response 0 t SharedBiasExample.axis
  have he := RetainedPhysical.polynomial_error x z r.F r.H hz r.hF r.hH (fun _ => rfl)
    n ht hn SharedBiasExample.axis axis_unit 0
  have heSI : GNC.enorm ((RetainedNorm.lengthScale:ℝ) • (retained-polynomial)) ≤ 1 := by
    rw [GNC.enorm_smul,abs_of_pos (show (0:ℝ) < (RetainedNorm.lengthScale:ℝ) by
      norm_num [RetainedNorm.lengthScale])]
    exact (mul_le_mul_of_nonneg_left he (show (0:ℝ) ≤ (RetainedNorm.lengthScale:ℝ) by
      norm_num [RetainedNorm.lengthScale])).trans (by norm_num [RetainedNorm.lengthScale])
  have hret : GNC.enorm ((RetainedNorm.lengthScale:ℝ) • retained) ≤
      (ComparatorPrefixData.nominalMetres n:ℝ)+1 := by
    have h := GNC.enorm_add_le ((RetainedNorm.lengthScale:ℝ) • (retained-polynomial))
      ((RetainedNorm.lengthScale:ℝ) • polynomial)
    rw [← smul_add,sub_add_cancel] at h
    linarith [nominal_enclosure n hn]
  have hall := SolarRegion.continuous_nonlinear_enclosure r.w m.p m.v r.F r.H SharedBiasExample.axis
    r.hw m.hp m.hv r.hF r.hH r.hr m.noncollision r.hdw r.hdF r.hdH r.hiw r.hiF r.hiH
    m.initialPlane m.initialNormal m.position_derivative m.velocity_derivative axis_in_cap t ht
  have hid := RetainedPhysical.nonlinear_decomposition r.w m.p m.v r.F r.H SharedBiasExample.axis
    r.hw m.hp m.hv r.hF r.hH r.hr m.noncollision r.hdw r.hdF r.hdH r.hiF r.hiH
    m.initialPlane m.initialNormal m.position_derivative m.velocity_derivative ht 0
  rw [RetainedPhysical.deviation_position] at hid
  rw [hid,smul_add]
  have h := GNC.enorm_add_le ((RetainedNorm.lengthScale:ℝ) • retained)
    ((RetainedNorm.lengthScale:ℝ) • RetainedPhysical.remainder r.F r.H
      (fun s => PlanarChaserError.residual (r.w s) (m.p s)) t 0)
  exact h.trans (by linarith [hall.2.2.1])

end GNC.Applications.OrbitalFuel.ComparatorPrefix
