import GNC.Applications.OrbitalFuel.ComparatorMotionBound
import GNC.Applications.OrbitalFuel.ComparatorNominal

/-! Close the comparator's actual nonlinear position region. Independent
pointing on each burn is retained, and the comparison bound is applied only
within a proposed prefix before a first-exit argument discharges that premise.
-/
noncomputable section
set_option autoImplicit false
namespace GNC.Applications.OrbitalFuel.ComparatorPrefix
open GNC PolynomialOrbit PolynomialOrbitTransition Set Matrix
open ChaserReferenceData ChaserExistence

theorem continuous_region (r : Flow) (q : Fin 18 → Vec3)
    (hq : ∀ j, q j ∈ ThrustSupport.Cap SharedBiasExample.axis SharedBiasCertificates.Solar.kappa)
    (m : Motion r (commands q)) :
    ∀ t ∈ Icc (0:ℝ) (3/5),
      GNC.enorm ((RetainedNorm.lengthScale:ℝ) • (m.p t-position (r.w t))) < (proposedPosition:ℝ) := by
  obtain ⟨c⟩ := exists_motion r (RetainedPhysical.commands SharedBiasExample.axis)
    (shared_commands_bound SharedBiasExample.axis axis_in_cap)
  have hw := r.hw
  have hpc : Continuous (fun t => position (r.w t)) := by
    apply continuous_pi
    intro i
    fin_cases i <;> simp [position] <;> fun_prop
  have hf : Continuous (fun t => GNC.enorm ((RetainedNorm.lengthScale:ℝ) •
      (m.p t-position (r.w t)))) :=
    GNC.enorm_continuous.comp ((m.hp.sub hpc).const_smul (RetainedNorm.lengthScale:ℝ))
  have hi : GNC.enorm ((RetainedNorm.lengthScale:ℝ) • (m.p 0-position (r.w 0))) <
      (proposedPosition:ℝ) := by
    rw [(same_initial r _ _ m c).1]
    obtain ⟨n,hn⟩ := RetainedNormData.coverage (show (0:ℝ) ∈ Icc 0 (3/5) by norm_num)
    have h := nominal_candidate r c n (by norm_num) hn
    have hb := position_budget n (by norm_num : (0:ℝ) ≤ 0) hn.2
    simp only [mul_zero,zero_mul,add_zero] at hb
    exact h.trans_lt hb
  have hclose (t : ℝ) (ht : t ∈ Icc (0:ℝ) (3/5))
      (hprefix : ∀ s ∈ Icc (0:ℝ) t,
        GNC.enorm ((RetainedNorm.lengthScale:ℝ) • (m.p s-position (r.w s))) ≤ (proposedPosition:ℝ)) :
      GNC.enorm ((RetainedNorm.lengthScale:ℝ) • (m.p t-position (r.w t))) < (proposedPosition:ℝ) := by
    have hd := prefix_difference r q hq m c ht hprefix
      (fun s hs => candidate_region r c ⟨hs.1,hs.2.trans ht.2⟩)
    obtain ⟨n,hn⟩ := RetainedNormData.coverage ht
    have hc := nominal_candidate r c n ht hn
    have hb := position_budget n ht.1 hn.2
    have he : m.p t-position (r.w t) = (m.p t-c.p t)+(c.p t-position (r.w t)) := by abel
    rw [he,smul_add]
    exact (GNC.enorm_add_le _ _).trans_lt (by linarith)
  exact IntegralTube.prefix_closure hf hi hclose

end GNC.Applications.OrbitalFuel.ComparatorPrefix
