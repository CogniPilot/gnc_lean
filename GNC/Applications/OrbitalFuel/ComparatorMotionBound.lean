import GNC.Applications.OrbitalFuel.ComparatorForcing
import GNC.Analysis.SwitchedSecondOrder

/-! A comparison of actual nonlinear motions, with a regional hypothesis
that is discharged by the subsequent first-exit closure. This bound uses
the entire field difference and all independent pointing directions.
-/
noncomputable section
set_option autoImplicit false
namespace GNC.Applications.OrbitalFuel.ComparatorPrefix
open GNC GNC.ThrustSupport PolynomialOrbit PolynomialOrbitTransition Set Matrix
open ChaserReferenceData ChaserExistence

theorem field_continuous (r : Flow) (commands : Fin 18 → Vec3) (m : Motion r commands) :
    ContinuousOn (fun t => Gravity.field3 1 (m.p t)) (Icc (0:ℝ) (3/5)) := by
  intro t ht
  have hp : 0 < GNC.enorm (m.p t) := by
    have hn := m.noncollision t ht
    have he : GNC.enorm (m.p t) ≠ 0 := fun h => hn ((GNC.enorm_eq_zero_iff _).mp h)
    exact lt_of_le_of_ne (GNC.enorm_nonneg _) (Ne.symm he)
  exact (Gravity.field3_continuousAt 1 hp).comp_continuousWithinAt m.hp.continuousWithinAt

theorem prefix_difference (r : Flow) (q : Fin 18 → Vec3)
    (hq : ∀ j, q j ∈ Cap SharedBiasExample.axis SharedBiasCertificates.Solar.kappa)
    (m : Motion r (commands q))
    (c : Motion r (RetainedPhysical.commands SharedBiasExample.axis))
    {T : ℝ} (hT : T ∈ Icc (0:ℝ) (3/5))
    (hm : ∀ t ∈ Icc (0:ℝ) T,
      GNC.enorm ((RetainedNorm.lengthScale:ℝ) • (m.p t-position (r.w t))) ≤ (proposedPosition:ℝ))
    (hc : ∀ t ∈ Icc (0:ℝ) T,
      GNC.enorm ((RetainedNorm.lengthScale:ℝ) • (c.p t-position (r.w t))) ≤ (proposedPosition:ℝ)) :
    GNC.enorm ((RetainedNorm.lengthScale:ℝ) • (m.p T-c.p T)) ≤
      4*T*impulseReal T*(RetainedNorm.lengthScale:ℝ) := by
  let p : ℝ → Jacobian.E3 := fun t => euclideanEquiv (m.p t-c.p t)
  let v : ℝ → Jacobian.E3 := fun t => euclideanEquiv (m.v t-c.v t)
  let a : ℕ → ℝ → Jacobian.E3 := fun k t => euclideanEquiv
    (Gravity.field3 1 (m.p t)+acceleration r (commands q) k t-
      (Gravity.field3 1 (c.p t)+acceleration r (RetainedPhysical.commands SharedBiasExample.axis) k t))
  have hp : Continuous p := euclideanEquiv.continuous.comp (m.hp.sub c.hp)
  have hv : Continuous v := euclideanEquiv.continuous.comp (m.hv.sub c.hv)
  have hdom : Icc (0:ℝ) T ⊆ Icc 0 (3/5) := Icc_subset_Icc_right hT.2
  have ha (k : ℕ) : ContinuousOn (a k) (Icc 0 T) := by
    exact euclideanEquiv.continuous.comp_continuousOn
      ((((field_continuous r _ m).mono hdom).add
        (acceleration_continuous r (commands q) k).continuousOn).sub
        (((field_continuous r _ c).mono hdom).add
          (acceleration_continuous r (RetainedPhysical.commands SharedBiasExample.axis) k).continuousOn))
  have hdp (k : ℕ) (hk : k < 37) (t : ℝ)
      (ht : t ∈ Ioo (nodes k) (nodes (k+1))) : HasDerivAt p (v t) t := by
    have ht' : t ∈ Ioo (BurnSchedule.time k:ℝ) (BurnSchedule.time (k+1):ℝ) := by
      simpa only [nodes_eq k (by omega),nodes_eq (k+1) (by omega)] using ht
    exact euclideanEquiv.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t
      ((m.position_derivative k hk t ht').fun_sub (c.position_derivative k hk t ht'))
  have hdv (k : ℕ) (hk : k < 37) (t : ℝ)
      (ht : t ∈ Ioo (nodes k) (nodes (k+1))) : HasDerivAt v (a k t) t := by
    have ht' : t ∈ Ioo (BurnSchedule.time k:ℝ) (BurnSchedule.time (k+1):ℝ) := by
      simpa only [nodes_eq k (by omega),nodes_eq (k+1) (by omega)] using ht
    exact euclideanEquiv.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t
      ((m.velocity_derivative k hk t ht').fun_sub (c.velocity_derivative k hk t ht'))
  have hi := same_initial r _ _ m c
  have h := ArcGronwall.second_order p v a nodes arcRate 37 nodes_monotone nodes_zero
    (by simpa only [nodes_final] using hT) hT.2 hp hv (fun k _ => ha k)
    (fun k hk t _ ht => hdp k hk t ht) (fun k hk t _ ht => hdv k hk t ht)
    (fun k _ => arcRate_nonneg k) (by
      intro k hk t ht
      change GNC.enorm _ ≤ 4*GNC.enorm (m.p t-c.p t)+arcRate k
      have he : Gravity.field3 1 (m.p t)+acceleration r (commands q) k t-
          (Gravity.field3 1 (c.p t)+acceleration r (RetainedPhysical.commands SharedBiasExample.axis) k t) =
          (Gravity.field3 1 (m.p t)-Gravity.field3 1 (c.p t))+
            (acceleration r (commands q) k t-
              acceleration r (RetainedPhysical.commands SharedBiasExample.axis) k t) := by abel
      rw [he]
      exact (GNC.enorm_add_le _ _).trans (add_le_add
        (gravity_difference (r.w t) (m.p t) (c.p t)
          (Reference.physical_solar_annulus r.w r.hw r.hdw r.hiw t (hdom ht)).1.le
          (hm t ht) (hc t ht)) (acceleration_difference r q hq k t)))
    (by simp [p,hi.1]) (by simp [v,hi.2])
  rw [arc_budget] at h
  rw [GNC.enorm_smul,abs_of_pos (show (0:ℝ) < (RetainedNorm.lengthScale:ℝ) by
    norm_num [RetainedNorm.lengthScale])]
  have hp' : GNC.enorm (m.p T-c.p T) ≤ 4*T*impulseReal T := h.1
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hp'
    (show (0:ℝ) ≤ (RetainedNorm.lengthScale:ℝ) by norm_num [RetainedNorm.lengthScale])

end GNC.Applications.OrbitalFuel.ComparatorPrefix
