import GNC.Applications.OrbitalFuel.ComparatorPrefixTheory
import GNC.Applications.OrbitalFuel.ChaserExistence

/-! Physical forcing differences for independently pointed comparison burns.
The same RTN rotation acts on both commands; orthogonality gives a Euclidean
bound. The prefix budget counts only elapsed burn time.
-/
noncomputable section
set_option autoImplicit false
namespace GNC.Applications.OrbitalFuel.ComparatorPrefix
open GNC PolynomialOrbit PolynomialOrbitTransition PolynomialBurn Set Matrix
open ChaserReferenceData ChaserExistence

def commands (q : Fin 18 → Vec3) (j : Fin 18) : Vec3 :=
  SolarComparator.plan j • rotate (SharedBiasGeometry.cycleRotation j) (q j)

def arcRate (k : ℕ) : ℝ := BurnSchedule.input (fun j _ => (rate j:ℝ)) k 0

theorem arcRate_nonneg (k : ℕ) : 0 ≤ arcRate k := by
  unfold arcRate BurnSchedule.input
  split_ifs
  · exact rate_nonneg _
  · exact le_rfl

theorem arc_budget_general (D : Fin 18 → ℝ) (t : ℝ) :
    ArcGronwall.prefixBudget nodes (fun k => BurnSchedule.input (fun j _ => D j) k 0) 37 t =
      ∑ j : Fin 18, (min t (burnFinish j:ℝ)-min t (burnStart j:ℝ))*D j := by
  have h := BurnPrefix.burn_integrals
    (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℝ)) (fun j _ _ => D j) t
  have hu (k : ℕ) (s : ℝ) :
      BurnSchedule.input (fun j _ (_ : Fin 1) => D j) k s =
        fun _ => BurnSchedule.input (fun j _ => D j) k 0 := by
    unfold BurnSchedule.input
    split_ifs <;> rfl
  simp_rw [one_mulVec,hu] at h
  simp only [intervalIntegral.integral_const] at h
  have he := congrFun h (0 : Fin 1)
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul] at he
  unfold ArcGronwall.prefixBudget ArcGronwall.budget
  rw [← show (∑ k ∈ Finset.range 37,
      (min (BurnSchedule.time (k+1):ℝ) t-min (BurnSchedule.time k:ℝ) t)*
        BurnSchedule.input (fun j _ => D j) k 0) =
      ∑ j : Fin 18, (min t (burnFinish j:ℝ)-min t (burnStart j:ℝ))*D j by
    simpa only [min_comm] using he]
  apply Finset.sum_congr rfl
  intro k hk
  dsimp only
  rw [nodes_eq k (by have := Finset.mem_range.mp hk; omega),
    nodes_eq (k+1) (by have := Finset.mem_range.mp hk; omega)]

theorem arc_budget (t : ℝ) :
    ArcGronwall.prefixBudget nodes arcRate 37 t = impulseReal t :=
  arc_budget_general (fun j => (rate j:ℝ)) t

theorem acceleration_difference (r : Flow) (q : Fin 18 → Vec3)
    (hq : ∀ j, q j ∈ ThrustSupport.Cap SharedBiasExample.axis SharedBiasCertificates.Solar.kappa)
    (k : ℕ) (t : ℝ) :
    GNC.enorm (acceleration r (commands q) k t-
      acceleration r (RetainedPhysical.commands SharedBiasExample.axis) k t) ≤ arcRate k := by
  unfold acceleration arcRate BurnSchedule.input
  split_ifs with hk
  · let j : Fin 18 := ⟨k/2,by omega⟩
    have hb : 0 ≤ (beta:ℝ) := by
      norm_num [beta,BurnSensitivity.burnScale,FreeResponse.lengthUnit]
    have hbeta : (RetainedPrefix.beta:ℝ) = (beta:ℝ) := rfl
    change GNC.enorm ((RetainedPrefix.beta:ℝ) •
      (polynomialFrame (lift (r.w t)) *ᵥ commands q j)-
      (RetainedPrefix.beta:ℝ) •
      (polynomialFrame (lift (r.w t)) *ᵥ RetainedPhysical.commands SharedBiasExample.axis j)) ≤ _
    rw [← smul_sub,← Matrix.mulVec_sub,GNC.enorm_smul,hbeta,abs_of_nonneg hb,
      frame_enorm _ (r.hr t)]
    have h := mul_le_mul_of_nonneg_left (command_difference j (q j) (hq j)) hb
    simpa only [commands,rate,Rat.cast_mul,Rat.cast_add,Rat.cast_abs,Rat.cast_sub] using h
  · simp [GNC.enorm]

theorem same_initial (r : Flow) (c d : Fin 18 → Vec3) (m : Motion r c) (n : Motion r d) :
    m.p 0 = n.p 0 ∧ m.v 0 = n.v 0 := by
  have hp := m.initialPlane.trans n.initialPlane.symm
  have hn := m.initialNormal.trans n.initialNormal.symm
  have h0 := congrFun hp 0
  have h1 := congrFun hp 1
  have h2 := congrFun hp 2
  have h3 := congrFun hp 3
  have h4 := congrFun hn 0
  have h5 := congrFun hn 1
  simp [PlanarChaserError.plane,PlanarChaserError.normal] at h0 h1 h2 h3 h4 h5
  constructor <;> ext i <;> fin_cases i <;> assumption

/-- On either proposed chaser region, the full nonlinear field is four-
Lipschitz in Euclidean length. No gravity linearization is used here. -/
theorem gravity_difference (w : Fin 4 → ℝ) (p q : Vec3)
    (hr : (7997/10000:ℝ) ≤ PolynomialOrbit.radius w)
    (hp : GNC.enorm ((RetainedNorm.lengthScale:ℝ) • (p-position w)) ≤ (proposedPosition:ℝ))
    (hq : GNC.enorm ((RetainedNorm.lengthScale:ℝ) • (q-position w)) ≤ (proposedPosition:ℝ)) :
    GNC.enorm (Gravity.field3 1 p-Gravity.field3 1 q) ≤ 4*GNC.enorm (p-q) := by
  have hpn : GNC.enorm (p-position w) ≤ (proposedPosition:ℝ)/(RetainedNorm.lengthScale:ℝ) := by
    rw [GNC.enorm_smul,abs_of_pos (show (0:ℝ) < (RetainedNorm.lengthScale:ℝ) by
      norm_num [RetainedNorm.lengthScale])] at hp
    exact (le_div_iff₀ (by norm_num [RetainedNorm.lengthScale])).mpr (by simpa [mul_comm] using hp)
  have hqn : GNC.enorm (q-position w) ≤ (proposedPosition:ℝ)/(RetainedNorm.lengthScale:ℝ) := by
    rw [GNC.enorm_smul,abs_of_pos (show (0:ℝ) < (RetainedNorm.lengthScale:ℝ) by
      norm_num [RetainedNorm.lengthScale])] at hq
    exact (le_div_iff₀ (by norm_num [RetainedNorm.lengthScale])).mpr (by simpa [mul_comm] using hq)
  have h := Gravity.field_difference_ball 1 (by norm_num)
    (WithLp.toLp 2 (position w) : Jacobian.E3) (WithLp.toLp 2 (p-position w))
    (WithLp.toLp 2 (q-position w)) (r := (799/1000:ℝ))
    (R := (proposedPosition:ℝ)/(RetainedNorm.lengthScale:ℝ)) (by norm_num)
    (by
      change _ ≤ GNC.enorm (position w)
      rw [position_norm]
      norm_num [proposedPosition,RetainedNorm.lengthScale] at *
      linarith) hpn hqn
  change GNC.enorm (Gravity.field3 1 (position w+(p-position w))-
    Gravity.field3 1 (position w+(q-position w))) ≤
    (2*1/(799/1000)^3)*GNC.enorm ((p-position w)-(q-position w)) at h
  rw [show position w+(p-position w) = p by abel,
    show position w+(q-position w) = q by abel] at h
  simp only [sub_sub_sub_cancel_right] at h
  exact h.trans (mul_le_mul_of_nonneg_right
    (show (2*1/(799/1000)^3:ℝ) ≤ 4 by norm_num) (GNC.enorm_nonneg _))

end GNC.Applications.OrbitalFuel.ComparatorPrefix
