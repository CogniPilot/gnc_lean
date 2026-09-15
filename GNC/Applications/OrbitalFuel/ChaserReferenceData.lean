import GNC.Applications.OrbitalFuel.ReferenceFlowExistence
import GNC.Applications.OrbitalFuel.PhysicalReferenceEnclosure
import GNC.Applications.OrbitalFuel.RetainedPhysicalIntegrals
import GNC.Applications.OrbitalFuel.ChaserResponse
import GNC.Applications.OrbitalFuel.ChaserContinuation

/-! Discharge the reference and forcing bounds used for chaser existence.
The frame preserves physical vector length; no acceleration bound is inferred
from samples. Every command sequence of norm at most one is covered.
-/
noncomputable section
set_option autoImplicit false
namespace GNC.Applications.OrbitalFuel.ChaserReferenceData
open GNC PolynomialOrbit PolynomialOrbitTransition Set Matrix
abbrev Flow := ReferenceFlowExistence.Flow

def clampTime (t : ℝ) : ℝ := max 0 (min (3/5) t)

theorem clamp_mem (t : ℝ) : clampTime t ∈ Icc (0:ℝ) (3/5) :=
  ⟨le_max_left _ _,max_le (by norm_num) (min_le_left _ _)⟩

theorem clamp_eq {t : ℝ} (ht : t ∈ Icc (0:ℝ) (3/5)) : clampTime t = t := by
  simp only [clampTime,min_eq_right ht.2,max_eq_right ht.1]

theorem clamp_continuous : Continuous clampTime :=
  continuous_const.max (continuous_const.min continuous_id)

def center (r : Flow) (t : ℝ) : Vec3 := position (r.w (clampTime t))
def thrust (r : Flow) (t : ℝ) : Vec3 :=
  PlanarChaserError.referenceThrust (PolynomialTransition.alpha:ℝ) (r.w (clampTime t))

theorem frame_continuous {X : Type*} [TopologicalSpace X]
    (z : X → Fin 5 → ℝ) (hz : Continuous z) :
    Continuous (fun t => polynomialFrame (z t)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  fin_cases i <;> fin_cases j <;> simp [polynomialFrame] <;> fun_prop

theorem frame_enorm (w : Fin 4 → ℝ) (hr : 0 < radius w) (q : Vec3) :
    GNC.enorm (polynomialFrame (lift w) *ᵥ q) = GNC.enorm q := by
  have hv : polynomialFrame (lift w) *ᵥ q =
      ![w 0*(radius w)⁻¹*q 0-w 1*(radius w)⁻¹*q 1,
        w 1*(radius w)⁻¹*q 0+w 0*(radius w)⁻¹*q 1,q 2] := by
    ext i
    fin_cases i <;> simp [polynomialFrame,lift,Matrix.mulVec,dotProduct,
      Fin.sum_univ_succ] <;> ring
  have he : lengthSq (polynomialFrame (lift w) *ᵥ q) = lengthSq q := by
    rw [hv]
    change (w 0*(radius w)⁻¹*q 0-w 1*(radius w)⁻¹*q 1)^2+
      (w 1*(radius w)⁻¹*q 0+w 0*(radius w)⁻¹*q 1)^2+q 2^2 =
      q 0^2+q 1^2+q 2^2
    calc
      _ = (w 0^2+w 1^2)*(radius w)⁻¹^2*(q 0^2+q 1^2)+q 2^2 := by ring
      _ = _ := by rw [← radius_sq]; field_simp
  rw [← GNC.enorm_sq,← GNC.enorm_sq] at he
  nlinarith [GNC.enorm_nonneg (polynomialFrame (lift w) *ᵥ q),GNC.enorm_nonneg q]

theorem center_continuous (r : Flow) : Continuous (center r) := by
  have hw := r.hw.comp clamp_continuous
  apply continuous_pi
  intro i
  fin_cases i <;> simp [center,position,Matrix.cons_val_two] <;> fun_prop

theorem center_lower (r : Flow) (t : ℝ) : (79/100:ℝ) ≤ GNC.enorm (center r t) := by
  have h := Reference.physical_solar_annulus r.w r.hw r.hdw r.hiw
    (clampTime t) (clamp_mem t)
  change _ ≤ GNC.enorm (position _)
  rw [position_norm]
  linarith [h.1]

theorem thrust_continuous (r : Flow) : Continuous (thrust r) := by
  have hz := lift_continuous (r.hw.comp clamp_continuous) (fun t => r.hr (clampTime t))
  exact ((frame_continuous _ hz).matrix_mulVec continuous_const).const_smul
    (PolynomialTransition.alpha:ℝ)

theorem thrust_bound (r : Flow) (t : ℝ) : ‖thrust r t‖ ≤ (1/2500:ℝ) := by
  apply (pi_norm_le_enorm _).trans
  change GNC.enorm (PlanarChaserError.referenceThrust _ _) ≤ _
  rw [Reference.thrust_tangent,GNC.enorm_smul]
  have hα : 0 ≤ (PolynomialTransition.alpha:ℝ) := by norm_num [PolynomialTransition.alpha]
  rw [abs_of_nonneg hα]
  have h := mul_le_mul_of_nonneg_left (Reference.tangent_bound (r.w (clampTime t))) hα
  norm_num [PolynomialTransition.alpha] at h ⊢
  linarith

def nodes (k : ℕ) : ℝ := BurnSchedule.time (min k 37)

theorem nodes_eq (k : ℕ) (hk : k ≤ 37) : nodes k = (BurnSchedule.time k:ℝ) := by
  simp only [nodes,Nat.min_eq_left hk]

theorem nodes_zero : nodes 0 = 0 := by norm_num [nodes,BurnSchedule.time_zero]
theorem nodes_final : nodes 37 = (3/5:ℝ) := by norm_num [nodes,BurnSchedule.time_final]

theorem nodes_monotone : Monotone nodes := by
  apply monotone_nat_of_le_succ
  intro k
  by_cases hk : k < 37
  · rw [nodes_eq k (by omega),nodes_eq (k+1) (by omega)]
    exact BurnSchedule.order k hk
  · simp only [nodes,Nat.min_eq_right (show 37 ≤ k by omega),
      Nat.min_eq_right (show 37 ≤ k+1 by omega),le_refl]

def acceleration (r : Flow) (commands : Fin 18 → Vec3) (k : ℕ) (t : ℝ) : Vec3 :=
  BurnSchedule.input (fun j t => ChaserResponse.acceleration
    (RetainedPrefix.beta:ℝ) (lift (r.w t)) (commands j)) k t

theorem acceleration_continuous (r : Flow) (commands : Fin 18 → Vec3) (k : ℕ) :
    Continuous (acceleration r commands k) := by
  change Continuous (BurnSchedule.input (fun j t => ChaserResponse.acceleration
    (RetainedPrefix.beta:ℝ) (lift (r.w t)) (commands j)) k)
  apply BurnSchedule.input_continuous
  intro j
  exact ((frame_continuous _ (lift_continuous r.hw r.hr)).matrix_mulVec
    continuous_const).const_smul (RetainedPrefix.beta:ℝ)

theorem acceleration_bound (r : Flow) (commands : Fin 18 → Vec3)
    (hcommands : ∀ j, GNC.enorm (commands j) ≤ 1) (k : ℕ) (t : ℝ) :
    ‖acceleration r commands k t‖ ≤ (49/2500:ℝ) := by
  unfold acceleration BurnSchedule.input
  split_ifs with hk
  · apply (pi_norm_le_enorm _).trans
    change GNC.enorm ((RetainedPrefix.beta:ℝ) •
      (polynomialFrame (lift (r.w t)) *ᵥ commands ⟨k/2,by omega⟩)) ≤ _
    rw [GNC.enorm_smul,frame_enorm _ (r.hr t)]
    have hβ : 0 ≤ (RetainedPrefix.beta:ℝ) := by
      norm_num [RetainedPrefix.beta,BurnSensitivity.burnScale,FreeResponse.lengthUnit]
    rw [abs_of_nonneg hβ]
    have h := mul_le_mul_of_nonneg_left (hcommands ⟨k/2,by omega⟩) hβ
    norm_num [RetainedPrefix.beta,BurnSensitivity.burnScale,FreeResponse.lengthUnit] at h ⊢
    linarith
  · norm_num

theorem shared_commands_bound (q : Vec3)
    (hq : q ∈ ThrustSupport.Cap SharedBiasExample.axis SharedBiasCertificates.Solar.kappa) :
    ∀ j, GNC.enorm (RetainedPhysical.commands q j) ≤ 1 := by
  intro j
  rw [RetainedPhysical.commands,GNC.enorm_smul,GNC.rotate_enorm,
    ThrustSupport.unit_enorm q hq.1,mul_one,
    abs_of_nonneg (SharedBiasCertificates.Solar.in_box j).1]
  exact (SharedBiasCertificates.Solar.in_box j).2

end GNC.Applications.OrbitalFuel.ChaserReferenceData
