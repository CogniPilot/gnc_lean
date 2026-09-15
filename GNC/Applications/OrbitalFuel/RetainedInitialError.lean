import GNC.Applications.OrbitalFuel.RetainedResponseIdentity
import GNC.Applications.OrbitalFuel.ValidatedTerminalData

/-! Charge the exact initial orbital-speed square root in the all-time
retained response. The forward-entry bound comes from the already checked
joint reference/transition ODE cells, not a sampled matrix norm.
-/
noncomputable section
namespace GNC.Applications.OrbitalFuel.RetainedPhysical
open GNC PolynomialOrbitTransition PolynomialBurn RetainedPrefix Matrix
open GNC.PolynomialODE GNC.PolynomialBounds PolynomialTransition
set_option autoImplicit false

def retained (z : ℝ → Fin 5 → ℝ) (F : ℝ → Matrix (Fin 4) (Fin 4) ℝ)
    (H : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (initialSpeed : ℝ) (q : Vec3) (T : ℝ)
    (j : Fin 2) : Vec3 := fun i =>
  cartesian
    (ChaserPrefix.retainedPlane (alpha:ℝ) (beta:ℝ) z F
      (TerminalResponse.initialPlane initialSpeed) (commands q) T)
    (ChaserPrefix.retainedNormal (beta:ℝ) H TerminalResponse.initialNormal (commands q) T)
    ⟨3*j.val+i.val,by omega⟩

theorem state_transition_bound (x : Trajectory) (n : Fin 68) {t : ℝ}
    (ht : t ∈ Set.Icc ((RetainedNormData.pieces n).start:ℝ)
      ((RetainedNormData.pieces n).finish:ℝ)) (s : Fin 25) (hs : 5 ≤ s.val) :
    |x.state t s| ≤ 4 := by
  let p := RetainedNormData.pieces n
  have hp := RetainedNormData.valid n
  have hu := p.reference_interval hp ht
  have hx (i : Fin 25) :
      |x.state t i-curve (steps p.referenceStep).coefficients (t-(p.offset:ℝ)) i| ≤
        ((steps p.referenceStep).error i:ℝ) := by
    have h := (x.cell_error p.referenceStep hu i).le
    have he : (p.referenceStep.val:ℝ)*(3/160)+(t-(p.offset:ℝ)) = t := by
      simp only [RetainedNorm.Piece.offset,Rat.cast_mul,Rat.cast_natCast,Rat.cast_div,Rat.cast_ofNat]
      ring
    simpa only [he] using h
  have hu' : t-(p.offset:ℝ) ∈ Set.Icc (0:ℝ) ((steps p.referenceStep).duration:ℝ) := by
    simpa only [durations,Rat.cast_div,Rat.cast_ofNat] using hu
  have h := (steps p.referenceStep).actual_box (steps_valid p.referenceStep) hu' (x.state t) hx s
  exact h.trans (by exact_mod_cast transition_regions p.referenceStep s hs)

theorem plane_transition_bound (x : Trajectory) (z : ℝ → Fin 5 → ℝ)
    (F : ℝ → Matrix (Fin 4) (Fin 4) ℝ) (H : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hstate : ∀ t, x.state t = pack (z t) (F t) (H t)) (n : Fin 68) {t : ℝ}
    (ht : t ∈ Set.Icc ((RetainedNormData.pieces n).start:ℝ)
      ((RetainedNormData.pieces n).finish:ℝ)) (i j : Fin 4) : |F t i j| ≤ 4 := by
  have h := state_transition_bound x n ht (planeIndex i j) (by dsimp only [planeIndex]; omega)
  simpa only [hstate t,pack_plane] using h

theorem plane_initial_difference (z : ℝ → Fin 5 → ℝ)
    (F : ℝ → Matrix (Fin 4) (Fin 4) ℝ) (q : Vec3) (T s c : ℝ) (i : Fin 4) :
    ChaserPrefix.retainedPlane (alpha:ℝ) (beta:ℝ) z F
        (TerminalResponse.initialPlane s) (commands q) T i-
      ChaserPrefix.retainedPlane (alpha:ℝ) (beta:ℝ) z F
        (TerminalResponse.initialPlane c) (commands q) T i =
      F T i 2*(12500000/(FreeResponse.lengthUnit:ℝ))*(s-c) := by
  have he : ChaserPrefix.retainedPlane (alpha:ℝ) (beta:ℝ) z F
        (TerminalResponse.initialPlane s) (commands q) T-
      ChaserPrefix.retainedPlane (alpha:ℝ) (beta:ℝ) z F
        (TerminalResponse.initialPlane c) (commands q) T =
      F T *ᵥ (TerminalResponse.initialPlane s-TerminalResponse.initialPlane c) := by
    simp only [ChaserPrefix.retainedPlane,mulVec_add,mulVec_sub]
    abel
  have hi := congrFun he i
  simp only [Pi.sub_apply] at hi
  rw [hi]
  simp [TerminalResponse.initialPlane,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.succ]
  ring

theorem initial_error (z : ℝ → Fin 5 → ℝ) (F : ℝ → Matrix (Fin 4) (Fin 4) ℝ)
    (H : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (q : Vec3) (T : ℝ)
    (hF : ∀ i, |F T i 2| ≤ 4) (j : Fin 2) :
    GNC.enorm (retained z F H (Real.sqrt (3/2:ℝ)) q T j-
      retained z F H (TerminalData.initialSpeedCenter:ℝ) q T j) ≤ 1/10^20 := by
  have hp (i : Fin 4) :
      |ChaserPrefix.retainedPlane (alpha:ℝ) (beta:ℝ) z F
          (TerminalResponse.initialPlane (Real.sqrt (3/2:ℝ))) (commands q) T i-
        ChaserPrefix.retainedPlane (alpha:ℝ) (beta:ℝ) z F
          (TerminalResponse.initialPlane (TerminalData.initialSpeedCenter:ℝ)) (commands q) T i| ≤
        4/10^25 := by
    rw [plane_initial_difference,abs_mul,abs_mul]
    have hc : |12500000/(FreeResponse.lengthUnit:ℝ)| ≤ 1 := by norm_num [FreeResponse.lengthUnit]
    have h := mul_le_mul (mul_le_mul (hF i) hc (abs_nonneg _) (by norm_num))
      TerminalData.initialSpeed_enclosure (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 4*1)
    simpa only [mul_one,mul_one_div] using h
  have hc (k : Fin 6) :
      |cartesian
        (ChaserPrefix.retainedPlane (alpha:ℝ) (beta:ℝ) z F
          (TerminalResponse.initialPlane (Real.sqrt (3/2:ℝ))) (commands q) T)
        (ChaserPrefix.retainedNormal (beta:ℝ) H TerminalResponse.initialNormal (commands q) T) k-
      cartesian
        (ChaserPrefix.retainedPlane (alpha:ℝ) (beta:ℝ) z F
          (TerminalResponse.initialPlane (TerminalData.initialSpeedCenter:ℝ)) (commands q) T)
        (ChaserPrefix.retainedNormal (beta:ℝ) H TerminalResponse.initialNormal (commands q) T) k| ≤ 4/10^25 := by
    fin_cases k
    · exact hp 0
    · exact hp 1
    · norm_num [cartesian]
    · exact hp 2
    · exact hp 3
    · norm_num [cartesian]
  apply enorm_le_of_component_bounds _ (fun _ => (4/10^25:ℝ))
  · intro i
    exact hc ⟨3*j.val+i.val,by omega⟩
  · norm_num
  · norm_num [Fin.sum_univ_succ]

end GNC.Applications.OrbitalFuel.RetainedPhysical
