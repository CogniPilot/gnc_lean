import GNC.Applications.OrbitalFuel.RetainedOverlay
import GNC.Applications.OrbitalFuel.RetainedCombination

/-! Exact identities connecting the accumulated forcing to the eighteen
physical burn commands and continuous reference thrust at any query time.
The same body-pointing vector is used on every burn.
-/
noncomputable section
namespace GNC.Applications.OrbitalFuel.RetainedPhysical
open GNC PolynomialOrbitTransition PolynomialBurn RetainedPrefix Matrix
set_option autoImplicit false

def commands (q : Vec3) (j : Fin 18) : Vec3 :=
  SharedBiasCertificates.Solar.x j • rotate (SharedBiasGeometry.cycleRotation j) q

theorem coordinate_integral {m : ℕ} (f : ℝ → Fin m → ℝ) (hf : Continuous f)
    (a b : ℝ) (i : Fin m) :
    (∫ t in a..b, f t) i = ∫ t in a..b, f t i :=
  ((ContinuousLinearMap.proj (R := ℝ) i).intervalIntegral_comp_comm
    (hf.intervalIntegrable (μ := MeasureTheory.volume) a b)).symm

theorem burn_sum {m : ℕ} (u : Fin 18 → ℝ → Fin m → ℝ) (T : ℝ) :
    (∑ a : Fin 37, ∫ t in min (BurnSchedule.time a.val:ℝ) T..
      min (BurnSchedule.time (a.val+1):ℝ) T, BurnSchedule.input u a.val t) =
      ∑ j : Fin 18, ∫ t in min (burnStart j:ℝ) T..min (burnFinish j:ℝ) T, u j t := by
  simpa only [one_mulVec,Finset.sum_range] using
    BurnPrefix.burn_integrals (fun _ => (1 : Matrix (Fin m) (Fin m) ℝ)) u T

theorem common_sum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : ℝ → E) (hv : Continuous v) {T : ℝ} (hT : T ∈ Set.Icc (0:ℝ) (3/5)) :
    (∑ a : Fin 37, ∫ t in min (BurnSchedule.time a.val:ℝ) T..
      min (BurnSchedule.time (a.val+1):ℝ) T, v t) = ∫ t in (0:ℝ)..T, v t := by
  have h := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun k => min (BurnSchedule.time k:ℝ) T) (n := 37)
    (fun k _ => hv.intervalIntegrable (μ := MeasureTheory.volume) _ _)
  simpa only [Finset.sum_range,BurnSchedule.time_zero,BurnSchedule.time_final,
    Rat.cast_zero,Rat.cast_div,Rat.cast_ofNat,min_eq_left hT.1,min_eq_right hT.2] using h

theorem arc_sum_add {m : ℕ} (u : Fin 18 → ℝ → Fin m → ℝ) (v : ℝ → Fin m → ℝ)
    (hu : ∀ j, Continuous (u j)) (hv : Continuous v)
    {T : ℝ} (hT : T ∈ Set.Icc (0:ℝ) (3/5)) :
    (∑ a : Fin 37, ∫ t in min (BurnSchedule.time a.val:ℝ) T..
      min (BurnSchedule.time (a.val+1):ℝ) T, BurnSchedule.input u a.val t+v t) =
      (∑ j : Fin 18, ∫ t in min (burnStart j:ℝ) T..min (burnFinish j:ℝ) T, u j t)+
        ∫ t in (0:ℝ)..T, v t := by
  calc
    _ = ∑ a : Fin 37,
        ((∫ t in min (BurnSchedule.time a.val:ℝ) T..min (BurnSchedule.time (a.val+1):ℝ) T,
          BurnSchedule.input u a.val t)+
        ∫ t in min (BurnSchedule.time a.val:ℝ) T..min (BurnSchedule.time (a.val+1):ℝ) T, v t) := by
      apply Finset.sum_congr rfl
      intro a _
      exact intervalIntegral.integral_add
        ((BurnSchedule.input_continuous hu a.val).intervalIntegrable _ _)
        (hv.intervalIntegrable _ _)
    _ = _ := by rw [Finset.sum_add_distrib,burn_sum,common_sum v hv hT]

theorem plane_schedule (z : ℝ → Fin 5 → ℝ) (F : ℝ → Matrix (Fin 4) (Fin 4) ℝ)
    (q : Vec3) (a : Fin 37) (t : ℝ) :
    planeInverse (F t) *ᵥ ChaserResponse.planeBurn (beta:ℝ) (z t) (command a q) =
      BurnSchedule.input (fun j t => planeInverse (F t) *ᵥ
        ChaserResponse.planeBurn (beta:ℝ) (z t) (commands q j)) a.val t := by
  rw [command_schedule a q t]
  by_cases h : a.val < 37 ∧ a.val%2 = 1
  · simp only [BurnSchedule.input,dif_pos h,commands]
  · simp only [BurnSchedule.input,dif_neg h]
    simp [ChaserResponse.planeBurn,show (![0,0] : Fin 2 → ℝ) = 0 by ext i; fin_cases i <;> rfl]

theorem normal_schedule (H : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (q : Vec3) (a : Fin 37) (t : ℝ) :
    normalInverse (H t) *ᵥ ChaserResponse.normalBurn (beta:ℝ) (command a q) =
      BurnSchedule.input (fun j t => normalInverse (H t) *ᵥ
        ChaserResponse.normalBurn (beta:ℝ) (commands q j)) a.val t := by
  rw [command_schedule a q t]
  by_cases h : a.val < 37 ∧ a.val%2 = 1
  · simp only [BurnSchedule.input,dif_pos h,commands]
  · simp only [BurnSchedule.input,dif_neg h]
    simp [ChaserResponse.normalBurn,show (![0,0] : Fin 2 → ℝ) = 0 by ext i; fin_cases i <;> rfl]

def pulled (x : Trajectory) (n : Fin 68) (T : ℝ) (q : Vec3) : Fin 6 → ℝ :=
  fun i => combine (fun k => ValidatedRetainedPrefix.accumulated x n.val T i k) q

theorem pulled_arcs (x : Trajectory) (n : Fin 68) {T : ℝ}
    (ht : T ∈ Set.Icc ((RetainedNormData.pieces n).start:ℝ)
      ((RetainedNormData.pieces n).finish:ℝ)) (q : Vec3) (i : Fin 6) :
    pulled x n T q i = (RetainedPrefixData.initial i:ℝ)+
      ∑ a : Fin 37, ∫ t in min (BurnSchedule.time a.val:ℝ) T..
        min (BurnSchedule.time (a.val+1):ℝ) T,
          combine (fun k => (forcing a i k).value (x.state t)) q := by
  have he : (fun k => ValidatedRetainedPrefix.accumulated x n.val T i k) =
      (fun k => ValidatedRetainedPrefix.initial i k)+
        ∑ a : Fin 37, (fun k => ∫ t in min (BurnSchedule.time a.val:ℝ) T..
          min (BurnSchedule.time (a.val+1):ℝ) T, (forcing a i k).value (x.state t)) := by
    ext k
    simpa only [Pi.add_apply,Finset.sum_apply] using RetainedOverlay.accumulated_arcs x n ht i k
  rw [pulled,he,combine_add,combine_sum]
  have hi : combine (fun k => ValidatedRetainedPrefix.initial i k) q =
      (RetainedPrefixData.initial i:ℝ) := by simp [combine,ValidatedRetainedPrefix.initial]
  rw [hi]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  exact combine_integral _ (continuous_pi (fun k => (forcing a i k).value_continuous x.continuous)) q _ _

theorem pulled_coordinates {m : ℕ} (x : Trajectory) (n : Fin 68) {T : ℝ}
    (ht : T ∈ Set.Icc ((RetainedNormData.pieces n).start:ℝ)
      ((RetainedNormData.pieces n).finish:ℝ)) (q : Vec3) (indices : Fin m → Fin 6)
    (v : Fin 37 → ℝ → Fin m → ℝ) (hv : ∀ a, Continuous (v a))
    (he : ∀ a t i, combine (fun k => (forcing a (indices i) k).value (x.state t)) q = v a t i) :
    (fun i => pulled x n T q (indices i)) =
      (fun i => (RetainedPrefixData.initial (indices i):ℝ))+
        ∑ a : Fin 37, ∫ t in min (BurnSchedule.time a.val:ℝ) T..
          min (BurnSchedule.time (a.val+1):ℝ) T, v a t := by
  ext i
  simp only [Pi.add_apply,Finset.sum_apply]
  rw [pulled_arcs x n ht q]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [coordinate_integral _ (hv a)]
  exact intervalIntegral.integral_congr (fun t _ => he a t i)

end GNC.Applications.OrbitalFuel.RetainedPhysical
