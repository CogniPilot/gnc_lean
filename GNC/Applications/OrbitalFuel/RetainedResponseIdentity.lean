import GNC.Applications.OrbitalFuel.RetainedPhysicalIntegrals
import GNC.Applications.OrbitalFuel.ValidatedRetainedResponse
import GNC.Applications.OrbitalFuel.TerminalResponse

/-! The certified accumulated response is the retained physical burn/coast
response with the stored rational initial-speed center. This is an exact
identity, before charging the initial square-root error and gravity remainder.
-/
noncomputable section
namespace GNC.Applications.OrbitalFuel.RetainedPhysical
open GNC PolynomialOrbitTransition PolynomialBurn RetainedPrefix Matrix
set_option autoImplicit false

theorem planeRows_apply (y : Fin 6 → ℝ) (i : Fin 4) :
    planeRows y i = y ⟨i.val,by omega⟩ := by fin_cases i <;> rfl

theorem normalRows_apply (y : Fin 6 → ℝ) (i : Fin 2) :
    normalRows y i = y ⟨4+i.val,by omega⟩ := by fin_cases i <;> rfl

theorem initial_plane : (fun i : Fin 4 => (RetainedPrefixData.initial ⟨i.val,by omega⟩:ℝ)) =
    TerminalResponse.initialPlane (TerminalData.initialSpeedCenter:ℝ) := by
  ext i
  fin_cases i <;> norm_num [RetainedPrefixData.initial,TerminalResponse.initialPlane,
    TerminalData.initialSpeedCenter,FreeResponse.lengthUnit,Matrix.cons_val_two,Matrix.cons_val_three]

theorem initial_normal : (fun i : Fin 2 => (RetainedPrefixData.initial ⟨4+i.val,by omega⟩:ℝ)) =
    TerminalResponse.initialNormal := by
  ext i
  fin_cases i <;> norm_num [RetainedPrefixData.initial,TerminalResponse.initialNormal,
    FreeResponse.lengthUnit,Matrix.cons_val_four]

theorem pulled_plane (x : Trajectory) (z : ℝ → Fin 5 → ℝ)
    (F : ℝ → Matrix (Fin 4) (Fin 4) ℝ) (H : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hz : Continuous z) (hF : Continuous F)
    (hstate : ∀ t, x.state t = pack (z t) (F t) (H t)) (n : Fin 68) {T : ℝ}
    (hT : T ∈ Set.Icc (0:ℝ) (3/5))
    (ht : T ∈ Set.Icc ((RetainedNormData.pieces n).start:ℝ)
      ((RetainedNormData.pieces n).finish:ℝ)) (q : Vec3) :
    planeRows (pulled x n T q) = TerminalResponse.initialPlane (TerminalData.initialSpeedCenter:ℝ)+
      (∑ j : Fin 18, ∫ t in min (burnStart j:ℝ) T..min (burnFinish j:ℝ) T,
        planeInverse (F t) *ᵥ ChaserResponse.planeBurn (beta:ℝ) (z t) (commands q j))+
      ∫ t in (0:ℝ)..T, planeInverse (F t) *ᵥ TargetThrust.forcing (PolynomialTransition.alpha:ℝ) (z t) := by
  let u := fun j t => planeInverse (F t) *ᵥ ChaserResponse.planeBurn (beta:ℝ) (z t) (commands q j)
  let v := fun t => planeInverse (F t) *ᵥ TargetThrust.forcing (PolynomialTransition.alpha:ℝ) (z t)
  have hK : Continuous (fun t => planeInverse (F t)) :=
    (continuous_const.matrix_mul hF.matrix_transpose).matrix_mul continuous_const
  have hu (j : Fin 18) : Continuous (u j) := hK.matrix_mulVec
    (ChaserResponse.planeBurn_continuous (beta:ℝ) (commands q j) hz)
  have hv : Continuous v := hK.matrix_mulVec (TargetThrust.forcing_continuous _ hz)
  have he := pulled_coordinates x n ht q (fun i : Fin 4 => ⟨i.val,by omega⟩)
    (fun a t => BurnSchedule.input u a.val t+v t)
    (fun a => (BurnSchedule.input_continuous hu a.val).add hv) (by
      intro a t i
      rw [hstate t,plane_combination,plane_schedule]
      exact add_comm _ _)
  rw [initial_plane,arc_sum_add u v hu hv hT] at he
  simpa only [← planeRows_apply,add_assoc] using he

theorem pulled_normal (x : Trajectory) (z : ℝ → Fin 5 → ℝ)
    (F : ℝ → Matrix (Fin 4) (Fin 4) ℝ) (H : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hH : Continuous H)
    (hstate : ∀ t, x.state t = pack (z t) (F t) (H t)) (n : Fin 68) {T : ℝ}
    (ht : T ∈ Set.Icc ((RetainedNormData.pieces n).start:ℝ)
      ((RetainedNormData.pieces n).finish:ℝ)) (q : Vec3) :
    normalRows (pulled x n T q) = TerminalResponse.initialNormal+
      ∑ j : Fin 18, ∫ t in min (burnStart j:ℝ) T..min (burnFinish j:ℝ) T,
        normalInverse (H t) *ᵥ ChaserResponse.normalBurn (beta:ℝ) (commands q j) := by
  let u := fun j t => normalInverse (H t) *ᵥ ChaserResponse.normalBurn (beta:ℝ) (commands q j)
  have hK : Continuous (fun t => normalInverse (H t)) :=
    (continuous_const.matrix_mul hH.matrix_transpose).matrix_mul continuous_const
  have hu (j : Fin 18) : Continuous (u j) := hK.matrix_mulVec continuous_const
  have he := pulled_coordinates x n ht q (fun i : Fin 2 => ⟨4+i.val,by omega⟩)
    (fun a t => BurnSchedule.input u a.val t)
    (fun a => BurnSchedule.input_continuous hu a.val) (by
      intro a t i
      rw [hstate t,normal_combination,normal_schedule])
  rw [initial_normal,burn_sum u T] at he
  simpa only [← normalRows_apply] using he

/-- Exact retained response, in Cartesian position/velocity row order. -/
theorem response_identity (x : Trajectory) (z : ℝ → Fin 5 → ℝ)
    (F : ℝ → Matrix (Fin 4) (Fin 4) ℝ) (H : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hz : Continuous z) (hF : Continuous F) (hH : Continuous H)
    (hstate : ∀ t, x.state t = pack (z t) (F t) (H t)) (n : Fin 68) {T : ℝ}
    (hT : T ∈ Set.Icc (0:ℝ) (3/5))
    (ht : T ∈ Set.Icc ((RetainedNormData.pieces n).start:ℝ)
      ((RetainedNormData.pieces n).finish:ℝ)) (q : Vec3) (j : Fin 2) (i : Fin 3) :
    ValidatedRetainedResponse.response x n T q j i =
      cartesian
        (ChaserPrefix.retainedPlane (PolynomialTransition.alpha:ℝ) (beta:ℝ) z F
          (TerminalResponse.initialPlane (TerminalData.initialSpeedCenter:ℝ)) (commands q) T)
        (ChaserPrefix.retainedNormal (beta:ℝ) H TerminalResponse.initialNormal (commands q) T)
        ⟨3*j.val+i.val,by omega⟩ := by
  change combine (fun k => (matrixValue (x.state T) *ᵥ
    (fun r => ValidatedRetainedPrefix.accumulated x n.val T r k)) ⟨3*j.val+i.val,by omega⟩) q = _
  rw [combine_forward]
  change (matrixValue (x.state T) *ᵥ pulled x n T q) _ = _
  rw [hstate T,matrixValue_packed,pulled_plane x z F H hz hF hstate n hT ht q,
    pulled_normal x z F H hH hstate n ht q]
  rfl

end GNC.Applications.OrbitalFuel.RetainedPhysical
