import GNC.Applications.OrbitalFuel.TargetThrustFormula
import GNC.Applications.OrbitalFuel.BurnTheory
import GNC.Analysis.SymplecticResponse

/-! Continuous enclosure for the whole-horizon target-thrust pullback. Each
polynomial cell uses the existing joint reference/transition ODE certificate.
-/
noncomputable section
open Matrix
namespace GNC.Applications.OrbitalFuel.TargetThrust
open GNC.PolynomialODE GNC.PolynomialOrbitTransition PolynomialBurn

theorem tangentSlot_correct (i : Fin 4) :
    observable (tangentSlot i) = planeObservable i 1 := by
  fin_cases i <;> rfl

theorem integral_error (x : Trajectory) (i : Fin 4) :
    |(∫ t in (0:ℝ)..(3/5), (observable (tangentSlot i)).value (x.state t))-
      (integralSum i:ℝ)| ≤ (3/5)*(1/10^14) := by
  let values : ℕ → ℝ := fun k =>
    if hk : k < 32 then (cellIntegral (fullCell ⟨k,hk⟩) (tangentSlot i):ℝ) else 0
  have h := GNC.IntegralPartition.uniform_error
    (fun t => (observable (tangentSlot i)).value (x.state t))
    (fun k => (k:ℝ)*(3/160)) values 32 (1/10^14)
    (fun k _ => ((observable (tangentSlot i)).value_continuous x.continuous).intervalIntegrable _ _)
    (fun k hk => by
      have hc := x.cell_integral (fullCell ⟨k,hk⟩) (fullCell_valid ⟨k,hk⟩) (tangentSlot i)
      have hs : ((fullCell ⟨k,hk⟩).start:ℝ) = (k:ℝ)*(3/160) := by
        simp [fullCell, Cell.start]
      have hf : ((fullCell ⟨k,hk⟩).finish:ℝ) = ((k+1:ℕ):ℝ)*(3/160) := by
        simp [fullCell, Cell.finish]
        ring
      rw [hs,hf] at hc
      have hlen : (((k+1:ℕ):ℝ)*(3/160)-(k:ℝ)*(3/160)) = 3/160 := by
        push_cast
        ring
      simpa only [values, dif_pos hk, hlen, fullCell, Rat.cast_mul, Rat.cast_sub,
        Rat.cast_div, Rat.cast_zero, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat, sub_zero] using hc)
  have hv : (∑ k ∈ Finset.range 32, values k) = (integralSum i:ℝ) := by
    rw [Finset.sum_range]
    simp only [integralSum, Rat.cast_sum]
    apply Finset.sum_congr rfl
    intro k _
    simp only [values, dif_pos k.isLt]
  rw [hv] at h
  norm_num at h ⊢
  exact h

/-- The chaser's retained gravity equation is forced by minus the target's
prescribed acceleration. No derivative of that prescribed reference input
is inserted into the gravity variational generator. -/
def forcing (α : ℝ) (z : Fin 5 → ℝ) : Fin 4 → ℝ :=
  fun i => -α*planeInjection z i 1

theorem forcing_continuous (α : ℝ) {z : ℝ → Fin 5 → ℝ} (hz : Continuous z) :
    Continuous (fun t => forcing α (z t)) := by
  apply continuous_pi
  intro i
  fin_cases i <;> simp [forcing, planeInjection, Matrix.cons_val_two] <;> fun_prop

theorem forcing_pairing (α : ℝ) (z : Fin 5 → ℝ) (F : Matrix (Fin 4) (Fin 4) ℝ)
    (i : Fin 4) :
    (planeInverse F *ᵥ forcing α z) i = -α*(planeInverse F * planeInjection z) i 1 := by
  simp only [Matrix.mulVec, dotProduct, forcing, Matrix.mul_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Actual forced linear relative motion, with its complete target-thrust
free response. A separate residual is still needed for the nonlinear chaser.
-/
theorem free_response (α : ℝ) (z : ℝ → Fin 5 → ℝ)
    (F : ℝ → Matrix (Fin 4) (Fin 4) ℝ) (x : ℝ → Fin 4 → ℝ)
    (hz : Continuous z) (hF : Continuous F)
    (hdF : ∀ t ∈ Set.Icc (0:ℝ) (3/5), HasDerivAt F (planeGenerator (z t)*F t) t)
    (hiF : F 0 = 1)
    (hdx : ∀ t ∈ Set.Icc (0:ℝ) (3/5),
      HasDerivAt x (planeGenerator (z t) *ᵥ x t+forcing α (z t)) t) :
    x (3/5) = F (3/5) *ᵥ (fun i => x 0 i-
      α*(∫ t in (0:ℝ)..(3/5), ((F t)⁻¹ * planeInjection (z t)) i 1)) := by
  have hp : Continuous (fun t => GNC.SymplecticResponse.pullback planeForm (F t)) :=
    (continuous_const.matrix_mul hF.matrix_transpose).matrix_mul continuous_const
  have hi : IntervalIntegrable
      (fun t => GNC.SymplecticResponse.pullback planeForm (F t) *ᵥ forcing α (z t))
      MeasureTheory.volume 0 (3/5) :=
    (hp.matrix_mulVec (forcing_continuous α hz)).intervalIntegrable (0:ℝ) (3/5)
  have h := GNC.SymplecticResponse.endpoint F (fun t => planeGenerator (z t)) planeForm
    x (fun t => forcing α (z t)) (by norm_num) planeForm_sq hdF
    (fun t _ => plane_hamiltonian (z t)) hiF hdx hi
  have he (i : Fin 4) :
      (∫ t in (0:ℝ)..(3/5), GNC.SymplecticResponse.pullback planeForm (F t) *ᵥ forcing α (z t)) i =
      -α*(∫ t in (0:ℝ)..(3/5), ((F t)⁻¹ * planeInjection (z t)) i 1) := by
    have hc := (ContinuousLinearMap.proj (R := ℝ) i).intervalIntegral_comp_comm hi
    change (∫ t in (0:ℝ)..(3/5), (planeInverse (F t) *ᵥ forcing α (z t)) i) =
      (∫ t in (0:ℝ)..(3/5), GNC.SymplecticResponse.pullback planeForm (F t) *ᵥ forcing α (z t)) i at hc
    rw [← hc]
    simp_rw [forcing_pairing]
    rw [intervalIntegral.integral_const_mul]
    congr 1
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [plane_inverse z F hdF hiF t (by norm_num [Set.uIcc_of_le] at ht ⊢; exact ht)]
  rw [h]
  congr 1
  funext i
  simp only [Pi.add_apply, he, sub_eq_add_neg, neg_mul]

theorem normal_free_response (z : ℝ → Fin 5 → ℝ)
    (H : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (x : ℝ → Fin 2 → ℝ)
    (hdH : ∀ t ∈ Set.Icc (0:ℝ) (3/5), HasDerivAt H (normalGenerator (z t)*H t) t)
    (hiH : H 0 = 1)
    (hdx : ∀ t ∈ Set.Icc (0:ℝ) (3/5), HasDerivAt x (normalGenerator (z t) *ᵥ x t) t) :
    x (3/5) = H (3/5) *ᵥ x 0 := by
  have h := GNC.SymplecticResponse.endpoint H (fun t => normalGenerator (z t)) normalForm
    x (fun _ => 0) (by norm_num) normalForm_sq hdH (fun t _ => normal_hamiltonian (z t)) hiH
    (fun t ht => by simpa only [add_zero] using hdx t ht) (by simp)
  simpa only [Matrix.mulVec_zero, intervalIntegral.integral_zero, add_zero] using h

end GNC.Applications.OrbitalFuel.TargetThrust
