import GNC.Applications.OrbitalFuel.ChaserResponse
import GNC.Applications.OrbitalFuel.BurnSensitivityInputs

/-! The switched chaser response uses exactly the continuous burn means
whose enclosures enter the certified solar coefficient matrix. Integrating
a command constant in reference RTN coordinates gives the mean times the
command, with the normalized burn duration 1/50 accounted for exactly.
-/
noncomputable section
open Matrix
namespace GNC.Applications.OrbitalFuel.BurnMeanResponse
open GNC PolynomialOrbitTransition ChaserResponse

theorem burn_horizon (j : Fin 18) {t : ℝ}
    (ht : t ∈ Set.uIcc (PolynomialBurn.burnStart j:ℝ) (PolynomialBurn.burnFinish j:ℝ)) :
    t ∈ Set.Icc (0:ℝ) (3/5) := by
  have hk : 2*j.val+1 < 37 := by omega
  have he : 2*j.val+1+1 = 2*j.val+2 := by omega
  have ho := BurnSchedule.order (2*j.val+1) hk
  have hh := BurnSchedule.horizon (2*j.val+1) hk
  rw [he, BurnSchedule.burn_start, BurnSchedule.burn_finish] at ho hh
  rw [Set.uIcc_of_le ho] at ht
  exact ⟨hh.1.trans ht.1, ht.2.trans hh.2⟩

def planeMean (z : ℝ → Fin 5 → ℝ) (F : ℝ → Matrix (Fin 4) (Fin 4) ℝ)
    (H : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (j : Fin 18) : Matrix (Fin 4) (Fin 2) ℝ :=
  Matrix.of (fun i k => BurnSensitivity.means z F H j ⟨2*i.val+k.val,by omega⟩)

def normalMean (z : ℝ → Fin 5 → ℝ) (F : ℝ → Matrix (Fin 4) (Fin 4) ℝ)
    (H : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (j : Fin 18) : Fin 2 → ℝ :=
  fun i => BurnSensitivity.means z F H j ⟨8+i.val,by omega⟩

theorem plane_mean (z : ℝ → Fin 5 → ℝ) (F : ℝ → Matrix (Fin 4) (Fin 4) ℝ)
    (H : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hdF : ∀ t ∈ Set.Icc (0:ℝ) (3/5), HasDerivAt F (planeGenerator (z t)*F t) t)
    (hiF : F 0 = 1) (j : Fin 18) (i : Fin 4) (k : Fin 2) :
    planeMean z F H j i k =
      50*(∫ t in (PolynomialBurn.burnStart j:ℝ)..(PolynomialBurn.burnFinish j:ℝ),
        (planeInverse (F t)*planeInjection (z t)) i k) := by
  have he : planeMean z F H j i k =
      50*(∫ t in (PolynomialBurn.burnStart j:ℝ)..(PolynomialBurn.burnFinish j:ℝ),
        ((F t)⁻¹*planeInjection (z t)) i k) := by
    fin_cases i <;> fin_cases k <;> simp [planeMean, BurnSensitivity.means]
  rw [he]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  rw [plane_inverse z F hdF hiF t (burn_horizon j ht)]

theorem normal_mean (z : ℝ → Fin 5 → ℝ) (F : ℝ → Matrix (Fin 4) (Fin 4) ℝ)
    (H : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hdH : ∀ t ∈ Set.Icc (0:ℝ) (3/5), HasDerivAt H (normalGenerator (z t)*H t) t)
    (hiH : H 0 = 1) (j : Fin 18) (i : Fin 2) :
    normalMean z F H j i =
      50*(∫ t in (PolynomialBurn.burnStart j:ℝ)..(PolynomialBurn.burnFinish j:ℝ),
        normalInverse (H t) i 1) := by
  have he : normalMean z F H j i =
      50*(∫ t in (PolynomialBurn.burnStart j:ℝ)..(PolynomialBurn.burnFinish j:ℝ), (H t)⁻¹ i 1) := by
    fin_cases i <;> simp [normalMean, BurnSensitivity.means]
  rw [he]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  rw [normal_inverse z H hdH hiH t (burn_horizon j ht)]

theorem plane_burn_integral (β : ℝ) (z : ℝ → Fin 5 → ℝ)
    (F : ℝ → Matrix (Fin 4) (Fin 4) ℝ) (H : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hz : Continuous z) (hF : Continuous F)
    (hdF : ∀ t ∈ Set.Icc (0:ℝ) (3/5), HasDerivAt F (planeGenerator (z t)*F t) t)
    (hiF : F 0 = 1) (j : Fin 18) (q : Vec3) :
    (∫ t in (PolynomialBurn.burnStart j:ℝ)..(PolynomialBurn.burnFinish j:ℝ),
      planeInverse (F t) *ᵥ planeBurn β (z t) q) =
        (β/50) • (planeMean z F H j *ᵥ ![q 0,q 1]) := by
  have hK : Continuous (fun t => planeInverse (F t)) :=
    (continuous_const.matrix_mul hF.matrix_transpose).matrix_mul continuous_const
  have hB : Continuous (fun t => planeInjection (z t)) := by
    apply continuous_matrix
    intro i k
    fin_cases i <;> fin_cases k <;>
      simp [planeInjection, Matrix.cons_val_two, Matrix.cons_val_three] <;> fun_prop
  have hKB := hK.matrix_mul hB
  have hint := (hK.matrix_mulVec (planeBurn_continuous β q hz)).intervalIntegrable
    (μ := MeasureTheory.volume) (PolynomialBurn.burnStart j:ℝ) (PolynomialBurn.burnFinish j:ℝ)
  ext i
  have hproj := (ContinuousLinearMap.proj (R := ℝ) i).intervalIntegral_comp_comm hint
  change (∫ t in (PolynomialBurn.burnStart j:ℝ)..(PolynomialBurn.burnFinish j:ℝ),
      (planeInverse (F t) *ᵥ planeBurn β (z t) q) i) =
    (∫ t in (PolynomialBurn.burnStart j:ℝ)..(PolynomialBurn.burnFinish j:ℝ),
      planeInverse (F t) *ᵥ planeBurn β (z t) q) i at hproj
  rw [← hproj]
  have he (t : ℝ) : (planeInverse (F t) *ᵥ planeBurn β (z t) q) i =
      β*((planeInverse (F t)*planeInjection (z t)) i 0*q 0+
        (planeInverse (F t)*planeInjection (z t)) i 1*q 1) := by
    simp only [planeBurn, mulVec_smul, Pi.smul_apply, smul_eq_mul, mulVec_mulVec]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
    (((hKB.matrix_elem i 0).mul_const (q 0)).intervalIntegrable _ _)
    (((hKB.matrix_elem i 1).mul_const (q 1)).intervalIntegrable _ _)]
  simp [intervalIntegral.integral_mul_const, Pi.smul_apply, smul_eq_mul,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Matrix.cons_val_zero]
  rw [plane_mean z F H hdF hiF j i 0, plane_mean z F H hdF hiF j i 1]
  ring

theorem normal_burn_integral (β : ℝ) (z : ℝ → Fin 5 → ℝ)
    (F : ℝ → Matrix (Fin 4) (Fin 4) ℝ) (H : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hH : Continuous H)
    (hdH : ∀ t ∈ Set.Icc (0:ℝ) (3/5), HasDerivAt H (normalGenerator (z t)*H t) t)
    (hiH : H 0 = 1) (j : Fin 18) (q : Vec3) :
    (∫ t in (PolynomialBurn.burnStart j:ℝ)..(PolynomialBurn.burnFinish j:ℝ),
      normalInverse (H t) *ᵥ normalBurn β q) =
        (β/50*q 2) • normalMean z F H j := by
  have hK : Continuous (fun t => normalInverse (H t)) :=
    (continuous_const.matrix_mul hH.matrix_transpose).matrix_mul continuous_const
  have hint := (hK.matrix_mulVec (continuous_const : Continuous (fun _ : ℝ => normalBurn β q))).intervalIntegrable
    (μ := MeasureTheory.volume) (PolynomialBurn.burnStart j:ℝ) (PolynomialBurn.burnFinish j:ℝ)
  ext i
  have hproj := (ContinuousLinearMap.proj (R := ℝ) i).intervalIntegral_comp_comm hint
  change (∫ t in (PolynomialBurn.burnStart j:ℝ)..(PolynomialBurn.burnFinish j:ℝ),
      (normalInverse (H t) *ᵥ normalBurn β q) i) =
    (∫ t in (PolynomialBurn.burnStart j:ℝ)..(PolynomialBurn.burnFinish j:ℝ),
      normalInverse (H t) *ᵥ normalBurn β q) i at hproj
  rw [← hproj]
  have he (t : ℝ) : (normalInverse (H t) *ᵥ normalBurn β q) i = β*(normalInverse (H t) i 1*q 2) := by
    simp [normalBurn, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_mul_const]
  simp only [Pi.smul_apply, smul_eq_mul, normal_mean z F H hdH hiH j i]
  ring

theorem target_integral (α : ℝ) (z : ℝ → Fin 5 → ℝ)
    (F : ℝ → Matrix (Fin 4) (Fin 4) ℝ) (hz : Continuous z) (hF : Continuous F)
    (hdF : ∀ t ∈ Set.Icc (0:ℝ) (3/5), HasDerivAt F (planeGenerator (z t)*F t) t)
    (hiF : F 0 = 1) :
    (∫ t in (0:ℝ)..(3/5), planeInverse (F t) *ᵥ TargetThrust.forcing α (z t)) =
      -α • FreeResponse.pullbackIntegrals z F := by
  have hK : Continuous (fun t => planeInverse (F t)) :=
    (continuous_const.matrix_mul hF.matrix_transpose).matrix_mul continuous_const
  have hint := (hK.matrix_mulVec (TargetThrust.forcing_continuous α hz)).intervalIntegrable
    (μ := MeasureTheory.volume) (0:ℝ) (3/5)
  ext i
  have hproj := (ContinuousLinearMap.proj (R := ℝ) i).intervalIntegral_comp_comm hint
  change (∫ t in (0:ℝ)..(3/5), (planeInverse (F t) *ᵥ TargetThrust.forcing α (z t)) i) =
    (∫ t in (0:ℝ)..(3/5), planeInverse (F t) *ᵥ TargetThrust.forcing α (z t)) i at hproj
  rw [← hproj]
  simp_rw [TargetThrust.forcing_pairing]
  rw [intervalIntegral.integral_const_mul]
  change -α*(∫ t in (0:ℝ)..(3/5), (planeInverse (F t)*planeInjection (z t)) i 1) =
    -α*(∫ t in (0:ℝ)..(3/5), ((F t)⁻¹*planeInjection (z t)) i 1)
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  rw [plane_inverse z F hdF hiF t (by norm_num [Set.uIcc_of_le] at ht ⊢; exact ht)]

theorem retained_plane_means (α β : ℝ) (z : ℝ → Fin 5 → ℝ)
    (F : ℝ → Matrix (Fin 4) (Fin 4) ℝ) (H : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hz : Continuous z) (hF : Continuous F)
    (hdF : ∀ t ∈ Set.Icc (0:ℝ) (3/5), HasDerivAt F (planeGenerator (z t)*F t) t)
    (hiF : F 0 = 1) (initial : Fin 4 → ℝ) (command : Fin 18 → Vec3) :
    retainedPlane α β z F initial command =
      F (3/5) *ᵥ (initial+
        (∑ j : Fin 18, (β/50) • (planeMean z F H j *ᵥ ![command j 0,command j 1]))-
        α • FreeResponse.pullbackIntegrals z F) := by
  unfold retainedPlane
  simp_rw [plane_burn_integral β z F H hz hF hdF hiF, target_integral α z F hz hF hdF hiF]
  simp only [neg_smul, sub_eq_add_neg]

theorem retained_normal_means (β : ℝ) (z : ℝ → Fin 5 → ℝ)
    (F : ℝ → Matrix (Fin 4) (Fin 4) ℝ) (H : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hH : Continuous H)
    (hdH : ∀ t ∈ Set.Icc (0:ℝ) (3/5), HasDerivAt H (normalGenerator (z t)*H t) t)
    (hiH : H 0 = 1) (initial : Fin 2 → ℝ) (command : Fin 18 → Vec3) :
    retainedNormal β H initial command =
      H (3/5) *ᵥ (initial+∑ j : Fin 18, (β/50*command j 2) • normalMean z F H j) := by
  unfold retainedNormal
  simp_rw [normal_burn_integral β z F H hH hdH hiH]

end GNC.Applications.OrbitalFuel.BurnMeanResponse
