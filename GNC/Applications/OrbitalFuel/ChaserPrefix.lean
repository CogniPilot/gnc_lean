import GNC.Applications.OrbitalFuel.ChaserResponse
import GNC.Applications.OrbitalFuel.BurnPrefix

/-! Exact retained response and full gravity remainder at every mission time.
This includes partial burns and command switches. The physical ODE is used
only on open arcs; no derivative is invented at a rectangular-command edge.
-/
noncomputable section
open Matrix
open scoped Matrix Matrix.Norms.Elementwise
namespace GNC.Applications.OrbitalFuel.ChaserPrefix
open GNC PolynomialOrbit PolynomialOrbitTransition PlanarChaserError ChaserResponse

def planeRemainder (F : ℝ → Matrix (Fin 4) (Fin 4) ℝ) (r : ℝ → Vec3) (T : ℝ) : Fin 4 → ℝ :=
  F T *ᵥ (∫ t in (0:ℝ)..T, planeInverse (F t) *ᵥ planeInput (r t))

def normalRemainder (H : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (r : ℝ → Vec3) (T : ℝ) : Fin 2 → ℝ :=
  H T *ᵥ (∫ t in (0:ℝ)..T, normalInverse (H t) *ᵥ normalInput (r t))

def retainedPlane (α β : ℝ) (z : ℝ → Fin 5 → ℝ)
    (F : ℝ → Matrix (Fin 4) (Fin 4) ℝ) (initial : Fin 4 → ℝ)
    (command : Fin 18 → Vec3) (T : ℝ) : Fin 4 → ℝ :=
  F T *ᵥ (initial+
    (∑ j : Fin 18, ∫ t in min (PolynomialBurn.burnStart j:ℝ) T..min (PolynomialBurn.burnFinish j:ℝ) T,
      planeInverse (F t) *ᵥ planeBurn β (z t) (command j))+
    ∫ t in (0:ℝ)..T, planeInverse (F t) *ᵥ TargetThrust.forcing α (z t))

def retainedNormal (β : ℝ) (H : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (initial : Fin 2 → ℝ) (command : Fin 18 → Vec3) (T : ℝ) : Fin 2 → ℝ :=
  H T *ᵥ (initial+
    ∑ j : Fin 18, ∫ t in min (PolynomialBurn.burnStart j:ℝ) T..min (PolynomialBurn.burnFinish j:ℝ) T,
      normalInverse (H t) *ᵥ normalBurn β (command j))

section Motion
variable (α β : ℝ) (w : ℝ → Fin 4 → ℝ) (p v : ℝ → Vec3)
    (F : ℝ → Matrix (Fin 4) (Fin 4) ℝ) (H : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (command : Fin 18 → Vec3)
    (hw : Continuous w) (hp : Continuous p) (hv : Continuous v)
    (hz : Continuous (fun t => lift (w t))) (hF : Continuous F) (hH : Continuous H)
    (hr : ∀ t ∈ Set.Icc (0:ℝ) (3/5), 0 < radius (w t))
    (hn : ∀ t ∈ Set.Icc (0:ℝ) (3/5), p t ≠ 0)
    (hdw : ∀ t ∈ Set.Icc (0:ℝ) (3/5), HasDerivAt w (physicalRate α (w t)) t)
    (hdF : ∀ t ∈ Set.Icc (0:ℝ) (3/5), HasDerivAt F (planeGenerator (lift (w t))*F t) t)
    (hdH : ∀ t ∈ Set.Icc (0:ℝ) (3/5), HasDerivAt H (normalGenerator (lift (w t))*H t) t)
    (hiF : F 0 = 1) (hiH : H 0 = 1)
    (hdp : ∀ k < 37, ∀ t ∈ Set.Ioo (BurnSchedule.time k:ℝ) (BurnSchedule.time (k+1):ℝ),
      HasDerivAt p (v t) t)
    (hdv : ∀ k < 37, ∀ t ∈ Set.Ioo (BurnSchedule.time k:ℝ) (BurnSchedule.time (k+1):ℝ),
      HasDerivAt v (Gravity.field3 1 (p t)+
        BurnSchedule.input (fun j t => acceleration β (lift (w t)) (command j)) k t) t)
    {T : ℝ} (hT : T ∈ Set.Icc (0:ℝ) (3/5))

include hw hp hv hz hF hr hn hdw hdF hiF hdp hdv hT in
/-- Exact physical in-plane error at an arbitrary time, before any remainder
reserve is asserted sufficient. -/
theorem plane_prefix :
    plane (w T) (p T) (v T) =
      retainedPlane α β (fun t => lift (w t)) F (plane (w 0) (p 0) (v 0)) command T+
        planeRemainder F (fun t => residual (w t) (p t)) T := by
  have hc := residual_continuousOn hw.continuousOn hp.continuousOn hr hn
  have hpi : Continuous planeInput := by
    apply continuous_pi
    intro i
    fin_cases i <;> simp [planeInput, Matrix.cons_val_two, Matrix.cons_val_three] <;> fun_prop
  have hrc := hpi.comp_continuousOn hc
  have htc := TargetThrust.forcing_continuous α hz
  have he := BurnPrefix.endpoint F (fun t => planeGenerator (lift (w t))) planeForm
    (fun t => plane (w t) (p t) (v t))
    (fun j t => planeBurn β (lift (w t)) (command j))
    (fun t => TargetThrust.forcing α (lift (w t))+planeInput (residual (w t) (p t)))
    planeForm_sq hF (plane_continuous hw hp hv) (fun j => planeBurn_continuous β (command j) hz)
    (htc.continuousOn.add hrc) hdF (fun t _ => plane_hamiltonian (lift (w t))) hiF (by
      intro k hk t ht
      have hdom : t ∈ Set.Icc (0:ℝ) (3/5) :=
        ⟨(BurnSchedule.horizon k hk).1.trans ht.1.le,
          ht.2.le.trans (BurnSchedule.horizon k hk).2⟩
      have hd := plane_derivative (hdw t hdom) (hdp k hk t ht) (hdv k hk t ht)
      convert hd using 1
      congr 1
      by_cases hburn : k < 37 ∧ k%2 = 1
      · simp only [BurnSchedule.input, dif_pos hburn]
        exact (plane_input_identity α β (w t) (command ⟨k/2,by omega⟩)
          (residual (w t) (p t))).symm
      · simp only [BurnSchedule.input, dif_neg hburn, zero_add]
        exact (plane_coast_identity α (w t) (residual (w t) (p t))).symm) hT
  have hK : Continuous (fun t => planeInverse (F t)) :=
    (continuous_const.matrix_mul hF.matrix_transpose).matrix_mul continuous_const
  have hmul : Continuous (fun x : Matrix (Fin 4) (Fin 4) ℝ × (Fin 4 → ℝ) => x.1 *ᵥ x.2) :=
    continuous_fst.matrix_mulVec continuous_snd
  have hri := ((hmul.comp_continuousOn (hK.continuousOn.prodMk hrc)).mono
    (Set.Icc_subset_Icc le_rfl hT.2)).intervalIntegrable_of_Icc (μ := MeasureTheory.volume) hT.1
  change IntervalIntegrable (fun t => planeInverse (F t) *ᵥ planeInput (residual (w t) (p t)))
    MeasureTheory.volume 0 T at hri
  have hti := (hK.matrix_mulVec htc).intervalIntegrable (μ := MeasureTheory.volume) (0:ℝ) T
  change _ = F T *ᵥ (_+_+∫ t in (0:ℝ)..T,
    planeInverse (F t) *ᵥ (TargetThrust.forcing α (lift (w t))+planeInput (residual (w t) (p t)))) at he
  simp_rw [mulVec_add] at he
  rw [intervalIntegral.integral_add hti hri] at he
  simpa only [retainedPlane, planeRemainder, ← add_assoc, mulVec_add] using he

include hw hp hv hH hr hn hdH hiH hdp hdv hT in
theorem normal_prefix :
    normal (p T) (v T) = retainedNormal β H (normal (p 0) (v 0)) command T+
      normalRemainder H (fun t => residual (w t) (p t)) T := by
  have hc := residual_continuousOn hw.continuousOn hp.continuousOn hr hn
  have hni : Continuous normalInput := by
    apply continuous_pi
    intro i
    fin_cases i <;> simp [normalInput] <;> fun_prop
  have hrc := hni.comp_continuousOn hc
  have he := BurnPrefix.endpoint H (fun t => normalGenerator (lift (w t))) normalForm
    (fun t => normal (p t) (v t)) (fun j _t => normalBurn β (command j))
    (fun t => normalInput (residual (w t) (p t))) normalForm_sq hH (normal_continuous hp hv)
    (fun _ => continuous_const) hrc hdH (fun t _ => normal_hamiltonian (lift (w t))) hiH (by
      intro k hk t ht
      have hd := normal_derivative (w t) (hdp k hk t ht) (hdv k hk t ht)
      convert hd using 1
      congr 1
      by_cases hburn : k < 37 ∧ k%2 = 1
      · simp only [BurnSchedule.input, dif_pos hburn]
        exact (normal_input_identity β (lift (w t)) (command ⟨k/2,by omega⟩)
          (residual (w t) (p t))).symm
      · simp only [BurnSchedule.input, dif_neg hburn, zero_add]) hT
  simpa only [retainedNormal, normalRemainder, mulVec_add] using he

end Motion
end GNC.Applications.OrbitalFuel.ChaserPrefix
