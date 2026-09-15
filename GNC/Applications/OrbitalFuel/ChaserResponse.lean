import GNC.Applications.OrbitalFuel.BurnSchedule
import GNC.Applications.OrbitalFuel.TargetThrustTheory
import GNC.Dynamics.PlanarChaserError

/-! Exact endpoint of the three-dimensional nonlinear solar chaser.
The eighteen commanded vectors are expressed in the reference RTN frame;
the chaser's acceleration is the actual inverse-square field plus the
scheduled thrust. Only open-arc derivatives are required at burn switches.
The retained terminal map and the transported nonlinear remainder are
separated by an equality, before any reserve is asserted sufficient.
-/
noncomputable section
open Matrix
open scoped Matrix Matrix.Norms.Elementwise
namespace GNC.Applications.OrbitalFuel.ChaserResponse
open GNC PolynomialOrbit PolynomialOrbitTransition PlanarChaserError

def acceleration (β : ℝ) (z : Fin 5 → ℝ) (q : Vec3) : Vec3 :=
  β • (polynomialFrame z *ᵥ q)

def planeBurn (β : ℝ) (z : Fin 5 → ℝ) (q : Vec3) : Fin 4 → ℝ :=
  β • (planeInjection z *ᵥ ![q 0,q 1])

def normalBurn (β : ℝ) (q : Vec3) : Fin 2 → ℝ := β • ![0,q 2]

theorem acceleration_physical (β : ℝ) (w : Fin 4 → ℝ) (q : Vec3)
    (hh : 0 < angularMomentum w) :
    acceleration β (lift w) q = β • (physicalFrame w *ᵥ q) := by
  rw [physicalFrame_eq w hh]
  rfl

theorem planeBurn_continuous (β : ℝ) (q : Vec3) {z : ℝ → Fin 5 → ℝ}
    (hz : Continuous z) : Continuous (fun t => planeBurn β (z t) q) := by
  apply continuous_pi
  intro i
  fin_cases i <;> simp [planeBurn, planeInjection, Matrix.cons_val_two, Matrix.cons_val_three] <;> fun_prop

theorem plane_input_identity (α β : ℝ) (w : Fin 4 → ℝ) (q r : Vec3) :
    planeInput (acceleration β (lift w) q-referenceThrust α w+r) =
      planeBurn β (lift w) q+(TargetThrust.forcing α (lift w)+planeInput r) := by
  ext i
  fin_cases i <;>
    simp [planeInput, acceleration, planeBurn, referenceThrust, TargetThrust.forcing,
      planeInjection, polynomialFrame, dotProduct, Fin.sum_univ_succ,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail,
      Function.comp_def] <;> ring

theorem normal_input_identity (β : ℝ) (z : Fin 5 → ℝ) (q r : Vec3) :
    normalInput (acceleration β z q+r) = normalBurn β q+normalInput r := by
  ext i
  fin_cases i <;>
    simp [normalInput, acceleration, normalBurn, polynomialFrame,
      dotProduct, Fin.sum_univ_succ, Matrix.cons_val_two]

theorem plane_coast_identity (α : ℝ) (w : Fin 4 → ℝ) (r : Vec3) :
    planeInput (0-referenceThrust α w+r) = TargetThrust.forcing α (lift w)+planeInput r := by
  simpa [acceleration, planeBurn] using plane_input_identity α 0 w 0 r

theorem normal_coast_identity (r : Vec3) : normalInput (0+r) = normalInput r := by simp

def planeRemainder (F : ℝ → Matrix (Fin 4) (Fin 4) ℝ)
    (r : ℝ → Vec3) : Fin 4 → ℝ :=
  F (3/5) *ᵥ (∫ t in (0:ℝ)..(3/5), planeInverse (F t) *ᵥ planeInput (r t))

def normalRemainder (H : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (r : ℝ → Vec3) : Fin 2 → ℝ :=
  H (3/5) *ᵥ (∫ t in (0:ℝ)..(3/5), normalInverse (H t) *ᵥ normalInput (r t))

def retainedPlane (α β : ℝ) (z : ℝ → Fin 5 → ℝ)
    (F : ℝ → Matrix (Fin 4) (Fin 4) ℝ) (initial : Fin 4 → ℝ)
    (command : Fin 18 → Vec3) : Fin 4 → ℝ :=
  F (3/5) *ᵥ (initial+
    (∑ j : Fin 18, ∫ t in (PolynomialBurn.burnStart j:ℝ)..(PolynomialBurn.burnFinish j:ℝ),
      planeInverse (F t) *ᵥ planeBurn β (z t) (command j))+
    ∫ t in (0:ℝ)..(3/5), planeInverse (F t) *ᵥ TargetThrust.forcing α (z t))

def retainedNormal (β : ℝ) (H : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (initial : Fin 2 → ℝ) (command : Fin 18 → Vec3) : Fin 2 → ℝ :=
  H (3/5) *ᵥ (initial+
    ∑ j : Fin 18, ∫ t in (PolynomialBurn.burnStart j:ℝ)..(PolynomialBurn.burnFinish j:ℝ),
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

include hw hp hv hz hF hr hn hdw hdF hiF hdp hdv in
/-- The exact nonlinear in-plane endpoint is the retained forced response
plus the transported physical gravity remainder. No reserve bound or
linear error equation is assumed. -/
theorem plane_endpoint :
    plane (w (3/5)) (p (3/5)) (v (3/5)) =
      retainedPlane α β (fun t => lift (w t)) F (plane (w 0) (p 0) (v 0)) command+
        planeRemainder F (fun t => residual (w t) (p t)) := by
  have hc := residual_continuousOn hw.continuousOn hp.continuousOn hr hn
  have hpi : Continuous planeInput := by
    apply continuous_pi
    intro i
    fin_cases i <;> simp [planeInput, Matrix.cons_val_two, Matrix.cons_val_three] <;> fun_prop
  have hrc := hpi.comp_continuousOn hc
  have htc := TargetThrust.forcing_continuous α hz
  have he := BurnSchedule.endpoint F (fun t => planeGenerator (lift (w t))) planeForm
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
        exact (plane_coast_identity α (w t) (residual (w t) (p t))).symm)
  have hK : Continuous (fun t => planeInverse (F t)) :=
    (continuous_const.matrix_mul hF.matrix_transpose).matrix_mul continuous_const
  have hmul : Continuous (fun x : Matrix (Fin 4) (Fin 4) ℝ × (Fin 4 → ℝ) => x.1 *ᵥ x.2) :=
    continuous_fst.matrix_mulVec continuous_snd
  have hri := (hmul.comp_continuousOn (hK.continuousOn.prodMk hrc)).intervalIntegrable_of_Icc
    (μ := MeasureTheory.volume)
    (by norm_num : (0:ℝ) ≤ 3/5)
  change IntervalIntegrable (fun t => planeInverse (F t) *ᵥ planeInput (residual (w t) (p t)))
    MeasureTheory.volume 0 (3/5) at hri
  have hti := (hK.matrix_mulVec htc).intervalIntegrable (μ := MeasureTheory.volume) (0:ℝ) (3/5)
  change _ = F (3/5) *ᵥ (_+_+∫ t in (0:ℝ)..(3/5),
    planeInverse (F t) *ᵥ (TargetThrust.forcing α (lift (w t))+planeInput (residual (w t) (p t)))) at he
  simp_rw [mulVec_add] at he
  rw [intervalIntegral.integral_add hti hri] at he
  simpa only [retainedPlane, planeRemainder, ← add_assoc, mulVec_add] using he

include hw hp hv hH hr hn hdH hiH hdp hdv in
theorem normal_endpoint :
    normal (p (3/5)) (v (3/5)) = retainedNormal β H (normal (p 0) (v 0)) command+
      normalRemainder H (fun t => residual (w t) (p t)) := by
  have hc := residual_continuousOn hw.continuousOn hp.continuousOn hr hn
  have hni : Continuous normalInput := by
    apply continuous_pi
    intro i
    fin_cases i <;> simp [normalInput] <;> fun_prop
  have hrc := hni.comp_continuousOn hc
  have he := BurnSchedule.endpoint H (fun t => normalGenerator (lift (w t))) normalForm
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
      · simp only [BurnSchedule.input, dif_neg hburn, zero_add])
  simpa only [retainedNormal, normalRemainder, mulVec_add] using he

end Motion
end GNC.Applications.OrbitalFuel.ChaserResponse
