import GNC.Applications.OrbitalFuel.ValidatedPhysicalRetained

/-! Bounds on the actual nonlinear chaser relative to its reference, with
the complete transported gravity remainder still visible. Closing a numerical
reserve for that remainder is a subsequent obligation, not an assumption
hidden in the retained-response certificate.
-/
noncomputable section
namespace GNC.Applications.OrbitalFuel.RetainedPhysical
open GNC GNC.ThrustSupport PolynomialOrbit PolynomialOrbitTransition PolynomialBurn RetainedPrefix Matrix
set_option autoImplicit false

def remainder (F : ℝ → Matrix (Fin 4) (Fin 4) ℝ) (H : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (r : ℝ → Vec3) (T : ℝ) (j : Fin 2) : Vec3 := fun i =>
  cartesian (ChaserPrefix.planeRemainder F r T) (ChaserPrefix.normalRemainder H r T)
    ⟨3*j.val+i.val,by omega⟩

def deviation (w : Fin 4 → ℝ) (p v : Vec3) (j : Fin 2) : Vec3 := fun i =>
  cartesian (PlanarChaserError.plane w p v) (PlanarChaserError.normal p v)
    ⟨3*j.val+i.val,by omega⟩

theorem deviation_position (w : Fin 4 → ℝ) (p v : Vec3) :
    deviation w p v 0 = p-position w := by
  ext i
  fin_cases i <;> simp [deviation,cartesian,PlanarChaserError.plane,PlanarChaserError.normal,position]

theorem deviation_velocity (w : Fin 4 → ℝ) (p v : Vec3) :
    deviation w p v 1 = v-![w 2,w 3,0] := by
  ext i
  fin_cases i <;> simp [deviation,cartesian,PlanarChaserError.plane,PlanarChaserError.normal,
    Matrix.cons_val_two,Matrix.cons_val_three]

theorem cartesian_add (p p' : Fin 4 → ℝ) (n n' : Fin 2 → ℝ) :
    cartesian (p+p') (n+n') = cartesian p n+cartesian p' n' := by
  ext i
  fin_cases i <;> rfl

section Motion
variable (w : ℝ → Fin 4 → ℝ) (p v : ℝ → Vec3)
    (F : ℝ → Matrix (Fin 4) (Fin 4) ℝ) (H : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (q : Vec3)
    (hw : Continuous w) (hp : Continuous p) (hv : Continuous v)
    (hF : Continuous F) (hH : Continuous H)
    (hr : ∀ t, 0 < radius (w t))
    (hn : ∀ t ∈ Set.Icc (0:ℝ) (3/5), p t ≠ 0)
    (hdw : ∀ t ∈ Set.Icc (0:ℝ) (3/5), HasDerivAt w
      (physicalRate (PolynomialTransition.alpha:ℝ) (w t)) t)
    (hdF : ∀ t ∈ Set.Icc (0:ℝ) (3/5), HasDerivAt F (planeGenerator (lift (w t))*F t) t)
    (hdH : ∀ t ∈ Set.Icc (0:ℝ) (3/5), HasDerivAt H (normalGenerator (lift (w t))*H t) t)
    (hiF : F 0 = 1) (hiH : H 0 = 1)
    (hip : PlanarChaserError.plane (w 0) (p 0) (v 0) = TerminalResponse.initialPlane (Real.sqrt (3/2)))
    (hin : PlanarChaserError.normal (p 0) (v 0) = TerminalResponse.initialNormal)
    (hdp : ∀ k < 37, ∀ t ∈ Set.Ioo (BurnSchedule.time k:ℝ) (BurnSchedule.time (k+1):ℝ),
      HasDerivAt p (v t) t)
    (hdv : ∀ k < 37, ∀ t ∈ Set.Ioo (BurnSchedule.time k:ℝ) (BurnSchedule.time (k+1):ℝ),
      HasDerivAt v (Gravity.field3 1 (p t)+BurnSchedule.input
        (fun j t => ChaserResponse.acceleration (beta:ℝ) (lift (w t)) (commands q j)) k t) t)
    {T : ℝ} (hT : T ∈ Set.Icc (0:ℝ) (3/5))

include hw hp hv hF hH hr hn hdw hdF hdH hiF hiH hip hin hdp hdv hT in
theorem nonlinear_decomposition (j : Fin 2) :
    deviation (w T) (p T) (v T) j =
      retained (fun t => lift (w t)) F H (Real.sqrt (3/2:ℝ)) q T j+
        remainder F H (fun t => PlanarChaserError.residual (w t) (p t)) T j := by
  have hz := lift_continuous hw hr
  have hplane := ChaserPrefix.plane_prefix (PolynomialTransition.alpha:ℝ) (beta:ℝ)
    w p v F (commands q) hw hp hv hz hF (fun t _ => hr t) hn hdw hdF hiF hdp hdv hT
  have hnormal := ChaserPrefix.normal_prefix (beta:ℝ) w p v H (commands q)
    hw hp hv hH (fun t _ => hr t) hn hdH hiH hdp hdv hT
  rw [hip] at hplane
  rw [hin] at hnormal
  ext i
  simp only [deviation,hplane,hnormal,cartesian_add,Pi.add_apply,retained,remainder]

include hw hp hv hF hH hr hn hdw hdF hdH hiF hiH hip hin hdp hdv hT in
/-- Every-time physical error bounds. The explicit gravity integrals are
not yet replaced by a certified numerical reserve. -/
theorem nonlinear_enclosure
    (hiw : w 0 = ![4/5,0,0,Real.sqrt (3/2)])
    (hq : q ∈ Cap SharedBiasExample.axis SharedBiasCertificates.Solar.kappa) :
    GNC.enorm ((RetainedNorm.lengthScale:ℝ) • (p T-position (w T))) ≤
      10123001+GNC.enorm ((RetainedNorm.lengthScale:ℝ) •
        remainder F H (fun t => PlanarChaserError.residual (w t) (p t)) T 0) ∧
    GNC.enorm (SolarSensitivityFuel.speed • (v T-![w T 2,w T 3,0])) ≤
      5120001/1000000+GNC.enorm (SolarSensitivityFuel.speed •
        remainder F H (fun t => PlanarChaserError.residual (w t) (p t)) T 1) := by
  have hb := physical_reference_enclosure w F H hw hF hH hr hdw hdF hdH hiw hiF hiH hT q hq
  constructor
  · rw [← deviation_position (w T) (p T) (v T),
      nonlinear_decomposition w p v F H q hw hp hv hF hH hr hn hdw hdF hdH hiF hiH hip hin hdp hdv hT 0,
      smul_add]
    exact (GNC.enorm_add_le _ _).trans (add_le_add hb.1 le_rfl)
  · rw [← deviation_velocity (w T) (p T) (v T),
      nonlinear_decomposition w p v F H q hw hp hv hF hH hr hn hdw hdF hdH hiF hiH hip hin hdp hdv hT 1,
      smul_add]
    exact (GNC.enorm_add_le _ _).trans (add_le_add hb.2 le_rfl)

end Motion
end GNC.Applications.OrbitalFuel.RetainedPhysical
