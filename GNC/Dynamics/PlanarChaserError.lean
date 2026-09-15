import GNC.Dynamics.PlanarBurnObservable
import GNC.Dynamics.OrbitalRemainder
import GNC.Lie.ZeroAttitude

/-! Exact relative motion about a planar, tangentially thrusting reference.
The chaser follows the nonlinear inverse-square field in three dimensions.
Its gravity variational equation retains the complete Taylor remainder.
These are pointwise derivative identities, so they also apply separately
inside each burn/coast arc without imposing differentiability at switches.
-/
noncomputable section
namespace GNC.PlanarChaserError
open Matrix PolynomialOrbit PolynomialOrbitTransition

def plane (w : Fin 4 → ℝ) (p v : Vec3) : Fin 4 → ℝ :=
  ![p 0-w 0,p 1-w 1,v 0-w 2,v 1-w 3]

def normal (p v : Vec3) : Fin 2 → ℝ := ![p 2,v 2]

def planeInput (a : Vec3) : Fin 4 → ℝ := ![0,0,a 0,a 1]

def normalInput (a : Vec3) : Fin 2 → ℝ := ![0,a 2]

def referenceThrust (α : ℝ) (w : Fin 4 → ℝ) : Vec3 :=
  α • (polynomialFrame (lift w) *ᵥ ![0,1,0])

def residual (w : Fin 4 → ℝ) (p : Vec3) : Vec3 :=
  Gravity.remainder3 1 (position w) (p-position w)

theorem field3_formula (μ : ℝ) (p : Vec3) :
    Gravity.field3 μ p = (-μ/enorm p^3) • p := rfl

theorem reference_acceleration (α : ℝ) (w : Fin 4 → ℝ) :
    ![physicalRate α w 2,physicalRate α w 3,0] =
      Gravity.field3 1 (position w)+referenceThrust α w := by
  rw [field3_formula, position_norm]
  ext i
  fin_cases i <;>
    simp [physicalRate, position, referenceThrust, polynomialFrame, lift, Matrix.cons_val_two,
      Matrix.cons_val_three, div_eq_mul_inv] <;> ring

theorem gravity_decomposition (w : Fin 4 → ℝ) (p : Vec3) :
    Gravity.field3 1 p = Gravity.field3 1 (position w)+
      Gravity.gradient3 1 (position w) (p-position w)+residual w p := by
  unfold residual Gravity.remainder3
  rw [add_sub_cancel]
  abel

theorem plane_derivative {w : ℝ → Fin 4 → ℝ} {p v : ℝ → Vec3} {α t : ℝ}
    {a : Vec3} (hw : HasDerivAt w (physicalRate α (w t)) t)
    (hp : HasDerivAt p (v t) t)
    (hv : HasDerivAt v (Gravity.field3 1 (p t)+a) t) :
    HasDerivAt (fun s => plane (w s) (p s) (v s))
      (planeGenerator (lift (w t)) *ᵥ plane (w t) (p t) (v t)+
        planeInput (a-referenceThrust α (w t)+residual (w t) (p t))) t := by
  have hraw : HasDerivAt (fun s => plane (w s) (p s) (v s))
      ![v t 0-w t 2,v t 1-w t 3,
        (Gravity.field3 1 (p t)) 0+a 0-physicalRate α (w t) 2,
        (Gravity.field3 1 (p t)) 1+a 1-physicalRate α (w t) 3] t := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · simpa [plane, physicalRate] using (hasDerivAt_pi.mp hp 0).sub (hasDerivAt_pi.mp hw 0)
    · simpa [plane, physicalRate] using (hasDerivAt_pi.mp hp 1).sub (hasDerivAt_pi.mp hw 1)
    · simpa [plane] using (hasDerivAt_pi.mp hv 0).sub (hasDerivAt_pi.mp hw 2)
    · simpa [plane] using (hasDerivAt_pi.mp hv 1).sub (hasDerivAt_pi.mp hw 3)
  convert hraw using 1
  have hpos : ![plane (w t) (p t) (v t) 0,plane (w t) (p t) (v t) 1,p t 2] =
      p t-position (w t) := by
    ext i
    fin_cases i <;> simp [plane, position, Matrix.cons_val_two]
  rw [plane_action (w t) _ (p t 2), hpos]
  have hg := gravity_decomposition (w t) (p t)
  have hr := reference_acceleration α (w t)
  ext i
  fin_cases i <;>
    simp [plane, planeInput, Matrix.cons_val_two, Matrix.cons_val_three]
  · have hg0 := congrFun hg 0
    have hr0 := congrFun hr 0
    simp only [Pi.add_apply, Matrix.cons_val_zero] at hg0 hr0
    linarith
  · have hg1 := congrFun hg 1
    have hr1 := congrFun hr 1
    simp only [Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_zero] at hg1 hr1
    linarith

theorem normal_derivative {p v : ℝ → Vec3} (w : Fin 4 → ℝ) {t : ℝ}
    {a : Vec3} (hp : HasDerivAt p (v t) t)
    (hv : HasDerivAt v (Gravity.field3 1 (p t)+a) t) :
    HasDerivAt (fun s => normal (p s) (v s))
      (normalGenerator (lift w) *ᵥ normal (p t) (v t)+
        normalInput (a+residual w (p t))) t := by
  have hraw : HasDerivAt (fun s => normal (p s) (v s))
      ![v t 2,(Gravity.field3 1 (p t)) 2+a 2] t := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · simpa [normal] using hasDerivAt_pi.mp hp 2
    · simpa [normal] using hasDerivAt_pi.mp hv 2
  convert hraw using 1
  have hpos : ![p t 0-w 0,p t 1-w 1,normal (p t) (v t) 0] = p t-position w := by
    ext i
    fin_cases i <;> simp [normal, position, Matrix.cons_val_two]
  rw [normal_action w _ (p t 0-w 0) (p t 1-w 1), hpos]
  have hg := congrFun (gravity_decomposition w (p t)) 2
  have hz : Gravity.field3 1 (position w) 2 = 0 := by
    simp [field3_formula, position]
  simp only [Pi.add_apply, hz, zero_add] at hg
  ext i
  fin_cases i <;> simp [normal, normalInput]
  linarith

theorem plane_continuous {w : ℝ → Fin 4 → ℝ} {p v : ℝ → Vec3}
    (hw : Continuous w) (hp : Continuous p) (hv : Continuous v) :
    Continuous (fun t => plane (w t) (p t) (v t)) := by
  apply continuous_pi
  intro i
  fin_cases i <;> simp [plane, Matrix.cons_val_two, Matrix.cons_val_three] <;> fun_prop

theorem normal_continuous {p v : ℝ → Vec3} (hp : Continuous p) (hv : Continuous v) :
    Continuous (fun t => normal (p t) (v t)) := by
  apply continuous_pi
  intro i
  fin_cases i <;> simp [normal] <;> fun_prop

theorem field3_continuousOn {S : Set ℝ} {p : ℝ → Vec3} (μ : ℝ)
    (hp : ContinuousOn p S) (hz : ∀ t ∈ S, p t ≠ 0) :
    ContinuousOn (fun t => Gravity.field3 μ (p t)) S := by
  simp_rw [field3_formula]
  exact (continuousOn_const.div ((enorm_continuous.comp_continuousOn hp).pow 3)
    (fun t ht => pow_ne_zero _ (fun h => hz t ht ((enorm_eq_zero_iff _).mp h)))).smul hp

theorem residual_continuousOn {S : Set ℝ} {w : ℝ → Fin 4 → ℝ} {p : ℝ → Vec3}
    (hw : ContinuousOn w S) (hp : ContinuousOn p S)
    (hr : ∀ t ∈ S, 0 < radius (w t)) (hz : ∀ t ∈ S, p t ≠ 0) :
    ContinuousOn (fun t => residual (w t) (p t)) S := by
  have hpos : ContinuousOn (fun t => position (w t)) S :=
    (show Continuous position by
      apply continuous_pi
      intro i
      fin_cases i <;> simp [position, Matrix.cons_val_two] <;> fun_prop).comp_continuousOn hw
  have hrad : ContinuousOn (fun t => radius (w t)) S := by
    simpa only [Function.comp_def, position_norm] using enorm_continuous.comp_continuousOn hpos
  have hlift : ContinuousOn (fun t => lift (w t)) S := by
    apply continuousOn_pi.mpr
    intro i
    fin_cases i
    · change ContinuousOn (fun t => w t 0) S
      exact (continuous_apply 0).comp_continuousOn hw
    · change ContinuousOn (fun t => w t 1) S
      exact (continuous_apply 1).comp_continuousOn hw
    · change ContinuousOn (fun t => w t 2) S
      exact (continuous_apply 2).comp_continuousOn hw
    · change ContinuousOn (fun t => w t 3) S
      exact (continuous_apply 3).comp_continuousOn hw
    · exact hrad.inv₀ (fun t ht => (hr t ht).ne')
  have hG : ContinuousOn (fun t => gravityMatrix (lift (w t))) S :=
    (show Continuous gravityMatrix by
      apply continuous_matrix
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp [gravityMatrix, Matrix.cons_val_two] <;> fun_prop).comp_continuousOn hlift
  have hmul : Continuous (fun x : Matrix (Fin 3) (Fin 3) ℝ × Vec3 => x.1 *ᵥ x.2) :=
    continuous_fst.matrix_mulVec continuous_snd
  have hgrad := hmul.comp_continuousOn (hG.prodMk (hp.sub hpos))
  have hfield := field3_continuousOn 1 hpos (fun t ht h => by
    have he := (enorm_eq_zero_iff _).mpr h
    rw [position_norm] at he
    exact (hr t ht).ne' he)
  have hform : (fun t => residual (w t) (p t)) =
      fun t => Gravity.field3 1 (p t)-Gravity.field3 1 (position (w t))-
        gravityMatrix (lift (w t)) *ᵥ (p t-position (w t)) := by
    funext t
    simp [residual, Gravity.remainder3, add_sub_cancel, gravity_matrix]
  rw [hform]
  exact ((field3_continuousOn 1 hp hz).sub hfield).sub hgrad

theorem chaser_nonzero (w : Fin 4 → ℝ) (p : Vec3) {P lower : ℝ}
    (hp : enorm (p-position w) ≤ P) (hr : lower ≤ radius w) (hsep : P < lower) :
    p ≠ 0 := by
  intro h
  rw [h, zero_sub, enorm_neg, position_norm] at hp
  linarith

/-- A uniform acceleration remainder on a proposed position tube. The
separation condition keeps every chaser position away from collision. -/
theorem residual_bound (w : Fin 4 → ℝ) (p : Vec3) {P lower : ℝ}
    (hp : enorm (p-position w) ≤ P) (hr : lower ≤ radius w) (hsep : P < lower) :
    enorm (residual w p) ≤ 3*P^2/(lower-P)^4 := by
  have hrad : lower ≤ enorm (position w) := by simpa only [position_norm] using hr
  exact (Gravity.remainder3_bound 1 (by norm_num) (position w) (p-position w)
    (hp.trans_lt (hsep.trans_le hrad))).trans (by
      simpa using Gravity.remainderBound_uniform (by norm_num : (0:ℝ) ≤ 1)
        (enorm_nonneg _) hp hrad hsep)

end GNC.PlanarChaserError
