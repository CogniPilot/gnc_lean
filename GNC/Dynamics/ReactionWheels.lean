import GNC.Lie.RotationKinematics
import GNC.Analysis.EuclideanBox

/-! Three ideal balanced reaction wheels aligned with the body axes.

`J` is the constant reduced body inertia: it includes the wheels' transverse
inertia, while their absolute axial angular momenta are represented by `h`.
Thus wheel motor torque is `h'`, and relative rotor speed is `hᵢ/jᵢ - ωᵢ`.
The model equations are explicit. No friction, compliance, motor bandwidth,
mass-loss inertia correction or attitude estimation error is assumed away by
a theorem about the physical hardware.

The momentum realization below includes arbitrary differentiable inertial
total momentum and its external torque. Zero total momentum is a useful
nominal specialization, not a property of every spacecraft initialization.
-/
noncomputable section
set_option autoImplicit false
namespace GNC.ReactionWheels
open Matrix RotationKinematics
open scoped Matrix Matrix.Norms.Operator

abbrev InertiaMatrix := Matrix (Fin 3) (Fin 3) ℝ

def bodyMomentum (J : InertiaMatrix) (w h : Vec3) : Vec3 := J *ᵥ w+h

def inertialMomentum (J : InertiaMatrix) (R : SO3) (w h : Vec3) : Vec3 :=
  rotate R (bodyMomentum J w h)

/-- Euler's equation for the spacecraft and the three wheel spin axes.
`u` is torque applied by the motors to the wheels; `L` is external body torque. -/
def Euler (J : InertiaMatrix) (w a h u L : Vec3) : Prop :=
  J *ᵥ a+u+w ⨯₃ bodyMomentum J w h = L

theorem rotate_derivative {R : ℝ → SO3} {x : ℝ → Vec3} {w v : Vec3} {t : ℝ}
    (hR : HasDerivAt (fun s => (R s).val) ((R t).val*skew w) t)
    (hx : HasDerivAt x v t) :
    HasDerivAt (fun s => rotate (R s) (x s))
      (rotate (R t) (v+w ⨯₃ x t)) t := by
  convert SymplecticResponse.mulVec_derivative hR hx using 1
  simp only [rotate, ← mulVec_mulVec, skew_mulVec, mulVec_add]
  abel

theorem inertia_derivative (J : InertiaMatrix) {w : ℝ → Vec3} {a : Vec3} {t : ℝ}
    (hw : HasDerivAt w a t) :
    HasDerivAt (fun s => J *ᵥ w s) (J *ᵥ a) t := by
  simpa using SymplecticResponse.mulVec_derivative (hasDerivAt_const t J) hw

/-- The model Euler equation implies the inertial angular-momentum balance. -/
theorem momentum_balance (J : InertiaMatrix) {R : ℝ → SO3} {w h : ℝ → Vec3}
    {a u L : Vec3} {t : ℝ}
    (hR : HasDerivAt (fun s => (R s).val) ((R t).val*skew (w t)) t)
    (hw : HasDerivAt w a t) (hh : HasDerivAt h u t)
    (he : Euler J (w t) a (h t) u L) :
    HasDerivAt (fun s => inertialMomentum J (R s) (w s) (h s)) (rotate (R t) L) t := by
  exact he ▸ rotate_derivative hR ((inertia_derivative J hw).fun_add hh)

/-- Wheel spin momentum required by a prescribed inertial total momentum. -/
def momentum (J : InertiaMatrix) (R : SO3) (w H : Vec3) : Vec3 :=
  rotate R⁻¹ H-J *ᵥ w

/-- Actual derivative of `momentum`, hence the ideal wheel motor torque.
`D` is the external torque expressed in inertial axes. -/
def motor (J : InertiaMatrix) (R : SO3) (w a H D : Vec3) : Vec3 :=
  rotate R⁻¹ D-w ⨯₃ rotate R⁻¹ H-J *ᵥ a

theorem momentum_identity (J : InertiaMatrix) (R : SO3) (w H : Vec3) :
    bodyMomentum J w (momentum J R w H) = rotate R⁻¹ H := by
  simp [bodyMomentum, momentum]

theorem inertial_identity (J : InertiaMatrix) (R : SO3) (w H : Vec3) :
    inertialMomentum J R w (momentum J R w H) = H := by
  rw [inertialMomentum, momentum_identity, ← rotate_mul]
  simp [rotate]

theorem momentum_derivative (J : InertiaMatrix) {R : ℝ → SO3} {w H : ℝ → Vec3}
    {a D : Vec3} {t : ℝ}
    (hR : HasDerivAt (fun s => (R s).val) ((R t).val*skew (w t)) t)
    (hw : HasDerivAt w a t) (hH : HasDerivAt H D t) :
    HasDerivAt (fun s => momentum J (R s) (w s) (H s))
      (motor J (R t) (w t) a (H t) D) t :=
  (inverse_rotate_derivative hR hH).fun_sub (inertia_derivative J hw)

theorem realizes (J : InertiaMatrix) (R : SO3) (w a H D : Vec3) :
    Euler J w a (momentum J R w H) (motor J R w a H D) (rotate R⁻¹ D) := by
  rw [Euler, momentum_identity, motor]
  abel

theorem momentum_bound (J : InertiaMatrix) (R : SO3) (w H : Vec3)
    {jMax W B : ℝ} (hj : ∀ v, enorm (J *ᵥ v) ≤ jMax*enorm v)
    (hw : enorm w ≤ W) (hH : enorm H ≤ B) (hj0 : 0 ≤ jMax) :
    enorm (momentum J R w H) ≤ B+jMax*W := by
  have hb : enorm (momentum J R w H) ≤ enorm H+enorm (J *ᵥ w) := by
    simpa [momentum, sub_eq_add_neg, rotate_enorm, enorm_neg] using
      enorm_add_le (rotate R⁻¹ H) (-(J *ᵥ w))
  exact hb.trans (add_le_add hH ((hj w).trans (mul_le_mul_of_nonneg_left hw hj0)))

theorem motor_bound (J : InertiaMatrix) (R : SO3) (w a H D : Vec3)
    {jMax W A B E : ℝ} (hj : ∀ v, enorm (J *ᵥ v) ≤ jMax*enorm v)
    (hw : enorm w ≤ W) (ha : enorm a ≤ A) (hH : enorm H ≤ B) (hD : enorm D ≤ E)
    (hj0 : 0 ≤ jMax) :
    enorm (motor J R w a H D) ≤ E+W*B+jMax*A := by
  have hc : enorm (w ⨯₃ rotate R⁻¹ H) ≤ W*B := by
    have hc := cross_enorm_le w (rotate R⁻¹ H)
    rw [rotate_enorm] at hc
    exact hc.trans (mul_le_mul hw hH (enorm_nonneg H) ((enorm_nonneg w).trans hw))
  have hb := enorm_add_le (rotate R⁻¹ D-(w ⨯₃ rotate R⁻¹ H)) (-(J *ᵥ a))
  have hb' := enorm_add_le (rotate R⁻¹ D) (-(w ⨯₃ rotate R⁻¹ H))
  simp only [enorm_neg, rotate_enorm] at hb hb'
  apply hb.trans
  change enorm (rotate R⁻¹ D-(w ⨯₃ rotate R⁻¹ H))+enorm (J *ᵥ a) ≤ _
  have hb'' : enorm (rotate R⁻¹ D-(w ⨯₃ rotate R⁻¹ H)) ≤
      enorm D+enorm (w ⨯₃ rotate R⁻¹ H) := by
    simpa only [sub_eq_add_neg] using hb'
  exact add_le_add (hb''.trans (add_le_add hD hc))
    ((hj a).trans (mul_le_mul_of_nonneg_left ha hj0))

/-- External torque accumulates inertial momentum. This finite-horizon
bound is derived from the actual derivative, not assumed from samples. -/
theorem externalMomentum_bound {H D : ℝ → Vec3} {a b E B : ℝ}
    (hd : ∀ t ∈ Set.Icc a b, HasDerivAt H (D t) t)
    (hD : ∀ t ∈ Set.Ico a b, enorm (D t) ≤ E) (hH : enorm (H a) ≤ B) :
    ∀ t ∈ Set.Icc a b, enorm (H t) ≤ B+E*(t-a) := by
  let e : Vec3 ≃L[ℝ] EuclideanSpace ℝ (Fin 3) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm
  have hd' (t : ℝ) (ht : t ∈ Set.Icc a b) :
      HasDerivWithinAt (fun s => e (H s)) (e (D t)) (Set.Icc a b) t :=
    (e.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t (hd t ht)).hasDerivWithinAt
  have hb' (t : ℝ) (ht : t ∈ Set.Ico a b) : ‖e (D t)‖ ≤ E := hD t ht
  have h := norm_image_sub_le_of_norm_deriv_le_segment' hd' hb'
  intro t ht
  have he : enorm (H t-H a) ≤ E*(t-a) := h t ht
  have ha : enorm (H t) ≤ enorm (H a)+enorm (H t-H a) := by
    simpa only [add_sub_cancel] using enorm_add_le (H a) (H t-H a)
  exact ha.trans (add_le_add hH he)

/-- Misalignment at an axial lever arm creates a torque even if the
nominal thrust line passes through the center of mass. -/
theorem pointing_torque_bound (R : SO3) (n q : Vec3) (lever force : ℝ)
    {rho : ℝ} (hn : enorm n = 1) (hq : enorm (q-n) ≤ rho) :
    enorm (rotate R (force • ((lever • n) ⨯₃ q))) ≤ |force| * |lever| * rho := by
  have hc : n ⨯₃ q = n ⨯₃ (q-n) := by simp
  have hb := cross_enorm_le n (q-n)
  rw [hn, one_mul] at hb
  simp only [rotate_enorm, map_smul, LinearMap.smul_apply, enorm_smul]
  rw [hc]
  nlinarith [mul_le_mul_of_nonneg_left (hb.trans hq)
    (mul_nonneg (abs_nonneg force) (abs_nonneg lever))]

def relativeSpeed (spinInertia : Fin 3 → ℝ) (w h : Vec3) : Vec3 :=
  fun i => h i/spinInertia i-w i

def relativeAcceleration (spinInertia : Fin 3 → ℝ) (a u : Vec3) : Vec3 :=
  fun i => u i/spinInertia i-a i

theorem relativeSpeed_derivative (spinInertia : Fin 3 → ℝ)
    {w h : ℝ → Vec3} {a u : Vec3} {t : ℝ}
    (hw : HasDerivAt w a t) (hh : HasDerivAt h u t) :
    HasDerivAt (fun s => relativeSpeed spinInertia (w s) (h s))
      (relativeAcceleration spinInertia a u) t := by
  apply hasDerivAt_pi.mpr
  intro i
  exact ((hasDerivAt_pi.mp hh i).div_const (spinInertia i)).sub (hasDerivAt_pi.mp hw i)

/-- The rotor's absolute axial momentum, including body spin. -/
theorem spin_identity (spinInertia : Fin 3 → ℝ) (hj : ∀ i, spinInertia i ≠ 0)
    (w h : Vec3) (i : Fin 3) :
    spinInertia i*(w i+relativeSpeed spinInertia w h i) = h i := by
  simp only [relativeSpeed, add_sub_cancel]
  field_simp [hj i]

theorem motor_identity (spinInertia : Fin 3 → ℝ) (hj : ∀ i, spinInertia i ≠ 0)
    (a u : Vec3) (i : Fin 3) :
    spinInertia i*(a i+relativeAcceleration spinInertia a u i) = u i := by
  simp only [relativeAcceleration, add_sub_cancel]
  field_simp [hj i]

theorem relativeSpeed_bound (spinInertia : Fin 3 → ℝ) (w h : Vec3)
    {jMin W B : ℝ} (hj0 : 0 < jMin) (hj : ∀ i, jMin ≤ spinInertia i)
    (hw : enorm w ≤ W) (hh : enorm h ≤ B) (i : Fin 3) :
    |relativeSpeed spinInertia w h i| ≤ B/jMin+W := by
  have hwi := (component_le_enorm w i).trans hw
  have hhi := (component_le_enorm h i).trans hh
  have hji : 0 < spinInertia i := hj0.trans_le (hj i)
  have hb : |h i/spinInertia i| ≤ B/jMin := by
    rw [abs_div, abs_of_pos hji]
    exact div_le_div₀ ((enorm_nonneg h).trans hh) hhi hj0 (hj i)
  exact (abs_sub _ _).trans (add_le_add hb hwi)

theorem momentum_zero (J : InertiaMatrix) (R : SO3) (w : Vec3) :
    momentum J R w 0 = -(J *ᵥ w) := by simp [momentum]

theorem motor_zero (J : InertiaMatrix) (R : SO3) (w a : Vec3) :
    motor J R w a 0 0 = -(J *ᵥ a) := by simp [motor]

/-- Motor allocation must include wheel gyroscopic transport even when a
body-torque controller has already compensated the rigid-body gyroscopic term. -/
def motorForBodyTorque (w h desiredTorque externalTorque : Vec3) : Vec3 :=
  externalTorque-w ⨯₃ h-desiredTorque

theorem allocation_identity (J : InertiaMatrix) (w h T L : Vec3) :
    L-motorForBodyTorque w h T L-w ⨯₃ bodyMomentum J w h = T-w ⨯₃ (J *ᵥ w) := by
  simp only [motorForBodyTorque, bodyMomentum, map_add]
  abel

end GNC.ReactionWheels
