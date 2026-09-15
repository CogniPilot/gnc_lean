import GNC.Dynamics.PlanarThrustFrame
import GNC.Lie.RotationKinematics

/-! The exact moving RTN frame of the thrusting planar reference, as SO(3).
Its angular velocity and acceleration include the reference evolution.
No frozen-frame approximation is used. -/
noncomputable section
set_option autoImplicit false
namespace GNC.PlanarAttitudeFrame
open PolynomialOrbit PolynomialOrbitTransition Matrix
open scoped Matrix Matrix.Norms.Operator

def unit (z : Fin 5 → ℝ) : Prop := (z 0^2+z 1^2)*z 4^2 = 1
def spin (z : Fin 5 → ℝ) : ℝ := (z 0*z 3-z 1*z 2)*z 4^2
def spinAcceleration (a : ℝ) (z : Fin 5 → ℝ) : ℝ :=
  a*z 4-2*(z 0*z 3-z 1*z 2)*z 4^4*(z 0*z 2+z 1*z 3)

theorem lift_unit (w : Fin 4 → ℝ) (hr : 0 < radius w) : unit (lift w) := by
  dsimp [unit, lift]
  rw [← radius_sq]
  field_simp

theorem frame_orthogonal {z : Fin 5 → ℝ} (hz : unit z) :
    (polynomialFrame z).transpose*polynomialFrame z = 1 := by
  dsimp [unit] at hz
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [polynomialFrame, mul_apply, Fin.sum_univ_succ] <;> nlinarith [hz]

theorem frame_det {z : Fin 5 → ℝ} (hz : unit z) : (polynomialFrame z).det = 1 := by
  dsimp [unit] at hz
  simp [polynomialFrame, det_fin_three, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
  nlinarith [hz]

def rotation (w : Fin 4 → ℝ) (hr : 0 < radius w) : SO3 :=
  ⟨polynomialFrame (lift w), (mem_orthogonalGroup_iff' (Fin 3) ℝ).mpr
    (frame_orthogonal (lift_unit w hr)), frame_det (lift_unit w hr)⟩

theorem frame_derivative {z : ℝ → Fin 5 → ℝ} {a t : ℝ}
    (hz : HasDerivAt z (rate a (z t)) t) (hu : unit (z t)) :
    HasDerivAt (fun s => polynomialFrame (z s))
      (polynomialFrame (z t)*skew ![0,0,spin (z t)]) t := by
  have h0 := (hasDerivAt_pi.mp hz 0).mul (hasDerivAt_pi.mp hz 4)
  have h1 := (hasDerivAt_pi.mp hz 1).mul (hasDerivAt_pi.mp hz 4)
  dsimp [unit] at hu
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  fin_cases i <;> fin_cases j
  · convert h0 using 1
    simp [polynomialFrame, rate, spin, skew, mul_apply, Fin.sum_univ_succ]
    linear_combination (z t 2*z t 4)*hu
  · convert h1.neg using 1
    · funext s
      simp [polynomialFrame]
    · simp [polynomialFrame, rate, spin, skew, mul_apply, Fin.sum_univ_succ]
      linear_combination -(z t 3*z t 4)*hu
  · simpa [polynomialFrame, skew, mul_apply, Fin.sum_univ_succ] using hasDerivAt_const t (0:ℝ)
  · convert h1 using 1
    simp [polynomialFrame, rate, spin, skew, mul_apply, Fin.sum_univ_succ]
    linear_combination (z t 3*z t 4)*hu
  · convert h0 using 1
    simp [polynomialFrame, rate, spin, skew, mul_apply, Fin.sum_univ_succ]
    linear_combination (z t 2*z t 4)*hu
  · simpa [polynomialFrame, skew, mul_apply, Fin.sum_univ_succ] using hasDerivAt_const t (0:ℝ)
  · simpa [polynomialFrame, skew, mul_apply, Fin.sum_univ_succ] using hasDerivAt_const t (0:ℝ)
  · simpa [polynomialFrame, skew, mul_apply, Fin.sum_univ_succ] using hasDerivAt_const t (0:ℝ)
  · simpa [polynomialFrame, skew, mul_apply, Fin.sum_univ_succ] using hasDerivAt_const t (1:ℝ)

theorem spin_derivative {z : ℝ → Fin 5 → ℝ} {a t : ℝ}
    (hz : HasDerivAt z (rate a (z t)) t) (hu : unit (z t)) :
    HasDerivAt (fun s => spin (z s)) (spinAcceleration a (z t)) t := by
  have h0 := hasDerivAt_pi.mp hz 0
  have h1 := hasDerivAt_pi.mp hz 1
  have h2 := hasDerivAt_pi.mp hz 2
  have h3 := hasDerivAt_pi.mp hz 3
  have h4 := hasDerivAt_pi.mp hz 4
  convert (((h0.mul h3).sub (h1.mul h2)).mul (h4.pow 2)) using 1
  dsimp [spinAcceleration, rate, unit] at *
  linear_combination -(a*z t 4)*hu

theorem physical_derivative {w : ℝ → Fin 4 → ℝ} {a t : ℝ}
    (hr : ∀ s, 0 < radius (w s)) (hw : HasDerivAt w (physicalRate a (w t)) t) :
    HasDerivAt (fun s => (rotation (w s) (hr s)).val)
      ((rotation (w t) (hr t)).val*skew ![0,0,spin (lift (w t))]) t :=
  frame_derivative (lift_derivative hw (hr t)) (lift_unit _ (hr t))

theorem physical_spin_derivative {w : ℝ → Fin 4 → ℝ} {a t : ℝ}
    (hr : 0 < radius (w t)) (hw : HasDerivAt w (physicalRate a (w t)) t) :
    HasDerivAt (fun s => spin (lift (w s))) (spinAcceleration a (lift (w t))) t :=
  spin_derivative (lift_derivative hw hr) (lift_unit _ hr)

theorem spin_bounds {z : Fin 5 → ℝ} {a : ℝ}
    (hz : ∀ i, |z i| ≤ 4/3) (ha : |a| ≤ 1) :
    |spin z| ≤ 7 ∧ |spinAcceleration a z| ≤ 82 := by
  have hc : |z 0*z 3-z 1*z 2| ≤ 32/9 := by
    calc
      _ ≤ |z 0| * |z 3|+|z 1| * |z 2| := by
        simpa only [abs_mul] using abs_sub (z 0*z 3) (z 1*z 2)
      _ ≤ (4/3:ℝ)*(4/3)+(4/3)*(4/3) := by gcongr <;> apply hz
      _ = 32/9 := by norm_num
  have hd : |z 0*z 2+z 1*z 3| ≤ 32/9 := by
    calc
      _ ≤ |z 0| * |z 2|+|z 1| * |z 3| := by
        simpa only [abs_mul] using abs_add_le (z 0*z 2) (z 1*z 3)
      _ ≤ (4/3:ℝ)*(4/3)+(4/3)*(4/3) := by gcongr <;> apply hz
      _ = 32/9 := by norm_num
  constructor
  · calc
      _ = |z 0*z 3-z 1*z 2| * |z 4|^2 := by simp [spin, abs_mul, abs_pow]
      _ ≤ (32/9:ℝ)*(4/3)^2 := by gcongr; exact hz 4
      _ ≤ 7 := by norm_num
  · calc
      _ ≤ |a| * |z 4|+2*|z 0*z 3-z 1*z 2| * |z 4|^4 * |z 0*z 2+z 1*z 3| := by
        have h := abs_sub (a*z 4) (2*(z 0*z 3-z 1*z 2)*z 4^4*(z 0*z 2+z 1*z 3))
        simp_rw [abs_mul, abs_pow] at h
        norm_num at h
        exact h
      _ ≤ (1:ℝ)*(4/3)+2*(32/9)*(4/3)^4*(32/9) := by gcongr <;> apply hz
      _ ≤ 82 := by norm_num

end GNC.PlanarAttitudeFrame
