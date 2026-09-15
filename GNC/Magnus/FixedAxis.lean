import GNC.Magnus.MagnusFlow
import GNC.Lie.AxisRotation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Exact first Magnus term for a scalar function times a fixed generator.
This covers arbitrary time-varying angular speed about a fixed orbit normal.
It does not assert first-term exactness for changing rotation axes.
-/
noncomputable section
open MeasureTheory NormedSpace Matrix
open scoped Matrix.Norms.Operator
namespace GNC.FixedAxisMagnus

def phase (ω : ℝ → ℝ) (t : ℝ) : ℝ := ∫ s in 0..t, ω s

theorem phase_derivative (ω : ℝ → ℝ) (hω : Continuous ω) (t : ℝ) :
    HasDerivAt (phase ω) (ω t) t :=
  intervalIntegral.integral_hasDerivAt_right (hω.intervalIntegrable 0 t)
    hω.aestronglyMeasurable.stronglyMeasurableAtFilter hω.continuousAt

section Algebra
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

theorem cross_commutator (Z : A) (u v : ℝ) :
    (u • Z)*(v • Z)-(v • Z)*(u • Z) = 0 := by
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [mul_comm u v, sub_self]

theorem first_term (Z : A) (ω : ℝ → ℝ) (t : ℝ) :
    (∫ s in 0..t, ω s • Z) = phase ω t • Z := by
  exact intervalIntegral.integral_smul_const _ _

theorem right_derivative (Z : A) (ω : ℝ → ℝ) (hω : Continuous ω) (t : ℝ) :
    HasDerivAt (fun s => exp (phase ω s • Z))
      (exp (phase ω t • Z)*(ω t • Z)) t := by
  convert (hasDerivAt_exp_smul_const Z (phase ω t)).scomp t
    (phase_derivative ω hω t) using 1
  simp only [Function.comp_def, mul_smul_comm]

/-- The actual exponential of the first integral is the unique right flow,
for any initial value. No analytic Magnus tail is assumed to vanish. -/
theorem right_solution (Z : A) (ω : ℝ → ℝ) (hω : Continuous ω)
    (F : ℝ → A) (hF : ∀ t, HasDerivAt F (F t*(ω t • Z)) t) :
    ∀ t, F t = F 0*exp (phase ω t • Z) := by
  have he := Magnus.mixed_flow_unique (fun _ => 0) (fun t => ω t • Z)
    continuous_const (hω.smul continuous_const) F (fun t => F 0*exp (phase ω t • Z))
    (fun t => by simpa only [zero_mul, zero_add] using hF t)
    (fun t => by
      convert (right_derivative Z ω hω t).const_mul (F 0) using 1
      simp only [zero_mul,zero_add,mul_assoc]) (by simp [phase])
  exact fun t => congrFun he t

end Algebra

/-- The ordinary sine/cosine rotation is the actual mathlib exponential. -/
theorem z_exponential (t : ℝ) :
    AxisRotation.zMatrix t = exp (t • skew ![0,0,1]) := by
  have he := MixedInvariant.flow_unique (0 : Matrix (Fin 3) (Fin 3) ℝ) (skew ![0,0,1]) 1
    AxisRotation.zMatrix (fun s => by
      simpa only [zero_mul,zero_add,AxisRotation.zRotation] using
        AxisRotation.z_derivative (hasDerivAt_id s))
    (by simpa only [AxisRotation.zRotation] using
      congrArg Subtype.val AxisRotation.z_zero)
  simpa [MixedInvariant.flow] using congrFun he t

/-- Any actual planar frame with this angular-rate history has this exact
propagator. The rate need not be constant (eccentric and thrusting references
are allowed). Reference-frame hypotheses can be supplied by PlanarAttitudeFrame.
-/
theorem planar_rotation (R : ℝ → SO3) (ω : ℝ → ℝ) (hω : Continuous ω)
    (hR : ∀ t, HasDerivAt (fun s => (R s).val) ((R t).val*skew ![0,0,ω t]) t) :
    ∀ t, (R t).val = (R 0).val*AxisRotation.zMatrix (phase ω t) := by
  have hsk (t : ℝ) : skew ![0,0,ω t] = ω t • skew ![0,0,1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [skew]
  intro t
  rw [z_exponential]
  exact right_solution (skew ![0,0,1]) ω hω (fun s => (R s).val)
    (fun s => by simpa only [hsk] using hR s) t

end GNC.FixedAxisMagnus
