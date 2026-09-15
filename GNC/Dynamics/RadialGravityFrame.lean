import GNC.Dynamics.GravityLinearization
import GNC.Dynamics.PlanarAttitudeFrame
import GNC.Dynamics.RotatingVariational
import GNC.Magnus.FixedAxis

/-! Exact radial-frame gravity and the fixed-axis orbital rotation.
The central-gravity derivative is diagonal in the reference RTN frame.
The frame motion is retained; eccentric motion includes angular acceleration.
The diagonal gravity block and fixed-axis rotation do not, by themselves,
make the coupled translational Magnus expansion terminate.
-/
noncomputable section
namespace GNC.RadialGravityFrame
open Matrix
open scoped Matrix.Norms.Operator

abbrev M3 := Matrix (Fin 3) (Fin 3) ℝ
def gravity (c : ℝ) : M3 := diagonal ![2*c,-c,-c]
def omega (w : ℝ) : M3 := skew ![0,0,w]
def referencePosition (r : ℝ) (R : SO3) : Vec3 := rotate R ![r,0,0]

/-- Retaining a Kepler baseline with a different gravitational parameter
requires this full correction; an effective reference parameter is not a
replacement for the physical gravity gradient. -/
theorem gravity_parameter_split (μ μ₀ r : ℝ) :
    gravity (μ/r^3) = gravity (μ₀/r^3)+gravity ((μ-μ₀)/r^3) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gravity] <;> ring

theorem log_generator_parameter_split (μ μ₀ r w : ℝ) :
    RotatingVariational.logGenerator (gravity (μ/r^3)) (omega w) =
      RotatingVariational.logGenerator (gravity (μ₀/r^3)) (omega w)+
        fromBlocks (0:M3) 0 (gravity ((μ-μ₀)/r^3)) 0 := by
  simp only [RotatingVariational.logGenerator,fromBlocks_add,add_zero]
  rw [gravity_parameter_split μ μ₀ r]

theorem reference_norm (r : ℝ) (hr : 0 < r) (R : SO3) :
    enorm (referencePosition r R) = r := by
  rw [referencePosition,rotate_enorm,RotationKinematics.x_axis_norm,abs_of_pos hr]

/-- Actual inverse-square derivative, not an assigned diagonal surrogate. -/
theorem gradient_diagonal (μ r : ℝ) (hr : 0 < r) (R : SO3) (v : Vec3) :
    rotate R⁻¹ (Gravity.gradient3 μ (referencePosition r R) (rotate R v)) =
      gravity (μ/r^3) *ᵥ v := by
  have hn := reference_norm r hr R
  have hunit : Jacobian.unitAxis (rotate R⁻¹ (referencePosition r R)) = ![1,0,0] := by
    simp only [referencePosition,← rotate_mul,inv_mul_cancel,rotate_one,Jacobian.unitAxis,
      RotationKinematics.x_axis_norm,abs_of_pos hr]
    ext i
    fin_cases i <;> simp [hr.ne']
  rw [Gravity.gradient3_body μ R _ v (by rw [hn]; exact hr),hunit,hn]
  ext i
  fin_cases i <;> simp [Gravity.radialMap,gravity,mulVec,dotProduct,Fin.sum_univ_succ,
    Matrix.vecHead,Matrix.vecTail] <;> ring

/-- The constructed radial position is the actual position of the existing
planar physical reference, so diagonalization is applicable to that model. -/
theorem planar_reference (w : Fin 4 → ℝ) (hr : 0 < PolynomialOrbit.radius w) :
    referencePosition (PolynomialOrbit.radius w) (PlanarAttitudeFrame.rotation w hr) =
      PolynomialOrbitTransition.position w := by
  ext i
  fin_cases i <;>
    simp [referencePosition,rotate,PlanarAttitudeFrame.rotation,
      PolynomialOrbitTransition.polynomialFrame,PolynomialOrbit.lift,
      PolynomialOrbitTransition.position,mulVec,dotProduct,Fin.sum_univ_succ,hr.ne']

/-- Full frame kinematics of the physical planar reference give exactly the
first Magnus term of its rotation, even while radius and angular speed vary. -/
theorem planar_rotation_exact (w : ℝ → Fin 4 → ℝ) (a : ℝ)
    (hr : ∀ t, 0 < PolynomialOrbit.radius (w t))
    (hw : ∀ t, HasDerivAt w (PolynomialOrbit.physicalRate a (w t)) t) :
    ∀ t, (PlanarAttitudeFrame.rotation (w t) (hr t)).val =
      (PlanarAttitudeFrame.rotation (w 0) (hr 0)).val *
        NormedSpace.exp (FixedAxisMagnus.phase
          (fun s => PlanarAttitudeFrame.spin (PolynomialOrbit.lift (w s))) t •
            skew ![0,0,1]) := by
  have hω : Continuous (fun t => PlanarAttitudeFrame.spin (PolynomialOrbit.lift (w t))) :=
    continuous_iff_continuousAt.mpr fun t =>
      (PlanarAttitudeFrame.physical_spin_derivative (hr t) (hw t)).continuousAt
  have h := FixedAxisMagnus.planar_rotation (fun t => PlanarAttitudeFrame.rotation (w t) (hr t))
    _ hω (fun t => PlanarAttitudeFrame.physical_derivative hr (hw t))
  simpa only [FixedAxisMagnus.z_exponential] using h

/-- The position equation completes the exact retained first-order system. -/
theorem transformed_position {R : ℝ → SO3} {d v : ℝ → Vec3} {w t : ℝ}
    (hR : HasDerivAt (fun s => (R s).val) ((R t).val*omega w) t)
    (hd : HasDerivAt d (v t) t) :
    HasDerivAt (fun s => rotate (R s)⁻¹ (d s))
      (rotate (R t)⁻¹ (v t)-omega w *ᵥ rotate (R t)⁻¹ (d t)) t := by
  simpa only [omega,skew_mulVec] using RotationKinematics.inverse_rotate_derivative hR hd

/-- Transform the actual retained physical ODE, including the forcing. -/
theorem transformed_velocity {R : ℝ → SO3} {v f d : ℝ → Vec3}
    {r μ w t : ℝ} (hr : 0 < r)
    (hR : HasDerivAt (fun s => (R s).val) ((R t).val*omega w) t)
    (hv : HasDerivAt v (Gravity.gradient3 μ (referencePosition r (R t)) (d t)+f t) t) :
    HasDerivAt (fun s => rotate (R s)⁻¹ (v s))
      (gravity (μ/r^3) *ᵥ rotate (R t)⁻¹ (d t) -
        omega w *ᵥ rotate (R t)⁻¹ (v t)+rotate (R t)⁻¹ (f t)) t := by
  have hg := gradient_diagonal μ r hr (R t) (rotate (R t)⁻¹ (d t))
  simp only [← rotate_mul,mul_inv_cancel,rotate_one] at hg
  convert RotationKinematics.inverse_rotate_derivative hR hv using 1
  rw [rotate_add,hg]
  simp only [omega,skew_mulVec]
  abel

/-- Radial/transverse split with centrifugal, Coriolis and Euler terms.
Setting c=w^2 and alpha=0 gives precisely the classical HCW blocks. -/
theorem classical_blocks (c w alpha : ℝ) :
    RotatingVariational.classicalGenerator (gravity c) (omega w) (omega alpha) =
      fromBlocks (0:M3) 1
        !![2*c+w^2,alpha,0; -alpha,-c+w^2,0; 0,0,-c]
        !![0,2*w,0; -2*w,0,0; 0,0,0] := by
  unfold RotatingVariational.classicalGenerator
  congr 1 <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [gravity,omega,skew,mul_apply,Fin.sum_univ_succ] <;> ring

/-- Reference rotation is exactly removable, but the remaining coupled
generators at different gravity magnitudes are not commuting matrices. -/
theorem coupled_commutator_entry (c₁ c₂ w₁ w₂ : ℝ) :
    let A₁ := RotatingVariational.logGenerator (gravity c₁) (omega w₁)
    let A₂ := RotatingVariational.logGenerator (gravity c₂) (omega w₂)
    (A₁*A₂-A₂*A₁) (Sum.inl 0) (Sum.inl 0) = 2*(c₂-c₁) := by
  simp [RotatingVariational.logGenerator,fromBlocks_multiply,gravity,omega,skew,
    mul_apply,Fin.sum_univ_succ]
  ring

theorem coupled_not_commuting {c₁ c₂ w₁ w₂ : ℝ} (hc : c₁ ≠ c₂) :
    ¬ Commute (RotatingVariational.logGenerator (gravity c₁) (omega w₁))
      (RotatingVariational.logGenerator (gravity c₂) (omega w₂)) := by
  intro h
  have he := coupled_commutator_entry c₁ c₂ w₁ w₂
  dsimp only at he
  rw [h.eq,sub_self] at he
  simp only [Matrix.zero_apply] at he
  exact hc (by linarith)

end GNC.RadialGravityFrame
