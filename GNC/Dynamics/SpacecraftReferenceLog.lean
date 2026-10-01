import GNC.Dynamics.MixedErrorDynamics
import GNC.Dynamics.GravityMismatch

/-! The reference-input/right-Jacobian convention of Theorem IV.1 in
the October 2026 technical note. The result starts from the physical
component equations, not an assumed error ODE. -/
noncomputable section
open Matrix Real NormedSpace
open scoped Matrix Matrix.Norms.Operator
namespace GNC

/-- Lemma 2: the actual exponential differential transports the clock
commutator, even though C is outside the SE₂(3) algebra. -/
theorem kinematic_exponential_identity (x : LogState) :
    hat (Jacobian.blockLeft x (![x 1,0,0] : LogState))*exp (hat x) =
      exp (hat x)*kinematicC-kinematicC*exp (hat x) := by
  have h0 : logDrift 0 x=(![x 1,0,0] : LogState) := by
    ext i j
    fin_cases i <;> simp [logDrift, ad]
  have hz : hat (0:LogState)=0 := hatLinear.map_zero
  simpa only [h0, hz, zero_add] using logDrift_differential 0 x

/-- Theorem IV.1 / Eq. (47), in precisely the reference-input convention.
All inputs are pointwise values and may vary with time. -/
theorem spacecraft_reference_log_equation {X Y : ℝ → SE23} {x : ℝ → LogState}
    {dx : LogState} {a w abar wbar g gbar : Vec3} {t : ℝ}
    (hX : SpacecraftODEAt X a w g t) (hY : SpacecraftODEAt Y abar wbar gbar t)
    (hx : HasDerivAt x dx t) (he : ∀ s, SE23.error (Y s) (X s)=groupExp (x s))
    (hθ : enorm (x t 2)<π) :
    dx = logDrift (Jacobian.controlInput abar wbar) (x t) +
      Jacobian.blockRightInverse (x t) (Jacobian.controlInput (a-abar) (w-wbar)) +
      velocityOnly (Jacobian.inverseAt (x t 2) (rotate (Y t).rot⁻¹ (g-gbar))) := by
  let ν := Jacobian.controlInput a w
  let νbar := Jacobian.controlInput abar wbar
  let du := Jacobian.controlInput (a-abar) (w-wbar)
  let gv := velocityOnly (rotate (Y t).rot⁻¹ (g-gbar))
  let E := exp (hat (x t))
  have hπ : enorm (x t 2)<2*π := by linarith [pi_pos]
  have h := matrix_error_derivative ((spacecraft_ode_iff _ _ _ _ _).mp hX)
    ((spacecraft_ode_iff _ _ _ _ _).mp hY)
  simp_rw [he, groupExp_toMatrix] at h
  have hdu : hat ν-hat νbar=hat du := by
    change hatLinear _-hatLinear _=_
    rw [←map_sub, controlInput_sub]
    rfl
  have hd : hat (Jacobian.blockLeft (x t) (Jacobian.blockRightInverse (x t) du))*E =
      E*hat du := by
    rw [left_right_differential, Jacobian.blockRight_inverse _ _ hπ]
  have hf : hat (Jacobian.blockLeft (x t) (Jacobian.blockRightInverse (x t) du)+gv)*E =
      E*hat du+hat gv*E := by
    change hatLinear _*E=_
    rw [map_add, Matrix.add_mul]
    change hat (Jacobian.blockLeft (x t) (Jacobian.blockRightInverse (x t) du))*E+
      hat gv*E = _
    rw [hd]
  have ht : HasDerivAt (fun s => exp (hat (x s)))
      (E*(hat νbar+kinematicC)-(hat νbar+kinematicC)*E+
        hat (Jacobian.blockLeft (x t) (Jacobian.blockRightInverse (x t) du)+gv)*E) t := by
    convert h using 1
    rw [hf]
    change _ = E*(hat ν+kinematicC)-(hat ν+kinematicC)*E+hatLinear _*E
    rw [map_add, map_sub]
    change _ = E*(hat ν+kinematicC)-(hat ν+kinematicC)*E+
      (hat ν-hat νbar+hat gv)*E
    have hh : hat du=hat ν-hat νbar := hdu.symm
    rw [hh]
    noncomm_ring
  have hl := log_error_equation hx hπ ht
  rw [blockInverse_add _ _ _ hπ, Jacobian.blockInverse_left_all _ _ hπ,
    Jacobian.blockInverse_velocityOnly] at hl
  simpa only [add_assoc] using hl

/-- Proposition 1 / Eq. (67), for trajectories' actual group error. -/
theorem spacecraft_gravity_mismatch_bound (μ : ℝ) (hμ : 0≤μ)
    (chief deputy : SE23) (x : LogState)
    (he : SE23.error chief deputy=groupExp x)
    (hp : enorm (x 0)<enorm chief.pos) (hθ : enorm (x 2)<π) :
    enorm (Jacobian.inverseAt (x 2) (rotate chief.rot⁻¹
      (Gravity.field3 μ deputy.pos-Gravity.field3 μ chief.pos))) ≤
      Gravity.inverseJacobianGain (enorm (x 2))*
        Gravity.mismatchBound μ (enorm chief.pos) (enorm (x 0)) := by
  rw [physical_separation chief deputy x he]
  exact Gravity.log_mismatch_bound μ hμ chief.rot chief.pos (x 0) (x 2) hp hθ

end GNC
