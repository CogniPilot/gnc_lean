import GNC.Control.ReferenceDisturbance
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Force-commanded propulsion with changing mass.

The force is the net thrust, including exhaust momentum and nozzle pressure;
it is not a force on a closed, constant-mass body. Positive remaining mass is
explicit. These results complement `Control.Propellant`, whose command is
acceleration and whose required force follows the decreasing mass.
-/
noncomputable section
open Matrix Real
namespace GNC.VariableMassThrust

/-- Reciprocal mass has an exact polynomial differential lift. If mass flow
is a polynomial input/state, adding this scalar preserves a polynomial ODE.
This identity is exact; it is not a truncated expansion of 1/m. -/
theorem inverse_mass_derivative {m : ℝ → ℝ} {flow t : ℝ}
    (hm : HasDerivAt m (-flow) t) (hpos : 0 < m t) :
    HasDerivAt (fun s => (m s)⁻¹) (flow*((m t)⁻¹)^2) t := by
  convert hm.inv hpos.ne' using 1
  field_simp

/-- The rocket-equation primitive differentiates to the actual acceleration
magnitude for a force command and constant effective exhaust speed. It does
not equate accumulated scalar acceleration to an orbital velocity vector. -/
theorem accumulated_acceleration_derivative {m : ℝ → ℝ} {F exhaust t : ℝ}
    (hm : HasDerivAt m (-F/exhaust) t) (hpos : 0 < m t) (he : exhaust ≠ 0) :
    HasDerivAt (fun s => -exhaust*log (m s)) (F/m t) t := by
  convert (hm.log hpos.ne').const_mul (-exhaust) using 1
  field_simp

/-- A prescribed consumed-mass history has a positive remaining mass exactly
when the declared reserve is respected. -/
theorem remaining_mass_positive {m₀ consumed reserve : ℝ}
    (hr : 0 < reserve) (hbudget : consumed ≤ m₀-reserve) :
    0 < m₀-consumed ∧ reserve ≤ m₀-consumed := by
  constructor <;> linarith

theorem force_mass_error_split {F F₀ m m₀ : ℝ} (hm : m ≠ 0) (hm₀ : m₀ ≠ 0) :
    F/m-F₀/m₀ = (F-F₀)/m+F₀*(m₀-m)/(m*m₀) := by
  field_simp
  ring

/-- Joint force/mass uncertainty, without an independence assumption.
The denominator is a physical mass reserve shared by actual and reference. -/
theorem force_mass_error_bound {F F₀ m m₀ reserve forceError massError : ℝ}
    (hr : 0 < reserve) (hm : reserve ≤ m) (hm₀ : reserve ≤ m₀)
    (hF : |F-F₀| ≤ forceError) (hM : |m-m₀| ≤ massError) :
    |F/m-F₀/m₀| ≤ forceError/reserve+|F₀| *massError/reserve^2 := by
  have hmp := hr.trans_le hm
  have hm₀p := hr.trans_le hm₀
  rw [force_mass_error_split hmp.ne' hm₀p.ne']
  apply (abs_add_le _ _).trans
  simp only [abs_div, abs_mul, abs_of_pos hmp, abs_of_pos hm₀p, abs_sub_comm m₀ m]
  apply add_le_add
  · exact (div_le_div_of_nonneg_right hF hmp.le).trans
      (div_le_div_of_nonneg_left ((abs_nonneg _).trans hF) hr hm)
  · have hden : reserve^2 ≤ m*m₀ := by
      nlinarith [mul_le_mul hm hm₀ hr.le hmp.le]
    exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hM (abs_nonneg F₀))
      (mul_nonneg hmp.le hm₀p.le)).trans
        (div_le_div_of_nonneg_left (mul_nonneg (abs_nonneg F₀) ((abs_nonneg _).trans hM))
          (sq_pos_of_pos hr) hden)

/-- A physical acceleration envelope combining force, mass, and all-axis
pointing uncertainty. Correlated disturbances are allowed by these bounds. -/
theorem pointing_force_mass_error (n q : Vec3) {F F₀ m m₀ reserve forceError massError α : ℝ}
    (hn : n ⬝ᵥ n = 1) (hq : q ∈ ThrustSupport.Cap n (cos α))
    (hr : 0 < reserve) (hm : reserve ≤ m) (hm₀ : reserve ≤ m₀) (hF₀ : 0 ≤ F₀)
    (hF : |F-F₀| ≤ forceError) (hM : |m-m₀| ≤ massError)
    (hα : 0 ≤ α) (hπ : α ≤ π) :
    enorm ((F/m) • q-(F₀/m₀) • n) ≤
      forceError/reserve+|F₀| *massError/reserve^2+2*(F₀/m₀)*sin (α/2) := by
  exact ThrustSupport.magnitude_pointing_error n q hn hq
    (div_nonneg hF₀ (hr.trans_le hm₀).le) hα hπ
    (force_mass_error_bound hr hm hm₀ hF hM)

/-- Quantify the acceleration bias caused by freezing mass at ignition.
The fractional depletion f is an input assumption, not a numerical tolerance. -/
theorem frozen_mass_relative_error {F m₀ f : ℝ} (hF : F ≠ 0) (hm : m₀ ≠ 0)
    (hf : f < 1) :
    (F/(m₀*(1-f))-F/m₀)/(F/m₀) = f/(1-f) := by
  have h : 1-f ≠ 0 := by linarith
  field_simp <;> ring

end GNC.VariableMassThrust
