import GNC.Dynamics.GravityField
import GNC.Dynamics.GravityLinearization
import GNC.Control.ThrustSupport
import GNC.Control.Propellant

/-! Physical orbital energy and pointing-dependent work. No assumption of
constant gravity or local linearization is used in the energy balance. -/
noncomputable section
open Matrix Real
open scoped RealInnerProductSpace
namespace GNC.OrbitalEnergy
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def specificEnergy (mu : ℝ) (p v : E) : ℝ := ‖v‖^2/2-mu/‖p‖

/-- Central gravity cancels exactly from the derivative of specific energy.
The remaining acceleration includes thrust, drag and every perturbation. -/
theorem energy_derivative {p v : ℝ → E} {mu t : ℝ} {a : E}
    (hp : HasDerivAt p (v t) t)
    (hv : HasDerivAt v (Gravity.field mu (p t)+a) t) (hz : p t ≠ 0) :
    HasDerivAt (fun s => specificEnergy mu (p s) (v s)) ⟪v t,a⟫ t := by
  have hn : ‖p t‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hpot := (hasDerivAt_const t mu).div (Gravity.norm_derivative hp hz) hn
  convert (hv.norm_sq.div_const 2).sub hpot using 1
  simp only [Gravity.field, inner_add_right, inner_smul_right, real_inner_comm (v t) (p t)]
  field_simp
  ring

/-- Unit-vector pointing geometry supplies a lower bound on actual thrust
power when the nominal thrust direction is the actual velocity direction. -/
theorem thrust_work_bound (R : SO3) (n q : Vec3) {speed accel kappa : ℝ}
    (hq : q ∈ ThrustSupport.Cap n kappa) (hs : 0 ≤ speed) (ha : 0 ≤ accel) :
    speed*accel*kappa ≤ (rotate R (speed • n)) ⬝ᵥ (rotate R (accel • q)) := by
  rw [rotate_dot]
  simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul]
  have h := mul_le_mul_of_nonneg_left hq.2 (mul_nonneg hs ha)
  nlinarith

/-- For a positive normalized work requirement, a cap gives a strictly
smaller sufficient command budget than its isotropic chord enclosure.
This scalar allocation result does not impose position/phase constraints. -/
theorem axial_budget_improves {demand delta : ℝ} (hd : 0 < demand)
    (hdelta : 0 < delta) (hsmall : delta < 1) :
    demand/(1-delta^2/2) < demand/(1-delta) := by
  have hb : 0 < 1-delta := by linarith
  have hden : 1-delta < 1-delta^2/2 := by nlinarith
  exact div_lt_div_of_pos_left hd hb hden

end GNC.OrbitalEnergy
