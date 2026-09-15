import GNC.Dynamics.OrbitalBarrier

/-! Exact inverse-square gravity with thrust along the instantaneous radius.
This is distinct from thrust fixed in a reference RTN frame. No gravity
Taylor approximation occurs in the energy or Sundman identities below. -/
noncomputable section
namespace GNC.RadialThrust
open OrbitalBarrier (momentumSq)
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def acceleration (a : ℝ) (p : E) : E := (a/‖p‖) • p
def energy (mu a : ℝ) (p v : E) : ℝ := OrbitalEnergy.specificEnergy mu p v-a*‖p‖

/-- The complete radial-thrust energy, not the Kepler energy, is conserved. -/
theorem energy_derivative {p v : ℝ → E} {mu a t : ℝ}
    (hp : HasDerivAt p (v t) t)
    (hv : HasDerivAt v (Gravity.field mu (p t)+acceleration a (p t)) t)
    (hz : p t ≠ 0) : HasDerivAt (fun s => energy mu a (p s) (v s)) 0 t := by
  convert (OrbitalEnergy.energy_derivative hp hv hz).sub
    ((Gravity.norm_derivative hp hz).const_mul a) using 1
  simp only [acceleration, inner_smul_right]
  rw [real_inner_comm]
  ring

theorem momentumSquared_derivative {p v : ℝ → E} {c t : ℝ}
    (hp : HasDerivAt p (v t) t) (hv : HasDerivAt v (c • p t) t) :
    HasDerivAt (fun s => momentumSq (p s) (v s)) 0 t := by
  convert ((hp.norm_sq.mul hv.norm_sq).sub ((hp.inner ℝ hv).pow 2)) using 1
  simp only [inner_smul_right, real_inner_self_eq_norm_sq,
    real_inner_comm (v t) (p t)]
  ring

/-- Physical radial velocity and a Sundman time `dt/dτ = r` turn the full
radial dynamics into a cubic energy equation. -/
theorem sundman_energy (mu a : ℝ) (p v : E) (hz : p ≠ 0) :
    ⟪p,v⟫^2 = 2*a*‖p‖^3 + 2*energy mu a p v*‖p‖^2 +
      2*mu*‖p‖ - momentumSq p v := by
  have hn : ‖p‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  unfold energy OrbitalEnergy.specificEnergy momentumSq
  field_simp
  ring

/-- Affine normalization of the cubic to Weierstrass form. -/
theorem weierstrass_cubic (a e mu h2 r : ℝ) :
    (a/2)^2*(2*a*r^3+2*e*r^2+2*mu*r-h2) =
      4*(a*r/2+e/6)^3 - (e^2/3-a*mu)*(a*r/2+e/6) -
        (-e^3/27+a*mu*e/6+a^2*h2/4) := by ring

end GNC.RadialThrust
