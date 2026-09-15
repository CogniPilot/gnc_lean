import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-! Propellant conversion for constant exhaust speed and commanded physical
acceleration magnitude. Thrust follows mass, T=m*a. The model does not charge
reaction-wheel electrical power or additional attitude-control propellant.
-/
noncomputable section
open Real
namespace GNC.Propellant

def remainingMass (m₀ exhaust impulse : ℝ) : ℝ := m₀*exp (-impulse/exhaust)
def consumedMass (m₀ exhaust impulse : ℝ) : ℝ := m₀-remainingMass m₀ exhaust impulse

theorem mass_derivative {J : ℝ → ℝ} {a t m₀ exhaust : ℝ}
    (hJ : HasDerivAt J a t) :
    HasDerivAt (fun s => remainingMass m₀ exhaust (J s))
      (-a/exhaust*remainingMass m₀ exhaust (J t)) t := by
  convert ((hJ.neg.div_const exhaust).exp).const_mul m₀ using 1
  dsimp [remainingMass]
  ring

theorem mass_positive {m₀ exhaust impulse : ℝ} (hm : 0 < m₀) :
    0 < remainingMass m₀ exhaust impulse := mul_pos hm (exp_pos _)

/-- Minimizing physical accumulated acceleration is equivalent in ordering
to minimizing propellant under this mass-flow model. -/
theorem consumed_mono {m₀ exhaust J K : ℝ} (hm : 0 ≤ m₀)
    (he : 0 < exhaust) (hJK : J ≤ K) :
    consumedMass m₀ exhaust J ≤ consumedMass m₀ exhaust K := by
  have h := exp_le_exp.mpr (div_le_div_of_nonneg_right (neg_le_neg hJK) he.le)
  have hh := mul_le_mul_of_nonneg_left h hm
  dsimp [consumedMass, remainingMass]
  linarith

theorem consumed_nonneg {m₀ exhaust J : ℝ} (hm : 0 ≤ m₀)
    (he : 0 < exhaust) (hJ : 0 ≤ J) : 0 ≤ consumedMass m₀ exhaust J := by
  simpa [consumedMass, remainingMass] using consumed_mono hm he hJ

theorem consumed_strictMono {m₀ exhaust : ℝ} (hm : 0 < m₀) (he : 0 < exhaust) :
    StrictMono (consumedMass m₀ exhaust) := by
  intro J K hJK
  have h := exp_lt_exp.mpr ((div_lt_div_iff_of_pos_right he).mpr (neg_lt_neg hJK))
  have hh := mul_lt_mul_of_pos_left h hm
  dsimp [consumedMass, remainingMass]
  linarith

/-- The initial-mass acceleration limit enforces the actual thrust limit
throughout a nonnegative accumulated-acceleration schedule. -/
theorem thrust_limit {m₀ exhaust J a limit : ℝ} (hm : 0 ≤ m₀)
    (he : 0 < exhaust) (hJ : 0 ≤ J) (ha : 0 ≤ a) (hlimit : m₀*a ≤ limit) :
    remainingMass m₀ exhaust J*a ≤ limit := by
  have h := consumed_nonneg hm he hJ
  dsimp [consumedMass] at h
  exact (mul_le_mul_of_nonneg_right (by linarith : remainingMass m₀ exhaust J ≤ m₀) ha).trans hlimit

theorem inverse_mass_ratio {m₀ exhaust J : ℝ} (hm : m₀ ≠ 0) :
    m₀/remainingMass m₀ exhaust J = exp (J/exhaust) := by
  simp [remainingMass, div_mul_eq_div_div, hm, neg_div, exp_neg]

/-- The maximum scheduled physical delta-v supplies the inverse-mass
envelope used by the atmospheric remainder bound. -/
theorem inverse_mass_change_bound {m₀ exhaust J maximum : ℝ}
    (hm : m₀ ≠ 0) (he : 0 < exhaust) (hJ : 0 ≤ J) (hmax : J ≤ maximum) :
    0 ≤ m₀/remainingMass m₀ exhaust J-1 ∧
      m₀/remainingMass m₀ exhaust J-1 ≤ exp (maximum/exhaust)-1 := by
  rw [inverse_mass_ratio hm]
  have hlo := exp_le_exp.mpr (div_nonneg hJ he.le)
  have hhi := exp_le_exp.mpr (div_le_div_of_nonneg_right hmax he.le)
  simp only [exp_zero] at hlo
  exact ⟨by linarith, by linarith⟩

end GNC.Propellant
