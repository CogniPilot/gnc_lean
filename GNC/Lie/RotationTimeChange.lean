import GNC.Lie.RotationKinematics

/-! Actual angular derivatives of a rotation path under a scalar time change.
The clock acceleration term is needed when joining inertially fixed burns. -/
noncomputable section
set_option autoImplicit false
namespace GNC.RotationKinematics
open Matrix
open scoped Matrix Matrix.Norms.Operator

def Path.timeChange (p : Path) (clock rate acceleration : ℝ → ℝ) : Path where
  rotation t := p.rotation (clock t)
  velocity t := rate t • p.velocity (clock t)
  acceleration t := acceleration t • p.velocity (clock t)+rate t^2 • p.acceleration (clock t)

theorem Path.timeChange_jet (p : Path) {clock rate acceleration : ℝ → ℝ} {t : ℝ}
    (hp : p.HasJet (clock t)) (hc : HasDerivAt clock (rate t) t)
    (hr : HasDerivAt rate (acceleration t) t) :
    (p.timeChange clock rate acceleration).HasJet t := by
  constructor
  · convert hp.1.scomp t hc using 1
    simp [Path.timeChange, skew_smul]
  · convert hr.smul (hp.2.scomp t hc) using 1
    simp [Path.timeChange, smul_smul, pow_two, add_comm]

theorem Path.timeChange_continuous (p : Path) (hp : p.HasContinuousJet)
    {clock rate acceleration : ℝ → ℝ} (hc : Continuous clock)
    (hr : Continuous rate) (ha : Continuous acceleration) :
    (p.timeChange clock rate acceleration).HasContinuousJet :=
  ⟨hp.1.comp hc, hr.smul (hp.2.1.comp hc),
    (ha.smul (hp.2.1.comp hc)).add ((hr.pow 2).smul (hp.2.2.comp hc))⟩

theorem Path.timeChange_bounds (p : Path) (clock rate acceleration : ℝ → ℝ) (t : ℝ)
    {W A C D : ℝ} (hw : enorm (p.velocity (clock t)) ≤ W)
    (ha : enorm (p.acceleration (clock t)) ≤ A)
    (hc : |rate t| ≤ C) (hd : |acceleration t| ≤ D) :
    enorm ((p.timeChange clock rate acceleration).velocity t) ≤ C*W ∧
    enorm ((p.timeChange clock rate acceleration).acceleration t) ≤ D*W+C^2*A := by
  have hC := (abs_nonneg _).trans hc
  have hD := (abs_nonneg _).trans hd
  constructor
  · dsimp only [Path.timeChange]
    rw [enorm_smul]
    exact mul_le_mul hc hw (enorm_nonneg _) hC
  · apply (enorm_add_le _ _).trans
    simp only [enorm_smul, abs_pow]
    exact add_le_add (mul_le_mul hd hw (enorm_nonneg _) hD)
      (mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hc 2) ha (enorm_nonneg _)
        (sq_nonneg C))

theorem Path.timeChange_at_hold (p : Path) (clock rate acceleration : ℝ → ℝ) (t : ℝ)
    (hr : rate t = 0) (ha : acceleration t = 0) :
    (p.timeChange clock rate acceleration).velocity t = 0 ∧
      (p.timeChange clock rate acceleration).acceleration t = 0 := by
  simp [Path.timeChange, hr, ha]

end GNC.RotationKinematics
