import GNC.Dynamics.ForcedLogDynamics

/-! Remark 7's scalar ratio does not by itself establish dominance of the
actual thrust-attitude acceleration: the cross product can vanish at any
ratio when thrust and the attitude-error axis are aligned. -/
noncomputable section
open Matrix Real
open scoped Matrix
namespace GNC

def couplingRatio (l : ℝ) (a q p : Vec3) : ℝ := enorm a*enorm q/(l*enorm p)

/-- The ratio in (93) can be arbitrarily large while the actual coupling is
zero and the actual tidal action is nonzero, even at arbitrarily small θ. -/
theorem aligned_coupling_counterexample (k : Vec3) (hk : k ⬝ᵥ k = 1)
    (l ρ θ K : ℝ) (hl : 0 < l) (hρ : 0 < ρ) (hθ : 0 < θ) (hK : 1 < K) :
    couplingRatio l ((K*l*ρ/θ) • k) (θ • k) (ρ • k) = K ∧
    ((K*l*ρ/θ) • k) ⨯₃ (θ • k) = 0 ∧
    enorm (Gravity.radialMap l k (ρ • k)) = 2*l*ρ ∧
    0 < enorm (Gravity.radialMap l k (ρ • k)) := by
  have hcoef : 0 < K*l*ρ/θ := div_pos (mul_pos (mul_pos (by linarith) hl) hρ) hθ
  have hg : Gravity.radialMap l k (ρ • k) = (2*l*ρ) • k := by
    simp [Gravity.radialMap, hk, smul_sub, smul_smul]
    module
  have hgn : enorm (Gravity.radialMap l k (ρ • k)) = 2*l*ρ := by
    rw [hg, enorm_smul, Gravity.unit_enorm k hk, abs_of_pos (by positivity), mul_one]
  refine ⟨?_, ?_, hgn, by rw [hgn]; positivity⟩
  · simp only [couplingRatio, enorm_smul, Gravity.unit_enorm k hk, mul_one,
      abs_of_pos hcoef, abs_of_pos hθ, abs_of_pos hρ]
    field_simp
  · simp

/-- Equal, nonzero thrust along the attitude-error axis contributes no
attitude coupling to either translational row of the actual operator (72). -/
theorem aligned_thrust_no_coupling (μ : ℝ) (R : SO3) (chiefPos p v k w : Vec3) (a θ : ℝ) :
    forcedLinear μ R chiefPos (a • k) w (a • k) w ![p,v,θ • k] 1 =
      forcedLinear μ R chiefPos (a • k) w (a • k) w ![p,v,0] 1 := by
  simp [forcedLinear]

end GNC
