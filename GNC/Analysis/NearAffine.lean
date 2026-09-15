import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Tactic

/-! Certified comparison with a time-varying affine or mixed-invariant model.
The model residual and numerical/Magnus defect are separate budgets.
The proof reuses mathlib's approximate-trajectory Grönwall theorem.
-/
noncomputable section
open Set Metric
open scoped NNReal
namespace GNC.NearAffine
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Exact nonlinear trajectory versus approximate affine propagation.
The residual r may be state dependent; only its value along x is bounded
here. To obtain a computable certificate, establish that bound throughout
the admissible region, not just at the reference trajectory. -/
theorem affine_error_bound (A : ℝ → E →L[ℝ] E) (u r d : ℝ → E)
    {x y : ℝ → E} {K : ℝ≥0} {ρ εr εd a b : ℝ}
    (hA : ∀ t ∈ Ico a b, ‖A t‖ ≤ K)
    (hx : ∀ t ∈ Icc a b, HasDerivAt x (A t (x t)+u t+r t) t)
    (hy : ∀ t ∈ Icc a b, HasDerivAt y (A t (y t)+u t+d t) t)
    (hr : ∀ t ∈ Ico a b, ‖r t‖ ≤ εr)
    (hd : ∀ t ∈ Ico a b, ‖d t‖ ≤ εd)
    (h₀ : dist (x a) (y a) ≤ ρ) :
    ∀ t ∈ Icc a b, dist (x t) (y t) ≤ gronwallBound ρ K (εr+εd) (t-a) := by
  apply dist_le_of_approx_trajectories_ODE_of_mem
    (v := fun t z => A t z+u t) (s := fun _ => univ)
  · intro t ht
    have h : LipschitzWith K (fun z => A t z + u t) := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simpa only [dist_add_right] using
        ((A t).lipschitzWith_of_opNorm_le (hA t ht)).dist_le_mul x y
    exact h.lipschitzOnWith
  · intro t ht; exact (hx t ht).continuousAt.continuousWithinAt
  · intro t ht; exact (hx t ⟨ht.1,ht.2.le⟩).hasDerivWithinAt
  · intro t ht; simpa [dist_eq_norm] using hr t ht
  · simp
  · intro t ht; exact (hy t ht).continuousAt.continuousWithinAt
  · intro t ht; exact (hy t ⟨ht.1,ht.2.le⟩).hasDerivWithinAt
  · intro t ht; simpa [dist_eq_norm] using hd t ht
  · simp
  · exact h₀

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

theorem mixed_difference (M N X Y : A) :
    (M*X+X*N)-(M*Y+Y*N) = M*(X-Y)+(X-Y)*N := by noncomm_ring

theorem mixed_lipschitz {M N : A} {K : ℝ≥0} (h : ‖M‖+‖N‖ ≤ K) :
    LipschitzWith K (fun X => M*X+X*N) := by
  apply LipschitzWith.of_dist_le_mul
  intro X Y
  rw [dist_eq_norm, dist_eq_norm, mixed_difference]
  calc
    _ ≤ ‖M*(X-Y)‖+‖(X-Y)*N‖ := norm_add_le _ _
    _ ≤ ‖M‖*‖X-Y‖+‖X-Y‖*‖N‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = (‖M‖+‖N‖)*‖X-Y‖ := by ring
    _ ≤ K*‖X-Y‖ := mul_le_mul_of_nonneg_right h (norm_nonneg _)

/-- A nonlinear evolution close to M(t)X+XN(t), compared with any
approximation whose actual differential defect is bounded. M and N may
vary with time without commuting. No Magnus convergence claim is assumed. -/
theorem mixed_error_bound (M N u r d : ℝ → A)
    {x y : ℝ → A} {K : ℝ≥0} {ρ εr εd a b : ℝ}
    (hMN : ∀ t ∈ Ico a b, ‖M t‖+‖N t‖ ≤ K)
    (hx : ∀ t ∈ Icc a b, HasDerivAt x (M t*x t+x t*N t+u t+r t) t)
    (hy : ∀ t ∈ Icc a b, HasDerivAt y (M t*y t+y t*N t+u t+d t) t)
    (hr : ∀ t ∈ Ico a b, ‖r t‖ ≤ εr)
    (hd : ∀ t ∈ Ico a b, ‖d t‖ ≤ εd)
    (h₀ : dist (x a) (y a) ≤ ρ) :
    ∀ t ∈ Icc a b, dist (x t) (y t) ≤ gronwallBound ρ K (εr+εd) (t-a) := by
  apply dist_le_of_approx_trajectories_ODE_of_mem
    (v := fun t X => M t*X+X*N t+u t) (s := fun _ => univ)
  · intro t ht
    have h : LipschitzWith K (fun X => M t*X + X*N t + u t) := by
      apply LipschitzWith.of_dist_le_mul
      intro X Y
      simpa only [dist_add_right] using (mixed_lipschitz (hMN t ht)).dist_le_mul X Y
    exact h.lipschitzOnWith
  · intro t ht; exact (hx t ht).continuousAt.continuousWithinAt
  · intro t ht; exact (hx t ⟨ht.1,ht.2.le⟩).hasDerivWithinAt
  · intro t ht; simpa [dist_eq_norm] using hr t ht
  · simp
  · intro t ht; exact (hy t ht).continuousAt.continuousWithinAt
  · intro t ht; exact (hy t ⟨ht.1,ht.2.le⟩).hasDerivWithinAt
  · intro t ht; simpa [dist_eq_norm] using hd t ht
  · simp
  · exact h₀

end GNC.NearAffine
