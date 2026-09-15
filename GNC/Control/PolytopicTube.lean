import GNC.Control.Reachability
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! Common quadratic flow tubes from vertex inequalities.

The vertex certificate is stated as a quadratic-form inequality, equivalent
to the usual symmetric block LMI. Convex enclosure, the storage derivative,
and the nonlinear residual bound are explicit hypotheses. A numerical SDP
status is never used as a proof. The domain version quantifies only over
trajectories staying in the specified region; it does not assume an
unproved first-exit/continuation argument.
-/
noncomputable section
open Set Real
open scoped BigOperators
namespace GNC.PolytopicTube

variable {ι E W : Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]

def storage (P : E →L[ℝ] E) (x : E) : ℝ := inner ℝ x (P x)

/-- Continuous derivative of the actual quadratic storage; symmetry is
stated as an inner-product identity rather than an assumed derivative. -/
theorem storage_derivative (P : E →L[ℝ] E)
    (hP : ∀ x y, inner ℝ x (P y) = inner ℝ y (P x))
    {x : ℝ → E} {dx : E} {t : ℝ} (hx : HasDerivAt x dx t) :
    HasDerivAt (fun s => storage P (x s)) (2 * inner ℝ (x t) (P dx)) t := by
  simpa only [Function.comp_apply, storage, hP dx (x t), two_mul] using
    hx.inner ℝ (P.hasFDerivAt.comp_hasDerivAt t hx)

/-- Every convex combination inherits the common quadratic block LMI.
The weights may subsequently depend on time and state. -/
theorem vertex_supply (P : E →L[ℝ] E) (A : ι → E →L[ℝ] E)
    (B : W →L[ℝ] E) (w : ι → ℝ) (α μ : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1)
    (hvertex : ∀ i x d,
      2 * inner ℝ x (P (A i x + B d)) + α * storage P x ≤ μ * ‖d‖^2)
    (x : E) (d : W) :
    2 * inner ℝ x (P ((∑ i, w i • A i x) + B d)) + α * storage P x ≤
      μ * ‖d‖^2 := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    mul_le_mul_of_nonneg_left (hvertex i x d) (hw i))
  have hid : (∑ i, w i • (A i x + B d)) = (∑ i, w i • A i x) + B d := by
    simp only [smul_add, Finset.sum_add_distrib, ← Finset.sum_smul, hs, one_smul]
  rw [← hid]
  simp only [map_sum, map_smul, inner_sum, inner_smul_right]
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hs, one_mul] at h
  convert h using 1 <;> simp [Finset.mul_sum] <;> ring

/-- Geometry can remove a nonlinear term from a quadratic certificate
without claiming that the nonlinear vector field itself is linear. -/
theorem neutral_residual_supply (P : E →L[ℝ] E) (x f r : E)
    {α budget : ℝ} (h : 2 * inner ℝ x (P f) + α * storage P x ≤ budget)
    (hr : inner ℝ x (P r) = 0) :
    2 * inner ℝ x (P (f+r)) + α * storage P x ≤ budget := by
  simpa only [map_add, inner_add_right, hr, add_zero] using h

/-- A proved residual supply can be retained instead of discarded. -/
theorem residual_supply (P : E →L[ℝ] E) (x f r : E)
    {α budget ε : ℝ} (h : 2 * inner ℝ x (P f) + α * storage P x ≤ budget)
    (hr : 2 * inner ℝ x (P r) ≤ ε) :
    2 * inner ℝ x (P (f+r)) + α * storage P x ≤ budget + ε := by
  simp only [map_add, inner_add_right]
  linarith

/-- Universal finite-time flow tube for all admitted initial states and
disturbances. Regional validity is explicit in the trajectory predicate. -/
theorem reachable_tube (P : E →L[ℝ] E)
    (valid : (ℝ → E) → Prop) (f : ℝ → E → E)
    (domain : ℝ → Set E) {α budget ρ a b t : ℝ}
    (hα : α ≠ 0)
    (hP : ∀ x y, inner ℝ x (P y) = inner ℝ y (P x))
    (hvalid : ∀ x, valid x →
      (∀ s ∈ Icc a b, x s ∈ domain s) ∧
      (∀ s ∈ Icc a b, HasDerivAt x (f s (x s)) s))
    (hsupply : ∀ s ∈ Ico a b, ∀ x ∈ domain s,
      2 * inner ℝ x (P (f s x)) + α * storage P x ≤ budget)
    (ht : t ∈ Icc a b) :
    Reachability.reachable valid (Reachability.sublevel (storage P) ρ) a t ⊆
      Reachability.sublevel (storage P)
        (ρ * exp (-α*(t-a)) + (budget/α)*(1-exp (-α*(t-a)))) := by
  apply Reachability.sublevel_enclosure _ _ (exp_pos _).le
  intro x hx
  obtain ⟨hdom, hder⟩ := hvalid x hx
  exact Lyapunov.disturbed_bound_on hα
    (fun s hs => storage_derivative P hP (hder s hs))
    (fun s hs => by
      have h := hsupply s hs (x s) (hdom s ⟨hs.1, hs.2.le⟩)
      linarith) t ht

end GNC.PolytopicTube
