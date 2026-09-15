import GNC.Control.PolytopicTube
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Constant-metric incremental contraction and robust flow tubes.
These results compare two actual trajectories. Decay to one equilibrium is
not used as a substitute for the incremental dissipativity hypothesis.
-/
noncomputable section
open Set Real
namespace GNC.Contraction
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Fixed-metric contraction follows from a differential quadratic bound
on every point of each line segment. This is the constant-metric special
case; a variable metric needs its material derivative and geodesic analysis. -/
theorem differential_to_incremental (f : E → E) (A : E → E →L[ℝ] E)
    (P : E →L[ℝ] E) (domain : Set E) (k : ℝ)
    (hconv : Convex ℝ domain)
    (hf : ∀ x ∈ domain, HasFDerivAt f (A x) x)
    (hA : ∀ x ∈ domain, ∀ v,
      inner ℝ v (P (A x v)) ≤ -k * PolytopicTube.storage P v)
    {x y : E} (hx : x ∈ domain) (hy : y ∈ domain) :
    inner ℝ (x-y) (P (f x-f y)) ≤ -k * PolytopicTube.storage P (x-y) := by
  let v := x-y
  let path := fun s : ℝ => y+s • v
  have hp : ∀ s ∈ Icc (0:ℝ) 1, path s ∈ domain := by
    intro s hs
    have hm := hconv hy hx (sub_nonneg.mpr hs.2) hs.1 (by ring : 1-s+s=1)
    convert hm using 1
    dsimp [path, v]
    module
  have hpath : ∀ s, HasDerivAt path v s := by
    intro s
    simpa only [path, one_smul, zero_add] using
      (hasDerivAt_const s y).add ((hasDerivAt_id s).smul_const v)
  let φ := fun s => inner ℝ v (P (f (path s)))
  let dφ := fun s => inner ℝ v (P (A (path s) v))
  have hd : ∀ s ∈ Icc (0:ℝ) 1, HasDerivAt φ (dφ s) s := by
    intro s hs
    have h := (P.hasFDerivAt.comp_hasDerivAt s
      ((hf _ (hp s hs)).comp_hasDerivAt s (hpath s)))
    simpa [φ, dφ] using (hasDerivAt_const s v).inner ℝ h
  obtain ⟨c, hc, he⟩ := exists_hasDerivAt_eq_slope φ dφ (by norm_num : (0:ℝ)<1)
    (fun s hs => (hd s hs).continuousAt.continuousWithinAt)
    (fun s hs => hd s ⟨hs.1.le, hs.2.le⟩)
  have h := hA _ (hp c ⟨hc.1.le, hc.2.le⟩) v
  change dφ c ≤ _ at h
  rw [he] at h
  simpa [φ, path, v, map_sub, inner_sub_right] using h

/-- Incremental supply, including different disturbances on the two paths,
implies a tube about any admitted nominal trajectory. -/
theorem incremental_tube (P : E →L[ℝ] E) (domain : ℝ → Set E)
    (f : ℝ → E → E) {x y dx dy : ℝ → E} {α budget a b t : ℝ}
    (hα : α ≠ 0)
    (hP : ∀ u v, inner ℝ u (P v) = inner ℝ v (P u))
    (hx : ∀ s ∈ Icc a b, HasDerivAt x (f s (x s)+dx s) s)
    (hy : ∀ s ∈ Icc a b, HasDerivAt y (f s (y s)+dy s) s)
    (hdom : ∀ s ∈ Icc a b, x s ∈ domain s ∧ y s ∈ domain s)
    (hsupply : ∀ s ∈ Ico a b, ∀ u ∈ domain s, ∀ v ∈ domain s,
      2 * inner ℝ (u-v) (P (f s u-f s v+dx s-dy s)) +
        α * PolytopicTube.storage P (u-v) ≤ budget)
    (ht : t ∈ Icc a b) :
    PolytopicTube.storage P (x t-y t) ≤
      PolytopicTube.storage P (x a-y a)*exp (-α*(t-a)) +
      (budget/α)*(1-exp (-α*(t-a))) := by
  apply Lyapunov.disturbed_bound_on
    (V := fun s => PolytopicTube.storage P (x s-y s))
    (dV := fun s => 2 * inner ℝ (x s-y s)
      (P ((f s (x s)+dx s)-(f s (y s)+dy s)))) hα _ _ t ht
  · intro s hs
    exact PolytopicTube.storage_derivative P hP ((hx s hs).sub (hy s hs))
  · intro s hs
    have hm := hdom s ⟨hs.1, hs.2.le⟩
    have h := hsupply s hs (x s) hm.1 (y s) hm.2
    have he : (f s (x s)+dx s)-(f s (y s)+dy s) =
        f s (x s)-f s (y s)+dx s-dy s := by abel
    dsimp only
    rw [he]
    linarith

/-- A nonlinear residual with an incremental slope smaller than the
retained contraction margin preserves contraction. This separates an exact
geometric transport model from aerodynamic/servo/model residuals. -/
theorem residual_margin (P : E →L[ℝ] E) (f r : E → E)
    {k ell : ℝ} {x y : E}
    (hf : inner ℝ (x-y) (P (f x-f y)) ≤ -k*PolytopicTube.storage P (x-y))
    (hr : inner ℝ (x-y) (P (r x-r y)) ≤ ell*PolytopicTube.storage P (x-y)) :
    inner ℝ (x-y) (P ((f x+r x)-(f y+r y))) ≤
      -(k-ell)*PolytopicTube.storage P (x-y) := by
  rw [show (f x+r x)-(f y+r y) = (f x-f y)+(r x-r y) by abel]
  rw [map_add, inner_add_right]
  linarith

/-- Enclose the nonlinear residual after retaining a chosen reference
linear generator. This needs a differential bound throughout the convex
region, not just a Jacobian evaluation at its centre or vertices. -/
theorem reference_residual_supply (f : E → E) (Df : E → E →L[ℝ] E)
    (P Aref : E →L[ℝ] E) (region : Set E) (ell : ℝ)
    (hconv : Convex ℝ region)
    (hf : ∀ y ∈ region, HasFDerivAt f (Df y) y)
    (hres : ∀ y ∈ region, ∀ v,
      inner ℝ v (P ((Df y-Aref) v)) ≤ ell*PolytopicTube.storage P v)
    {x reference : E} (hx : x ∈ region) (hr : reference ∈ region) :
    inner ℝ (x-reference) (P (f x-f reference-Aref (x-reference))) ≤
      ell*PolytopicTube.storage P (x-reference) := by
  have h := differential_to_incremental (fun y => f y-Aref y)
    (fun y => Df y-Aref) P region (-ell) hconv
    (fun y hy => (hf y hy).sub Aref.hasFDerivAt)
    (fun y hy v => by simpa using hres y hy v) hx hr
  have he : (f x-Aref x)-(f reference-Aref reference) =
      f x-f reference-Aref (x-reference) := by
    rw [map_sub]
    abel
  simpa only [he, neg_neg] using h

end GNC.Contraction
