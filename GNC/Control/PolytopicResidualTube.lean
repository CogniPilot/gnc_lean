import GNC.Control.ReferenceTube
import GNC.Control.LMI

/-! Regional nonlinear BIBO tubes from common quadratic vertex certificates.

This composes the existing polytopic supply, actual storage derivative,
first-exit theorem and Grönwall bound. In contrast to `reachable_tube`,
membership in the certificate region is proved, not assumed. A quadratic
remainder becomes a sector on a specified ball; the decay lost to that
sector and the admissible disturbance budget are explicit. This theorem
does not assert feasibility for an uncontrolled orbital model or synthesize
a feedback law. Classical trajectory existence remains a hypothesis.
-/
noncomputable section
open Set Real
open scoped BigOperators
namespace GNC.PolytopicResidualTube
open PolytopicTube

variable {ι E W : Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]

omit [InnerProductSpace ℝ E] in
/-- Convert a quadratic residual to a sector only on the specified ball. -/
theorem quadratic_sector (x r : E) {c R : ℝ} (hc : 0 ≤ c)
    (hx : ‖x‖ ≤ R) (hr : ‖r‖ ≤ c * ‖x‖^2) :
    ‖r‖ ≤ (c*R)*‖x‖ := by
  have h := mul_le_mul_of_nonneg_left hx (mul_nonneg hc (norm_nonneg x))
  nlinarith

/-- Coercivity turns a norm-sector estimate into a storage supply bound. -/
theorem sector_supply (P : E →L[ℝ] E) (x r : E) {m ell : ℝ}
    (hm : 0 < m) (hell : 0 ≤ ell)
    (hcoerce : m*‖x‖^2 ≤ storage P x) (hr : ‖r‖ ≤ ell*‖x‖) :
    2*inner ℝ x (P r) ≤ (2*‖P‖*ell/m)*storage P x := by
  have h₁ := real_inner_le_norm x (P r)
  have h₂ := P.le_opNorm r
  have h₃ := mul_le_mul_of_nonneg_left hr (norm_nonneg P)
  have h₄ := mul_le_mul_of_nonneg_left (h₂.trans h₃) (norm_nonneg x)
  have h₅ := mul_le_mul_of_nonneg_left hcoerce
    (div_nonneg (by positivity : 0 ≤ 2*‖P‖*ell) hm.le)
  have hid : (2*‖P‖*ell/m)*(m*‖x‖^2) = 2*‖P‖*ell*‖x‖^2 := by
    field_simp
  rw [hid] at h₅
  nlinarith

/-- The energy sublevel is inside the residual's norm-validity region. -/
theorem sublevel_norm (P : E →L[ℝ] E) (x : E) {m R ρ : ℝ}
    (hm : 0 < m) (hR : 0 ≤ R)
    (hcoerce : m*‖x‖^2 ≤ storage P x)
    (hx : storage P x ≤ ρ) (hregion : ρ ≤ m*R^2) : ‖x‖ ≤ R := by
  have hs : ‖x‖^2 ≤ R^2 := by nlinarith
  nlinarith [norm_nonneg x]

/-- Regional quadratic gravity-like remainders have an explicit sector
loss. No actual-trajectory norm bound is supplied as a hypothesis. -/
theorem quadratic_supply (P : E →L[ℝ] E) (r : E → E)
    {m c R ρ : ℝ} (hm : 0 < m) (hc : 0 ≤ c) (hR : 0 ≤ R)
    (hcoerce : ∀ x, m*‖x‖^2 ≤ storage P x)
    (hregion : ρ ≤ m*R^2)
    (hr : ∀ x, ‖x‖ ≤ R → ‖r x‖ ≤ c*‖x‖^2) :
    ∀ x, storage P x ≤ ρ →
      2*inner ℝ x (P (r x)) ≤ (2*‖P‖*(c*R)/m)*storage P x := by
  intro x hx
  have hn := sublevel_norm P x hm hR (hcoerce x) hx hregion
  exact sector_supply P x (r x) hm (mul_nonneg hc hR) (hcoerce x)
    (quadratic_sector x (r x) hc hn (hr x hn))

/-- Vertex LMIs, a regional residual supply, and a strict computed inward
budget prove both invariance and a transient BIBO energy bound. The strict
condition is the actual dissipation margin, not an arbitrary tolerance.
Weights may be any time history (including one induced by the state). -/
theorem certificate (P : E →L[ℝ] E) (A : ι → E →L[ℝ] E)
    (B : W →L[ℝ] E) (weights : ℝ → ι → ℝ)
    (r : ℝ → E → E) (x : ℝ → E) (d : ℝ → W)
    {α γ μ δ ρ a b : ℝ}
    (hP : ∀ u v, inner ℝ u (P v) = inner ℝ v (P u))
    (hμ : 0 ≤ μ) (hδ : 0 ≤ δ) (hdecay : γ < α)
    (hbudget : μ*δ^2 < (α-γ)*ρ)
    (hinit : storage P (x a) ≤ ρ)
    (hw : ∀ s ∈ Ico a b, ∀ i, 0 ≤ weights s i)
    (hs : ∀ s ∈ Ico a b, ∑ i, weights s i = 1)
    (hd : ∀ s ∈ Ico a b, ‖d s‖ ≤ δ)
    (hvertex : ∀ i y u,
      2*inner ℝ y (P (A i y+B u))+α*storage P y ≤ μ*‖u‖^2)
    (hr : ∀ s ∈ Ico a b, ∀ y, storage P y ≤ ρ →
      2*inner ℝ y (P (r s y)) ≤ γ*storage P y)
    (hx : ∀ s ∈ Icc a b, HasDerivAt x
      ((∑ i, weights s i • A i (x s))+B (d s)+r s (x s)) s) :
    ∀ t ∈ Icc a b, storage P (x t) ≤ ρ ∧
      storage P (x t) ≤ storage P (x a)*exp (-(α-γ)*(t-a))+
        (μ*δ^2/(α-γ))*(1-exp (-(α-γ)*(t-a))) := by
  let V := fun t => storage P (x t)
  let dv := fun s => 2*inner ℝ (x s)
    (P ((∑ i, weights s i • A i (x s))+B (d s)+r s (x s)))
  have hder : ∀ s ∈ Icc a b, HasDerivAt V (dv s) s := by
    intro s hs'
    exact storage_derivative P hP (hx s hs')
  have hsupply : ∀ s ∈ Ico a b, V s ≤ ρ →
      dv s+(α-γ)*V s ≤ μ*δ^2 := by
    intro s hs' hreg
    have h := vertex_supply P A B (weights s) α μ (hw s hs') (hs s hs')
      hvertex (x s) (d s)
    have hres := hr s hs' (x s) hreg
    have hsq : ‖d s‖^2 ≤ δ^2 := by nlinarith [hd s hs', norm_nonneg (d s)]
    have hb := mul_le_mul_of_nonneg_left hsq hμ
    dsimp only [dv, V]
    simp only [map_add, inner_add_right] at h ⊢
    linarith
  have hinvariant : ∀ t ∈ Icc a b, V t ≤ ρ := by
    apply image_le_of_deriv_right_lt_deriv_boundary
      (fun s hs' => (hder s hs').continuousAt.continuousWithinAt)
      (fun s hs' => (hder s ⟨hs'.1,hs'.2.le⟩).hasDerivWithinAt)
      hinit (fun s => hasDerivAt_const s ρ)
    intro s hs' he
    have h := hsupply s hs' he.le
    rw [he] at h
    linarith
  have hbound := Lyapunov.disturbed_bound_on (ε := μ*δ^2)
    (sub_pos.mpr hdecay).ne' hder (by
    intro s hs'
    have h := hsupply s hs' (hinvariant s ⟨hs'.1,hs'.2.le⟩)
    linarith)
  exact fun t ht => ⟨hinvariant t ht, hbound t ht⟩

/-- A physical output Lipschitz gain gives a bounded output from the
proved sublevel. `recover` may be nonlinear, including a geometric map,
but its gain must be established on this entire region. -/
theorem output_bound {V : Type*} [NormedAddCommGroup V]
    (P : E →L[ℝ] E) (recover : E → V) (x : E)
    {m R ρ L : ℝ} (hm : 0 < m) (hR : 0 ≤ R) (hL : 0 ≤ L)
    (hcoerce : m*‖x‖^2 ≤ storage P x) (hx : storage P x ≤ ρ)
    (hregion : ρ ≤ m*R^2)
    (hout : ∀ y, ‖y‖ ≤ R → ‖recover y‖ ≤ L*‖y‖) :
    ‖recover x‖ ≤ L*R := by
  have hn := sublevel_norm P x hm hR hcoerce hx hregion
  exact (hout x hn).trans (mul_le_mul_of_nonneg_left hn hL)

end GNC.PolytopicResidualTube
