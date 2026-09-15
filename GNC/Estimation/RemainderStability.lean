import GNC.Control.Lyapunov
import Mathlib.Analysis.Calculus.MeanValue

/-! Quantitative local observer bounds from the actual nonlinear error ODE.

The quadratic and cubic remainder coefficients include both propagation and
correction. A cubic output approximation alone does not remove a quadratic
propagation remainder. The theorem uses a common dissipative error metric;
it does not assert that an arbitrary EKF or EqF satisfies its hypotheses.
The invariant ball is proved, not assumed along the trajectory. -/
noncomputable section
open Set Real
namespace GNC.Estimation.RemainderStability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def margin (α β γ R : ℝ) : ℝ := α-β*R-γ*R^2

theorem residual_dissipation (x linear remainder : E) {α β γ R : ℝ}
    (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hR : ‖x‖ ≤ R)
    (hlinear : inner ℝ x linear ≤ -α*‖x‖^2)
    (hremainder : ‖remainder‖ ≤ (β*‖x‖+γ*‖x‖^2)*‖x‖) :
    inner ℝ x (linear+remainder) ≤ -margin α β γ R*‖x‖^2 := by
  have hn := norm_nonneg x
  have hRsq : ‖x‖^2 ≤ R^2 := by nlinarith
  have hb := mul_le_mul_of_nonneg_left hR hβ
  have hg := mul_le_mul_of_nonneg_left hRsq hγ
  have hc : β*‖x‖+γ*‖x‖^2 ≤ β*R+γ*R^2 := add_le_add hb hg
  have hr := (real_inner_le_norm x remainder).trans
    (mul_le_mul_of_nonneg_left hremainder hn)
  have hm := mul_le_mul_of_nonneg_right hc (sq_nonneg ‖x‖)
  rw [inner_add_right]
  dsimp [margin]
  nlinarith

/-- A regional inward inequality suffices to prevent escape. Existence of
the differentiable trajectory on the stated finite interval is explicit. -/
theorem invariant_ball (f : ℝ → E → E) {x d : ℝ → E} {m R δ a b : ℝ}
    (hR : 0 < R) (hδ : δ < m*R)
    (hf : ∀ t ∈ Ico a b, ∀ y, ‖y‖ ≤ R → inner ℝ y (f t y) ≤ -m*‖y‖^2)
    (hd : ∀ t ∈ Ico a b, ‖d t‖ ≤ δ)
    (hx : ∀ t ∈ Icc a b, HasDerivAt x (f t (x t)+d t) t)
    (hinit : ‖x a‖ ≤ R) : ∀ t ∈ Icc a b, ‖x t‖ ≤ R := by
  have hder := fun t ht => (hx t ht).norm_sq
  have hb : ∀ t ∈ Icc a b, ‖x t‖^2 ≤ R^2 := by
    apply image_le_of_deriv_right_lt_deriv_boundary
      (fun t ht => (hder t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hder t ⟨ht.1,ht.2.le⟩).hasDerivWithinAt)
      (by nlinarith [norm_nonneg (x a)])
      (fun t => hasDerivAt_const t (R^2))
    intro t ht heq
    have he : ‖x t‖ = R := by nlinarith [norm_nonneg (x t)]
    have hlin := hf t ht (x t) he.le
    have hw := (real_inner_le_norm (x t) (d t)).trans
      (mul_le_mul_of_nonneg_left (hd t ht) (norm_nonneg (x t)))
    rw [inner_add_right]
    rw [he] at hlin hw
    nlinarith [mul_lt_mul_of_pos_left hδ hR]
  intro t ht
  have h := hb t ht
  nlinarith [norm_nonneg (x t)]

/-- Both the convergence region and the exponential rate are explicit.
The full vector-field remainder, not just the output residual, is bounded. -/
theorem exponential_bound (A : ℝ → E →L[ℝ] E) (r : ℝ → E → E)
    {x : ℝ → E} {α β γ R a b : ℝ}
    (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hR : 0 < R)
    (hm : 0 < margin α β γ R)
    (hA : ∀ t ∈ Ico a b, ∀ y, inner ℝ y (A t y) ≤ -α*‖y‖^2)
    (hr : ∀ t ∈ Ico a b, ∀ y, ‖y‖ ≤ R →
      ‖r t y‖ ≤ (β*‖y‖+γ*‖y‖^2)*‖y‖)
    (hx : ∀ t ∈ Icc a b, HasDerivAt x (A t (x t)+r t (x t)) t)
    (hinit : ‖x a‖ ≤ R) :
    ∀ t ∈ Icc a b, ‖x t‖ ≤ R ∧
      ‖x t‖^2 ≤ ‖x a‖^2*exp (-2*margin α β γ R*(t-a)) := by
  have hf : ∀ t ∈ Ico a b, ∀ y, ‖y‖ ≤ R →
      inner ℝ y (A t y+r t y) ≤ -margin α β γ R*‖y‖^2 := by
    intro t ht y hy
    exact residual_dissipation y (A t y) (r t y) hβ hγ hy (hA t ht y) (hr t ht y hy)
  have hin := invariant_ball (fun t y => A t y+r t y)
    (d := fun _ => 0) (δ := 0) hR (mul_pos hm hR) hf (by simp)
    (by simpa using hx) hinit
  have he := GNC.Lyapunov.exponential_bound_on
    (c := 2*margin α β γ R) (fun t ht => (hx t ht).norm_sq) (by
      intro t ht
      have h := hf t ht (x t) (hin t ⟨ht.1,ht.2.le⟩)
      nlinarith)
  intro t ht
  exact ⟨hin t ht, by simpa only [neg_mul] using he t ht⟩

/-- A bounded deterministic disturbance yields a certified ultimate error
radius delta/m. This is not a Gaussian mean-square or Riccati theorem. -/
theorem disturbed_bound (f : ℝ → E → E) {x d : ℝ → E} {m R δ a b : ℝ}
    (hm : 0 < m) (hR : 0 < R) (hδ : 0 ≤ δ) (hsmall : δ < m*R)
    (hf : ∀ t ∈ Ico a b, ∀ y, ‖y‖ ≤ R → inner ℝ y (f t y) ≤ -m*‖y‖^2)
    (hd : ∀ t ∈ Ico a b, ‖d t‖ ≤ δ)
    (hx : ∀ t ∈ Icc a b, HasDerivAt x (f t (x t)+d t) t)
    (hinit : ‖x a‖ ≤ R) :
    ∀ t ∈ Icc a b, ‖x t‖ ≤ R ∧
      ‖x t‖^2 ≤ ‖x a‖^2*exp (-m*(t-a))+
        (δ^2/m^2)*(1-exp (-m*(t-a))) := by
  have hin := invariant_ball f hR hsmall hf hd hx hinit
  have he := GNC.Lyapunov.disturbed_bound_on (c := m) (ε := δ^2/m) hm.ne'
    (fun t ht => (hx t ht).norm_sq) (by
      intro t ht
      have h := GNC.Lyapunov.disturbance_dissipation (x t) (f t (x t)) (d t)
        hm (hf t ht (x t) (hin t ⟨ht.1,ht.2.le⟩))
      have hs : ‖d t‖^2 ≤ δ^2 := by nlinarith [hd t ht, norm_nonneg (d t)]
      have hh := div_le_div_of_nonneg_right hs (by positivity : 0 ≤ 2*m)
      have hid : 2*(δ^2/(2*m)) = δ^2/m := by field_simp
      nlinarith)
  intro t ht
  refine ⟨hin t ht, ?_⟩
  convert he t ht using 1
  congr 1
  congr 1
  field_simp

/-- Removing only an output contribution improves this particular margin
if all other constants and the error metric are held fixed. -/
theorem margin_improvement (α βstate βoutput γ R : ℝ) :
    margin α βstate γ R-margin α (βstate+βoutput) 0 R =
      βoutput*R-γ*R^2 := by
  unfold margin
  ring

end GNC.Estimation.RemainderStability
