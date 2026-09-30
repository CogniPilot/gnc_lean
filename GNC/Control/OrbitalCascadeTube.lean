import GNC.Control.PolytopicResidualTube
import GNC.Control.DecayingSupplyTube
import GNC.Dynamics.GravityRemainderBall
import GNC.Dynamics.GravityGradientBound

/-! A dimension-independent acceleration-PD certificate for the translational
part of an attitude/translation cascade. The coordinates are x=e/L and
y=x+tau*edot/L, and the independent variable is t/tau. The actual reference
gradient is retained in the dynamics; only its storage contribution is bounded.
The gravity remainder is quadratic and vanishes at zero error. This module is
also a fair Cartesian baseline: no Lie-coordinate advantage is inferred.
-/
noncomputable section
open Set Real
namespace GNC.OrbitalCascadeTube
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def energy (x y : E) : ℝ := ‖x‖^2 + ‖y‖^2

omit [InnerProductSpace ℝ E] in
theorem energy_nonneg (x y : E) : 0 ≤ energy x y := by
  unfold energy
  positivity

/-- Exact completing-square identity for the normalized PD block. -/
theorem linear_identity (x y d : E) :
    2*inner ℝ x (-x+y)+2*inner ℝ y (-y+d)+energy x y/2-2*‖d‖^2 =
      -‖x-y‖^2-‖x‖^2/2-2*‖d-(1/2 : ℝ) • y‖^2 := by
  simp only [energy, norm_sub_sq_real, norm_smul, Real.norm_eq_abs,
    inner_add_right, inner_neg_right, inner_smul_right,
    real_inner_self_eq_norm_sq, real_inner_comm d y]
  norm_num
  ring

theorem linear_supply (x y d : E) :
    2*inner ℝ x (-x+y)+2*inner ℝ y (-y+d)+(1/2 : ℝ)*energy x y ≤
      2*‖d‖^2 := by
  have h := linear_identity x y d
  nlinarith [sq_nonneg ‖x-y‖, sq_nonneg ‖x‖, sq_nonneg ‖d-(1/2 : ℝ) • y‖]

/-- A gradient norm enclosure, valid for every direction rather than sampled
reference times, incurs only its gain in this structured storage. -/
theorem gradient_supply (x y Gx : E) {k : ℝ} (hk : 0 ≤ k)
    (hG : ‖Gx‖ ≤ k*‖x‖) :
    2*inner ℝ y Gx ≤ k*energy x y := by
  have h₁ := real_inner_le_norm y Gx
  have h₂ := mul_le_mul_of_nonneg_left hG (norm_nonneg y)
  have h₃ := mul_nonneg hk (sq_nonneg (‖x‖-‖y‖))
  dsimp [energy]
  nlinarith

/-- Direct storage estimation avoids an unnecessary condition-number factor. -/
theorem remainder_supply (x y r : E) {c R : ℝ}
    (hc : 0 ≤ c) (hx : ‖x‖ ≤ R) (hr : ‖r‖ ≤ c*‖x‖^2) :
    2*inner ℝ y r ≤ c*R*energy x y := by
  have hsector := PolytopicResidualTube.quadratic_sector x r hc hx hr
  exact gradient_supply x y r (mul_nonneg hc ((norm_nonneg x).trans hx)) hsector

theorem nonlinear_supply (x y Gx r d : E) {k c R : ℝ}
    (hk : 0 ≤ k) (hc : 0 ≤ c) (hx : ‖x‖ ≤ R)
    (hG : ‖Gx‖ ≤ k*‖x‖) (hr : ‖r‖ ≤ c*‖x‖^2) :
    2*inner ℝ x (-x+y)+2*inner ℝ y (-y+Gx+r+d)+
      (1/2-k-c*R)*energy x y ≤ 2*‖d‖^2 := by
  have h₁ := linear_supply x y d
  have h₂ := gradient_supply x y Gx hk hG
  have h₃ := remainder_supply x y r hc hx hr
  simp only [inner_add_right, inner_neg_right] at h₁ ⊢
  linarith

omit [InnerProductSpace ℝ E] in
theorem position_bound (x y : E) {R : ℝ} (hR : 0 ≤ R)
    (h : energy x y ≤ R^2) : ‖x‖ ≤ R := by
  dsimp [energy] at h
  nlinarith [sq_nonneg ‖y‖, norm_nonneg x]

/-- The PD correction has an exact squared acceleration gain of five. -/
theorem command_bound_sq (x y : E) : ‖x-(2 : ℝ) • y‖^2 ≤ 5*energy x y := by
  have h := sq_nonneg ‖(2 : ℝ) • x+y‖
  simp only [norm_add_sq_real, norm_smul, Real.norm_eq_abs,
    inner_smul_left] at h
  simp only [norm_sub_sq_real, norm_smul, Real.norm_eq_abs,
    inner_smul_right, energy]
  norm_num at h ⊢
  nlinarith

theorem energy_derivative {x y : ℝ → E} {Gx r d : E} {t : ℝ}
    (hx : HasDerivAt x (-x t+y t) t)
    (hy : HasDerivAt y (-y t+Gx+r+d) t) :
    HasDerivAt (fun s => energy (x s) (y s))
      (2*inner ℝ (x t) (-x t+y t)+2*inner ℝ (y t) (-y t+Gx+r+d)) t := by
  exact hx.norm_sq.add hy.norm_sq

/-- Nonlinear gravity tube: no trajectory containment is assumed in the
regional premises. Initial inclusion and a strict physical supply budget close
the region by first exit. Classical solution existence remains explicit. -/
theorem certificate (x y Gx r d : ℝ → E) {k c R δ a b : ℝ}
    (hk : 0 ≤ k) (hc : 0 ≤ c) (hR : 0 ≤ R) (hδ : 0 ≤ δ)
    (hdecay : 0 < 1/2-k-c*R)
    (hbudget : 2*δ^2 < (1/2-k-c*R)*R^2)
    (hinit : energy (x a) (y a) ≤ R^2)
    (hx : ∀ s ∈ Icc a b, HasDerivAt x (-x s+y s) s)
    (hy : ∀ s ∈ Icc a b, HasDerivAt y (-y s+Gx s+r s+d s) s)
    (hG : ∀ s ∈ Ico a b, ‖Gx s‖ ≤ k*‖x s‖)
    (hr : ∀ s ∈ Ico a b, energy (x s) (y s) ≤ R^2 → ‖r s‖ ≤ c*‖x s‖^2)
    (hd : ∀ s ∈ Ico a b, ‖d s‖ ≤ δ) :
    ∀ t ∈ Icc a b, energy (x t) (y t) ≤ R^2 ∧
      energy (x t) (y t) ≤ energy (x a) (y a)*exp (-(1/2-k-c*R)*(t-a))+
        (2*δ^2/(1/2-k-c*R))*(1-exp (-(1/2-k-c*R)*(t-a))) := by
  let V := fun s => energy (x s) (y s)
  let dv := fun s => 2*inner ℝ (x s) (-x s+y s)+
    2*inner ℝ (y s) (-y s+Gx s+r s+d s)
  have hder : ∀ s ∈ Icc a b, HasDerivAt V (dv s) s :=
    fun s hs => energy_derivative (hx s hs) (hy s hs)
  have hsupply : ∀ s ∈ Ico a b, V s ≤ R^2 →
      dv s+(1/2-k-c*R)*V s ≤ 2*δ^2 := by
    intro s hs hreg
    have h := nonlinear_supply (x s) (y s) (Gx s) (r s) (d s) hk hc
      (position_bound _ _ hR hreg) (hG s hs) (hr s hs hreg)
    have hsq : ‖d s‖^2 ≤ δ^2 := by nlinarith [hd s hs, norm_nonneg (d s)]
    exact h.trans (by linarith)
  have hinv : ∀ t ∈ Icc a b, V t ≤ R^2 := by
    apply image_le_of_deriv_right_lt_deriv_boundary
      (fun s hs => (hder s hs).continuousAt.continuousWithinAt)
      (fun s hs => (hder s ⟨hs.1,hs.2.le⟩).hasDerivWithinAt)
      hinit (fun s => hasDerivAt_const s (R^2))
    intro s hs he
    have h := hsupply s hs he.le
    rw [he] at h
    linarith
  have hb := Lyapunov.disturbed_bound_on (ε := 2*δ^2) hdecay.ne' hder (by
    intro s hs
    have h := hsupply s hs (hinv s ⟨hs.1,hs.2.le⟩)
    linarith)
  exact fun t ht => ⟨hinv t ht, hb t ht⟩

/-- Actual inverse-square gravity supplies the two physical coefficients. -/
theorem gravity_bounds [CompleteSpace E] (μ : ℝ) (hμ : 0 ≤ μ)
    (q e : E) {r D : ℝ} (hr : 0 < r) (hD : D < r)
    (hq : r ≤ ‖q‖) (he : ‖e‖ ≤ D) :
    ‖Gravity.gradient μ q e‖ ≤ (2*μ/r^3)*‖e‖ ∧
    ‖Gravity.field μ (q+e)-Gravity.field μ q-Gravity.gradient μ q e‖ ≤
      (3*μ/(r-D)^4)*‖e‖^2 := by
  constructor
  · apply (Gravity.gradient_bound μ hμ q e).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg e)
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (pow_le_pow_left₀ hr.le hq 3)
  · exact Gravity.remainder_quadratic μ hμ q e hD hq he

/-- Unit conversion for the actual gravity field, not an assumed normalized
residual. The domain radius D is physical; L scales position and tau time. -/
theorem scaled_gravity_bounds [CompleteSpace E] (μ : ℝ) (hμ : 0 ≤ μ)
    (q x : E) {r D L τ : ℝ} (hr : 0 < r) (hD : D < r) (hL : 0 < L)
    (hq : r ≤ ‖q‖) (hx : L*‖x‖ ≤ D) :
    ‖(τ^2/L) • Gravity.gradient μ q (L • x)‖ ≤ (2*μ*τ^2/r^3)*‖x‖ ∧
    ‖(τ^2/L) • (Gravity.field μ (q+L • x)-Gravity.field μ q-
        Gravity.gradient μ q (L • x))‖ ≤
      (3*μ*τ^2*L/(r-D)^4)*‖x‖^2 := by
  have hn : ‖L • x‖ = L*‖x‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hL]
  have h := gravity_bounds μ hμ q (L • x) hr hD hq (hn.trans_le hx)
  constructor
  · rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    have hb := mul_le_mul_of_nonneg_left h.1 (show 0 ≤ τ^2/L by positivity)
    rw [hn] at hb
    convert hb using 1 <;> field_simp <;> ring
  · rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    have hb := mul_le_mul_of_nonneg_left h.2 (show 0 ≤ τ^2/L by positivity)
    rw [hn] at hb
    convert hb using 1 <;> field_simp <;> ring

/-- Algebra of the physical feedback after scaling. The controller does
not cancel differential gravity; dg is carried into the normalized dynamics. -/
theorem physical_feedback_identity (e v dg f : E) {L τ : ℝ}
    (hL : L ≠ 0) (hτ : τ ≠ 0) :
    (τ/L) • v = -(L⁻¹ • e)+(L⁻¹ • (e+τ • v)) ∧
    (τ/L) • (v+τ • (-(τ^2)⁻¹ • e-(2/τ) • v+dg+f)) =
      -(L⁻¹ • (e+τ • v))+(τ^2/L) • dg+(τ^2/L) • f := by
  constructor <;> match_scalars <;> field_simp [hL, hτ] <;> ring

/-- The uniform budget first closes the nonlinear validity region. Within
that proved region, a decaying input supply yields the sharper envelope.
Both conclusions concern the same trajectories and the same regional gravity
bound; no second guessed tube or assumed containment is used. Time is normalized. -/
theorem transient_certificate (x y Gx r d : ℝ → E) {k c R δ ca S H T : ℝ}
    (hk : 0 ≤ k) (hc : 0 ≤ c) (hR : 0 ≤ R) (hδ : 0 ≤ δ)
    (hdecay : 0 < 1/2-k-c*R)
    (hne : (1/2-k-c*R)-ca ≠ 0)
    (hbudget : 2*δ^2 < (1/2-k-c*R)*R^2)
    (hinit : energy (x 0) (y 0) ≤ R^2)
    (hx : ∀ s ∈ Icc 0 T, HasDerivAt x (-x s+y s) s)
    (hy : ∀ s ∈ Icc 0 T, HasDerivAt y (-y s+Gx s+r s+d s) s)
    (hG : ∀ s ∈ Ico 0 T, ‖Gx s‖ ≤ k*‖x s‖)
    (hr : ∀ s ∈ Ico 0 T, energy (x s) (y s) ≤ R^2 → ‖r s‖ ≤ c*‖x s‖^2)
    (hd : ∀ s ∈ Ico 0 T, ‖d s‖ ≤ δ)
    (hds : ∀ s ∈ Ico 0 T, 2*‖d s‖^2 ≤ S+H*exp (-ca*s)) :
    ∀ t ∈ Icc 0 T, energy (x t) (y t) ≤ R^2 ∧
      energy (x t) (y t) ≤ DecayingSupplyTube.envelope
        (energy (x 0) (y 0)) (1/2-k-c*R) ca S H t := by
  have hreg := certificate x y Gx r d hk hc hR hδ hdecay hbudget
    hinit hx hy hG hr hd
  have hb := DecayingSupplyTube.bound (V := fun s => energy (x s) (y s))
    (S := S) (H := H) (T := T) hdecay.ne' hne (le_refl (energy (x 0) (y 0)))
    (fun s hs => energy_derivative (hx s hs) (hy s hs)) (by
      intro s hs
      have hinside := (hreg s ⟨hs.1,hs.2.le⟩).1
      have h := nonlinear_supply (x s) (y s) (Gx s) (r s) (d s) hk hc
        (position_bound _ _ hR hinside) (hG s hs) (hr s hs hinside)
      have hd' := hds s hs
      linarith)
  exact fun t ht => ⟨(hreg t ht).1, hb t ht⟩

end GNC.OrbitalCascadeTube
