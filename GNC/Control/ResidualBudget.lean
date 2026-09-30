import GNC.Control.PolytopicResidualTube

/-! Scalar disturbance budgets for a fixed common quadratic certificate.
These optimize a sufficient bound, not the true robust stability margin.
The constants and the residual-validity domain must already be certified.
-/
noncomputable section
namespace GNC.ResidualBudget

/-- With rho = m R^2 and gamma = k R, this is nu delta^2's strict budget. -/
def budget (m α k R : ℝ) : ℝ := m * R^2 * (α - k*R)

/-- Exact factorization around the unconstrained maximizing radius. -/
theorem maximum_gap (m α k R : ℝ) (hk : k ≠ 0) :
    4*m*α^3/(27*k^2) - budget m α k R =
      m*k*(R - 2*α/(3*k))^2*(R + α/(3*k)) := by
  unfold budget
  field_simp
  ring

/-- A global upper bound on the sufficient budget over nonnegative radii. -/
theorem budget_le_maximum {m α k R : ℝ}
    (hm : 0 ≤ m) (hα : 0 ≤ α) (hk : 0 < k) (hR : 0 ≤ R) :
    budget m α k R ≤ 4*m*α^3/(27*k^2) := by
  have hid := maximum_gap m α k R hk.ne'
  have h : 0 ≤ m*k*(R - 2*α/(3*k))^2*(R + α/(3*k)) := by positivity
  linarith

/-- The upper bound is attained at R = 2 alpha / (3 k). -/
theorem budget_at_optimum (m α k : ℝ) (hk : k ≠ 0) :
    budget m α k (2*α/(3*k)) = 4*m*α^3/(27*k^2) := by
  have h := maximum_gap m α k (2*α/(3*k)) hk
  simp only [sub_self, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    mul_zero, zero_mul] at h
  linarith

/-- The sufficient budget increases up to its unconstrained maximizer. -/
theorem budget_mono_before_optimum {m α k x y : ℝ}
    (hm : 0 ≤ m) (hk : 0 ≤ k) (hx : 0 ≤ x) (hxy : x ≤ y)
    (hy : 3*k*y ≤ 2*α) : budget m α k x ≤ budget m α k y := by
  have hy0 : 0 ≤ y := hx.trans hxy
  have h₁ : 0 ≤ (y-x)*(y+2*x) := mul_nonneg (sub_nonneg.mpr hxy) (by positivity)
  have h₂ := mul_nonneg hk h₁
  have h₃ := mul_nonneg (by linarith : 0 ≤ 2*α-3*k*y)
    (show 0 ≤ y+x by positivity)
  have hf : 0 ≤ α*(y+x)-k*(y^2+y*x+x^2) := by nlinarith
  have h := mul_nonneg (mul_nonneg hm (sub_nonneg.mpr hxy)) hf
  unfold budget
  nlinarith

/-- A smaller proved residual loss gives a larger sufficient disturbance
budget, with all other certificate data and the radius held fixed. -/
theorem smaller_loss {m α k₁ k₂ R : ℝ} (hm : 0 ≤ m) (hk : k₁ ≤ k₂)
    (hR : 0 ≤ R) : budget m α k₂ R ≤ budget m α k₁ R := by
  unfold budget
  exact mul_le_mul_of_nonneg_left
    (sub_le_sub_left (mul_le_mul_of_nonneg_right hk hR) α) (by positivity)

/-- An exact normalized example: m=alpha=nu=R=1 and c=1/10, P=I
give gamma=1/5; delta=1/2 is strictly admissible. No vehicle is inferred. -/
theorem normalized_example :
    (0 : ℝ) < 1 - 1/5 ∧
    (1/2 : ℝ)^2 < budget 1 1 (1/5) 1 ∧
    ((1/2 : ℝ)^2 / (1 - 1/5)) = 5/16 := by
  norm_num [budget]

/-- Every scalar vertex with decay at least one has this exact supply.
Together with convexity this covers any time-varying decay in [1,2]. -/
theorem scalar_vertex_supply (x d k : ℝ) (hk : 1 ≤ k) :
    2*x*(-k*x+d)+x^2 ≤ d^2 := by
  have h := mul_nonneg (sub_nonneg.mpr hk) (sq_nonneg x)
  nlinarith [sq_nonneg (x-d)]

end GNC.ResidualBudget
