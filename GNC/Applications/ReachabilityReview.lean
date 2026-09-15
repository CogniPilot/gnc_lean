import Mathlib.Tactic

/-! Exact counterexamples to printed intermediate claims in reachability
papers. These do not assert that current CORA or JuliaReach code uses those
formulas. See the companion papers repository for sources and scope.
-/
namespace GNC.Applications.ReachabilityReview
open Set

/-- Althoff (2013), Corollary 1: squaring a Minkowski sum requires mixed
products. For S=T=[-1,1], the omitted-cross enclosure reaches only 2, whereas
the exact square of S+T contains 4. -/
theorem quadratic_split_missing_cross_terms :
    ¬ (∀ x ∈ Icc (-1:ℝ) 1, ∀ y ∈ Icc (-1:ℝ) 1,
      ∃ u ∈ Icc (-1:ℝ) 1, ∃ v ∈ Icc (-1:ℝ) 1, (x+y)^2 = u^2+v^2) := by
  intro h
  obtain ⟨u, hu, v, hv, he⟩ := h 1 (by norm_num) 1 (by norm_num)
  have hu2 : u^2 ≤ 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hu.2) (show 0 ≤ u+1 by linarith [hu.1])]
  have hv2 : v^2 ≤ 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hv.2) (show 0 ≤ v+1 by linarith [hv.1])]
  norm_num at he
  linarith

/-- Althoff (2013), Proposition 2: the displayed factor 1+phi is invalid
for negative phi. In dimension one, retained generator 1 and removed
generator -1 span [-2,2], but the displayed new generator is zero. -/
theorem generator_removal_needs_absolute_value :
    ¬ (∃ δ ∈ Icc (-1:ℝ) 1, (1:ℝ) + (-1)*(-1) = δ*(1+(-1))) := by
  norm_num

theorem repaired_generator_radius (β γ φ : ℝ) (hβ : |β| ≤ 1) (hγ : |γ| ≤ 1) :
    |β+γ*φ| ≤ 1+|φ| := by
  have hm : |γ*φ| ≤ |φ| := by
    rw [abs_mul]
    simpa using mul_le_mul_of_nonneg_right hγ (abs_nonneg φ)
  exact (abs_add_le _ _).trans (add_le_add hβ hm)

/-- Patel--Subbarao (2026), Proposition 1 as printed, needs f(0)=0
(or an added f(0) term). A smooth constant map is a counterexample otherwise. -/
theorem sdc_needs_origin_offset : ¬ ∃ A : ℝ → ℝ, ∀ x : ℝ, 1 = A x*x := by
  rintro ⟨A, h⟩
  simpa using h 0

/-- Equation (21)'s linearized matrix set is not an enclosure without a
remainder. A(x)=x^2 has A(0)=A'(0)=0, yet A(1)=1. This example also admits
the exact equilibrium SDC system f(x)=x^3, so it is separate from the
missing-origin-offset issue. -/
theorem matrix_taylor_needs_remainder :
    HasDerivAt (fun x : ℝ => x^2) 0 0 ∧
    (1:ℝ) ∈ Icc (-1:ℝ) 1 ∧
    ¬ (∃ ξ ∈ Icc (-1:ℝ) 1, (1:ℝ)^2 = 0+0*ξ) := by
  constructor
  · convert (hasDerivAt_id (0:ℝ)).pow 2 using 1
    norm_num
  · norm_num

end GNC.Applications.ReachabilityReview
