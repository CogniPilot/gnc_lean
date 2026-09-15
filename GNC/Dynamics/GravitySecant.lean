import GNC.Dynamics.GravityGeometry

/-! An exact algebraic state-dependent coefficient for a central-gravity
increment. The coefficient is a scalar identity plus a rank-at-most-one
correction. There is no spatial Taylor truncation and no secant quadrature.
It still depends on the displaced state, so this is not a time propagator.
-/
noncomputable section
set_option autoImplicit false
namespace GNC.Gravity
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def secantCoefficient (μ r rho : ℝ) : ℝ :=
  μ*(rho^2+r*rho+r^2)/(r^3*rho^3*(rho+r))

/-- Algebraic factorization avoids dividing by the difference of radii,
so equal-radius displacements and the zero-displacement limit are included. -/
theorem inverse_cube_secant (μ r rho : ℝ) (hr : 0 < r) (hρ : 0 < rho) :
    μ/r^3-μ/rho^3 = secantCoefficient μ r rho*(rho^2-r^2) := by
  have hs : rho+r ≠ 0 := ne_of_gt (add_pos hρ hr)
  unfold secantCoefficient
  field_simp
  ring

def secantApply (μ : ℝ) (q d v : E) : E :=
  (-μ/‖q+d‖^3) • v+
    (secantCoefficient μ ‖q‖ ‖q+d‖*⟪(2:ℝ) • q+d,v⟫) • q

/-- Linear in the argument `v` for a fixed displacement parameter `d`.
Dependence on that parameter is precisely the remaining nonlinearity. -/
def secantMap (μ : ℝ) (q d : E) : E →ₗ[ℝ] E where
  toFun := secantApply μ q d
  map_add' u v := by simp [secantApply, inner_add_right, mul_add, add_smul, smul_add]; abel
  map_smul' c v := by
    simp only [secantApply, real_inner_smul_right, RingHom.id_apply,
      smul_add, smul_smul]
    module

/-- Exact gravity increment for arbitrary nonsingular endpoints. Unlike a
segment Taylor formula, this identity does not require the whole segment
to avoid the origin. That does not license physical collision trajectories. -/
theorem field_difference_secant (μ : ℝ) (q d : E)
    (hq : q ≠ 0) (hqd : q+d ≠ 0) :
    field μ (q+d)-field μ q = secantMap μ q d d := by
  have he : ‖q+d‖^2-‖q‖^2 = ⟪(2:ℝ) • q+d,d⟫ := by
    rw [norm_add_sq_real, inner_add_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq]
    ring
  rw [exact_radial_coefficients,
    inverse_cube_secant μ ‖q‖ ‖q+d‖ (norm_pos_iff.mpr hq) (norm_pos_iff.mpr hqd), he]
  rfl

/-- At zero displacement the exact coefficient is the actual gravity
gradient, including its radial term. No limiting quotient is required. -/
theorem secant_zero (μ : ℝ) (q v : E) (hq : q ≠ 0) :
    secantMap μ q 0 v = gradient μ q v := by
  have hn : ‖q‖ ≠ 0 := norm_ne_zero_iff.mpr hq
  change secantApply μ q 0 v = _
  simp only [secantApply, secantCoefficient, add_zero, real_inner_smul_left,
    gradient]
  match_scalars <;> field_simp <;> ring

/-- The correction to a scalar identity takes values in one fixed line.
This is the dimension-independent content of the rank-at-most-one claim. -/
theorem secant_correction_mem_span (μ : ℝ) (q d v : E) :
    secantMap μ q d v-(-μ/‖q+d‖^3) • v ∈ Submodule.span ℝ ({q} : Set E) := by
  change secantApply μ q d v-(-μ/‖q+d‖^3) • v ∈ _
  rw [secantApply, add_sub_cancel_left]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton q))

/-- The nonlinear coefficient construction respects spatial rotations (and
more generally real linear isometries). Cartesian implementations may use
the same exact factorization; no exclusive Lie-group efficiency is claimed. -/
theorem secant_isometry (μ : ℝ) (Q : E ≃ₗᵢ[ℝ] E) (q d v : E) :
    secantMap μ (Q q) (Q d) (Q v) = Q (secantMap μ q d v) := by
  change secantApply μ (Q q) (Q d) (Q v) = Q (secantApply μ q d v)
  simp only [secantApply, ← map_add, ← map_smul, Q.norm_map, Q.inner_map_map]

end GNC.Gravity
