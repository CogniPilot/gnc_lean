import GNC.Dynamics.Atmosphere

/-! Exact reuse of orbital trajectories under a constant spatial isometry.

The initial position, initial velocity and thrust history all transform.
This is not a theorem about rotating only the thrust with fixed initial data.
Radial density is allowed. A fixed atmospheric spin must commute with the
chosen isometry; general plane rotations of a spinning atmosphere do not.
No numerical ephemeris or floating-point rotation is certified here.
-/
noncomputable section
namespace GNC.OrbitalSymmetry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
open scoped RealInnerProductSpace

/-- The axisymmetric J2 correction, with κ = 3 J2 μ R² / 2 and a unit
physical symmetry axis. Equivariance itself does not need normalization. -/
def j2 (κ : ℝ) (axis p : E) : E :=
  (κ / ‖p‖^5) • (((5*⟪axis,p⟫^2/‖p‖^2-1) • p) - (2*⟪axis,p⟫) • axis)

theorem j2_equivariant (Q : E ≃ₗᵢ[ℝ] E) (κ : ℝ) (axis p : E)
    (haxis : Q axis = axis) : j2 κ axis (Q p) = Q (j2 κ axis p) := by
  have hi : ⟪axis,Q p⟫ = ⟪axis,p⟫ := by
    simpa only [haxis] using Q.inner_map_map axis p
  simp only [j2, hi, Q.norm_map, map_smul, map_sub, haxis]

def acceleration (μ κ H r₀ : ℝ) (spin : E →L[ℝ] E) (p v a : E) : E :=
  Gravity.field μ p - (κ * Atmosphere.density H r₀ p) •
    QuadraticDrag.field (v - spin p) + a

theorem gravity_equivariant (Q : E ≃ₗᵢ[ℝ] E) (μ : ℝ) (p : E) :
    Gravity.field μ (Q p) = Q (Gravity.field μ p) := by
  simp [Gravity.field]

theorem density_invariant (Q : E ≃ₗᵢ[ℝ] E) (H r₀ : ℝ) (p : E) :
    Atmosphere.density H r₀ (Q p) = Atmosphere.density H r₀ p := by
  simp [Atmosphere.density]

theorem drag_equivariant (Q : E ≃ₗᵢ[ℝ] E) (v : E) :
    QuadraticDrag.field (Q v) = Q (QuadraticDrag.field v) := by
  simp [QuadraticDrag.field]

theorem acceleration_equivariant (Q : E ≃ₗᵢ[ℝ] E) (μ κ H r₀ : ℝ)
    (spin : E →L[ℝ] E) (hspin : ∀ p, spin (Q p) = Q (spin p)) (p v a : E) :
    acceleration μ κ H r₀ spin (Q p) (Q v) (Q a) =
      Q (acceleration μ κ H r₀ spin p v a) := by
  unfold acceleration
  rw [gravity_equivariant, density_invariant, hspin,
    ← Q.map_sub v (spin p), drag_equivariant]
  simp only [map_add, map_sub, map_smul]

/-- Pointwise in time, so the thrust and drag scale may vary with time,
including a prescribed variable-mass schedule. -/
theorem transformed_motion (Q : E ≃ₗᵢ[ℝ] E) (μ κ H r₀ : ℝ)
    (spin : E →L[ℝ] E) (hspin : ∀ p, spin (Q p) = Q (spin p))
    {p v : ℝ → E} {a : E} {t : ℝ}
    (hp : HasDerivAt p (v t) t)
    (hv : HasDerivAt v (acceleration μ κ H r₀ spin (p t) (v t) a) t) :
    HasDerivAt (fun s => Q (p s)) (Q (v t)) t ∧
    HasDerivAt (fun s => Q (v s))
      (acceleration μ κ H r₀ spin (Q (p t)) (Q (v t)) (Q a)) t := by
  constructor
  · exact Q.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hp
  · rw [acceleration_equivariant Q μ κ H r₀ spin hspin]
    exact Q.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hv

/-- The surviving rotations about the common gravity/atmosphere axis
also preserve the complete motion with a J2 correction. -/
theorem transformed_motion_j2 (Q : E ≃ₗᵢ[ℝ] E) (μ κ H r₀ J : ℝ)
    (axis : E) (haxis : Q axis = axis)
    (spin : E →L[ℝ] E) (hspin : ∀ p, spin (Q p) = Q (spin p))
    {p v : ℝ → E} {a : E} {t : ℝ}
    (hp : HasDerivAt p (v t) t)
    (hv : HasDerivAt v
      (acceleration μ κ H r₀ spin (p t) (v t) a + j2 J axis (p t)) t) :
    HasDerivAt (fun s => Q (p s)) (Q (v t)) t ∧
    HasDerivAt (fun s => Q (v s))
      (acceleration μ κ H r₀ spin (Q (p t)) (Q (v t)) (Q a) + j2 J axis (Q (p t))) t := by
  constructor
  · exact Q.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hp
  · rw [acceleration_equivariant Q μ κ H r₀ spin hspin, j2_equivariant Q J axis (p t) haxis,
      ← map_add]
    exact Q.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hv

/-- Reusing an approximate nominal transports its complete ODE defect
without amplification. Numerical evaluation of Q needs its own budget. -/
theorem acceleration_defect_norm (Q : E ≃ₗᵢ[ℝ] E) (μ κ H r₀ : ℝ)
    (spin : E →L[ℝ] E) (hspin : ∀ p, spin (Q p) = Q (spin p)) (p v a dv : E) :
    ‖Q dv - acceleration μ κ H r₀ spin (Q p) (Q v) (Q a)‖ =
      ‖dv - acceleration μ κ H r₀ spin p v a‖ := by
  rw [acceleration_equivariant Q μ κ H r₀ spin hspin, ← map_sub, Q.norm_map]

theorem certificate_reuse (Q : E ≃ₗᵢ[ℝ] E) (p q target : E) {ε : ℝ}
    (h : ‖p-q‖ ≤ ε) : ‖(Q p-target)-(Q q-target)‖ ≤ ε := by
  simpa only [sub_sub_sub_cancel_right, ← map_sub, Q.norm_map] using h

omit [InnerProductSpace ℝ E] in
/-- Known target thrust or drag does not alter the chaser approximation
error when both predictors subtract the identical target ephemeris. -/
theorem target_cancels (p q target : E) :
    (p-target)-(q-target) = p-q := by abel

omit [InnerProductSpace ℝ E] in
theorem ephemeris_budget (p q target targetApprox : E) {ε η : ℝ}
    (hp : ‖p-q‖ ≤ ε) (ht : ‖target-targetApprox‖ ≤ η) :
    ‖(p-target)-(q-targetApprox)‖ ≤ ε+η := by
  have he : (p-target)-(q-targetApprox) = (p-q)-(target-targetApprox) := by abel
  rw [he]
  exact (norm_sub_le _ _).trans (add_le_add hp ht)

end GNC.OrbitalSymmetry
