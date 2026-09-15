import GNC.Dynamics.OrbitalSymmetry

/-! A quantitative obstruction to rotating an orbit in a spinning atmosphere.
Gravity and radial density cancel exactly; only the atmospheric-spin mismatch
remains. This is an acceleration-defect bound, not a terminal-position bound.+-/
noncomputable section
namespace GNC.OrbitalSymmetry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem drag_difference (u v : E) :
    ‖QuadraticDrag.field u-QuadraticDrag.field v‖ ≤ (‖u‖+‖v‖)*‖u-v‖ := by
  have he : QuadraticDrag.field u-QuadraticDrag.field v =
      ‖u‖ • (u-v)+(‖u‖-‖v‖) • v := by
    unfold QuadraticDrag.field
    module
  rw [he]
  have h := norm_add_le (‖u‖ • (u-v)) ((‖u‖-‖v‖) • v)
  simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg u)] at h
  have hn := mul_le_mul_of_nonneg_right (abs_norm_sub_norm_le u v) (norm_nonneg v)
  nlinarith

/-- No commuting-spin hypothesis: its failure appears explicitly in the
bound as `‖spin (Q p)-Q (spin p)‖`. No gravity-gradient enclosure is needed
to bound this pointwise symmetry defect. -/
theorem acceleration_spin_defect (Q : E ≃ₗᵢ[ℝ] E) (μ κ H r₀ : ℝ)
    (spin : E →L[ℝ] E) (p v a : E) :
    ‖acceleration μ κ H r₀ spin (Q p) (Q v) (Q a)-
        Q (acceleration μ κ H r₀ spin p v a)‖ ≤
      |κ*Atmosphere.density H r₀ p| *
        (‖Q v-spin (Q p)‖+‖v-spin p‖)*‖spin (Q p)-Q (spin p)‖ := by
  have he : acceleration μ κ H r₀ spin (Q p) (Q v) (Q a)-
      Q (acceleration μ κ H r₀ spin p v a) =
      (-(κ*Atmosphere.density H r₀ p)) •
        (QuadraticDrag.field (Q v-spin (Q p))-QuadraticDrag.field (Q (v-spin p))) := by
    unfold acceleration
    rw [gravity_equivariant,density_invariant]
    simp only [map_add,map_sub,map_smul,← drag_equivariant]
    module
  have hd : (Q v-spin (Q p))-Q (v-spin p) = -(spin (Q p)-Q (spin p)) := by
    rw [map_sub]
    abel
  rw [he,norm_smul,Real.norm_eq_abs,abs_neg]
  have h := mul_le_mul_of_nonneg_left (drag_difference (Q v-spin (Q p)) (Q (v-spin p)))
    (abs_nonneg (κ*Atmosphere.density H r₀ p))
  simpa only [Q.norm_map,hd,norm_neg,mul_assoc] using h

/-- An approximate nominal retains its old defect, plus the separately
computed symmetry mismatch. A trajectory comparison theorem must still
propagate this acceleration budget before claiming an arrival tube. -/
theorem reused_acceleration_defect (Q : E ≃ₗᵢ[ℝ] E) (μ κ H r₀ : ℝ)
    (spin : E →L[ℝ] E) (p v a dv : E) :
    ‖Q dv-acceleration μ κ H r₀ spin (Q p) (Q v) (Q a)‖ ≤
      ‖dv-acceleration μ κ H r₀ spin p v a‖+
        |κ*Atmosphere.density H r₀ p| *
          (‖Q v-spin (Q p)‖+‖v-spin p‖)*‖spin (Q p)-Q (spin p)‖ := by
  have h := norm_sub_le_norm_sub_add_norm_sub (Q dv)
    (Q (acceleration μ κ H r₀ spin p v a))
    (acceleration μ κ H r₀ spin (Q p) (Q v) (Q a))
  rw [← map_sub,Q.norm_map] at h
  have hs := acceleration_spin_defect Q μ κ H r₀ spin p v a
  rw [norm_sub_rev] at hs
  exact h.trans (add_le_add le_rfl hs)

end GNC.OrbitalSymmetry
