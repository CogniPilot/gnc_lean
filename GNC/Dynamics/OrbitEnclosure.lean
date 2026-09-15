import GNC.Dynamics.OrbitalEnergy

/-! Mapping a joint position/velocity enclosure to orbital invariants.
These are uniform finite-error bounds, not linearizations of orbital elements.
They apply away from the gravity singularity and avoid circular/equatorial
singularities of classical angular orbital elements. -/
noncomputable section
open Real Matrix
open scoped RealInnerProductSpace
namespace GNC.OrbitEnclosure
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem potential_bound (p dp : E) {mu P : ℝ} (hmu : 0 ≤ mu)
    (hp : ‖dp‖ ≤ P) (hsmall : P < ‖p‖) :
    |mu/‖p+dp‖-mu/‖p‖| ≤ mu*P/(‖p‖*(‖p‖-P)) := by
  have hP : 0 ≤ P := (norm_nonneg _).trans hp
  have hr : 0 < ‖p‖ := lt_of_le_of_lt hP hsmall
  have hd : |‖p+dp‖-‖p‖| ≤ P :=
    (by simpa using abs_norm_sub_norm_le (p+dp) p : |‖p+dp‖-‖p‖| ≤ ‖dp‖).trans hp
  have hl : ‖p‖-P ≤ ‖p+dp‖ := by linarith [(abs_le.mp hd).1]
  have hr' : 0 < ‖p+dp‖ := lt_of_lt_of_le (sub_pos.mpr hsmall) hl
  have he : mu/‖p+dp‖-mu/‖p‖ = mu*(‖p‖-‖p+dp‖)/(‖p‖*‖p+dp‖) := by
    field_simp
  rw [he, abs_div, abs_mul, abs_of_nonneg hmu, abs_of_pos (mul_pos hr hr'), abs_sub_comm]
  exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hd hmu)
    (mul_nonneg hr.le hr'.le)).trans
    (div_le_div_of_nonneg_left (mul_nonneg hmu hP) (mul_pos hr (sub_pos.mpr hsmall))
      (mul_le_mul_of_nonneg_left hl hr.le))

theorem energy_bound (p v dp dv : E) {mu P V : ℝ} (hmu : 0 ≤ mu)
    (hp : ‖dp‖ ≤ P) (hv : ‖dv‖ ≤ V) (hsmall : P < ‖p‖) :
    |OrbitalEnergy.specificEnergy mu (p+dp) (v+dv)-OrbitalEnergy.specificEnergy mu p v| ≤
      ‖v‖*V+V^2/2+mu*P/(‖p‖*(‖p‖-P)) := by
  have hV : 0 ≤ V := (norm_nonneg _).trans hv
  have hi : |inner ℝ v dv| ≤ ‖v‖*V := (abs_real_inner_le_norm v dv).trans
    (mul_le_mul_of_nonneg_left hv (norm_nonneg _))
  have hv2 : ‖dv‖^2 ≤ V^2 := by nlinarith [norm_nonneg dv]
  have he : OrbitalEnergy.specificEnergy mu (p+dp) (v+dv)-OrbitalEnergy.specificEnergy mu p v =
      (inner ℝ v dv+‖dv‖^2/2)-(mu/‖p+dp‖-mu/‖p‖) := by
    simp only [OrbitalEnergy.specificEnergy, norm_add_sq_real]
    ring
  rw [he]
  have hkin : |inner ℝ v dv+‖dv‖^2/2| ≤ ‖v‖*V+V^2/2 := by
    have hh := abs_add_le (inner ℝ v dv) (‖dv‖^2/2)
    rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖dv‖^2/2)] at hh
    linarith
  exact (abs_sub _ _).trans (add_le_add hkin (potential_bound p dp hmu hp hsmall))

theorem momentum_bound (p v dp dv : Vec3) {P V : ℝ}
    (hp : enorm dp ≤ P) (hv : enorm dv ≤ V) :
    enorm ((p+dp) ⨯₃ (v+dv)-p ⨯₃ v) ≤ enorm p*V+P*enorm v+P*V := by
  have he : (p+dp) ⨯₃ (v+dv)-p ⨯₃ v = (p ⨯₃ dv+dp ⨯₃ v)+dp ⨯₃ dv := by
    simp only [map_add, LinearMap.add_apply]
    abel
  rw [he]
  have h₁ := (cross_enorm_le p dv).trans (mul_le_mul_of_nonneg_left hv (enorm_nonneg p))
  have h₂ := (cross_enorm_le dp v).trans (mul_le_mul_of_nonneg_right hp (enorm_nonneg v))
  have h₃ := (cross_enorm_le dp dv).trans (mul_le_mul hp hv (enorm_nonneg dv) ((enorm_nonneg dp).trans hp))
  have hsum := enorm_add_le (p ⨯₃ dv) (dp ⨯₃ v)
  have htotal := enorm_add_le (p ⨯₃ dv+dp ⨯₃ v) (dp ⨯₃ dv)
  linarith

end GNC.OrbitEnclosure
