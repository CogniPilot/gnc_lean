import GNC.Dynamics.Atmosphere

/-! Uniform central-gravity remainder on a proposed orbital position tube. -/
noncomputable section
namespace GNC.Gravity

theorem remainderBound_uniform {mu r d radius lower : ℝ}
    (hm : 0 ≤ mu) (hd : 0 ≤ d) (hdr : d ≤ radius)
    (hr : lower ≤ r) (hsep : radius < lower) :
    remainderBound mu r d ≤ 3*mu*radius^2/(lower-radius)^4 := by
  have hrad : 0 ≤ radius := hd.trans hdr
  have hpos : 0 < r := (hrad.trans_lt hsep).trans_le hr
  have hc : 0 < lower-radius := sub_pos.mpr hsep
  have hrd : 0 < r-d := by linarith
  have hc1 : lower-radius ≤ r := by linarith
  have hc2 : lower-radius ≤ r-d := by linarith
  have hs1 : (lower-radius)^2 ≤ r^2 := by
    nlinarith [mul_self_le_mul_self hc.le hc1]
  have hs2 : (lower-radius)^2 ≤ (r-d)^2 := by
    nlinarith [mul_self_le_mul_self hc.le hc2]
  have hden : (lower-radius)^4 ≤ r^2*(r-d)^2 := by
    have h := mul_le_mul hs1 hs2 (sq_nonneg _) (sq_nonneg _)
    nlinarith
  have hd2 : d^2 ≤ radius^2 := by nlinarith [mul_self_le_mul_self hd hdr]
  have hm2 := mul_le_mul_of_nonneg_left hd2 hm
  have hnum : mu*d^2*(3*r-2*d) ≤ 3*mu*radius^2*r := by
    have h := mul_le_mul hm2 (by linarith : 3*r-2*d ≤ 3*r)
      (by nlinarith : 0 ≤ 3*r-2*d) (mul_nonneg hm (sq_nonneg _))
    nlinarith
  unfold remainderBound
  apply (div_le_div_iff₀ (by positivity : 0 < r^3*(r-d)^2)
    (pow_pos hc 4)).mpr
  calc
    _ ≤ (3*mu*radius^2*r)*(lower-radius)^4 :=
      mul_le_mul_of_nonneg_right hnum (by positivity)
    _ ≤ (3*mu*radius^2*r)*(r^2*(r-d)^2) :=
      mul_le_mul_of_nonneg_left hden (by positivity)
    _ = _ := by ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem remainder_uniform (mu : ℝ) (hm : 0 ≤ mu) (p h : E) {radius lower : ℝ}
    (hh : ‖h‖ ≤ radius) (hp : lower ≤ ‖p‖) (hsep : radius < lower) :
    ‖field mu (p+h)-field mu p-gradient mu p h‖ ≤
      3*mu*radius^2/(lower-radius)^4 :=
  (remainder_bound mu hm p h (hh.trans_lt (hsep.trans_le hp))).trans
    (remainderBound_uniform hm (norm_nonneg _) hh hp hsep)

end GNC.Gravity

namespace GNC.OrbitalRemainder
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Physical gravity and exponential-density corotating drag. The coefficient
c is the nominal density coefficient at the reference radius r₀. -/
def acceleration (mu c H r₀ gamma k : ℝ) (spin : E →L[ℝ] E) (p v : E) : E :=
  Gravity.field mu p-
    (c*(1+gamma)*(1+k)*Atmosphere.density H r₀ p) • QuadraticDrag.field (v-spin p)

def linear (mu c H : ℝ) (spin : E →L[ℝ] E) (p v dp dv : E) : E :=
  Gravity.gradient mu p dp-c • Atmosphere.productLinear
    (Atmosphere.densityLinear H p dp) (v-spin p) (dv-spin dp)

/-- The retained state term is the derivative of the actual nominal force,
including the spatial density derivative and atmospheric rotation. -/
theorem linear_derivative (mu c H : ℝ) (spin : E →L[ℝ] E)
    {p v : ℝ → E} {dp dv : E} {t : ℝ}
    (hp : HasDerivAt p dp t) (hv : HasDerivAt v dv t) (hp0 : p t ≠ 0) :
    HasDerivAt (fun s => acceleration mu c H ‖p t‖ 0 0 spin (p s) (v s))
      (linear mu c H spin (p t) (v t) dp dv) t := by
  have hw := hv.sub (spin.hasFDerivAt.comp_hasDerivAt t hp)
  have hd := Atmosphere.product_derivative_all (H := H) (r₀ := ‖p t‖) hp hw hp0
  convert (Gravity.field_derivative mu hp hp0).sub (hd.const_smul c) using 1
  · ext s
    simp [acceleration, mul_smul]
  · simp [linear, Atmosphere.density]

/-- Exact decomposition after retaining the state linearization and the
common density-scale input. It includes the density/state/mass cross terms. -/
theorem residual_identity (mu c H gamma k : ℝ) (spin : E →L[ℝ] E) (p v dp dv : E) :
    acceleration mu c H ‖p‖ gamma k spin (p+dp) (v+dv)-
      acceleration mu c H ‖p‖ 0 0 spin p v-linear mu c H spin p v dp dv+
      (c*gamma) • QuadraticDrag.field (v-spin p) =
    (Gravity.field mu (p+dp)-Gravity.field mu p-Gravity.gradient mu p dp)-
      c • Atmosphere.uncertainRemainder gamma k (Atmosphere.density H ‖p‖ (p+dp))
        (Atmosphere.densityLinear H p dp) (v-spin p) (dv-spin dp) := by
  have hw : v+dv-spin (p+dp) = (v-spin p)+(dv-spin dp) := by
    rw [map_add]
    module
  simp only [acceleration, linear, hw, Atmosphere.uncertainRemainder,
    Atmosphere.density, sub_self, neg_zero, zero_div, Real.exp_zero, add_zero, mul_one]
  module

/-- The complete physical acceleration remainder throughout a proposed
position/velocity region. Reference bounds are explicit continuum hypotheses. -/
theorem residual_bound (mu c H gamma k : ℝ) (spin : E →L[ℝ] E) (p v dp dv : E)
    {P V lower W omega G K cmax : ℝ}
    (hmu : 0 ≤ mu) (hc : 0 ≤ c) (hcmax : c ≤ cmax) (hH : 0 < H)
    (hp : ‖dp‖ ≤ P) (hv : ‖dv‖ ≤ V) (hr : lower ≤ ‖p‖) (hsep : P < lower)
    (hsmall : P/H ≤ 1) (hw : ‖v-spin p‖ ≤ W) (hspin : ‖spin‖ ≤ omega)
    (hg : |gamma| ≤ G) (hk : |k| ≤ K) :
    ‖acceleration mu c H ‖p‖ gamma k spin (p+dp) (v+dv)-
      acceleration mu c H ‖p‖ 0 0 spin p v-linear mu c H spin p v dp dv+
      (c*gamma) • QuadraticDrag.field (v-spin p)‖ ≤
    3*mu*P^2/(lower-P)^4+
      cmax*((1+G)*(((P/H)^2+P^2/(2*lower*H))*W^2+
        (P/H+(P/H)^2)*(2*W*(V+omega*P))+(1+P/H+(P/H)^2)*(V+omega*P)^2)+
        G*(P/H*W^2+2*W*(V+omega*P))+
        (1+G)*K*(1+P/H+(P/H)^2)*(W+(V+omega*P))^2) := by
  have hlow : 0 < lower := ((norm_nonneg dp).trans hp).trans_lt hsep
  have hp0 : p ≠ 0 := norm_pos_iff.mp (hlow.trans_le hr)
  have hs := Atmosphere.density_envelopes_uniform H p dp hH hlow hr hp hsmall
  have hlin := (Atmosphere.density_linear_bound H p dp hH hp0).trans
    (div_le_div_of_nonneg_right hp hH.le)
  have hwind := Atmosphere.relative_wind_bound spin dp dv hp hv hspin
  have hd := Atmosphere.uncertain_remainder_uniform gamma k
    (Atmosphere.density H ‖p‖ (p+dp)) (Atmosphere.densityLinear H p dp)
    (v-spin p) (dv-spin dp) hg hk hs.2.2 hs.1 hs.2.1 hlin hw hwind
  have hdrag := mul_le_mul hcmax hd (norm_nonneg _) (hc.trans hcmax)
  rw [residual_identity]
  refine (norm_sub_le _ _).trans (add_le_add (Gravity.remainder_uniform mu hmu p dp hp hr hsep) ?_)
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc] using hdrag

end GNC.OrbitalRemainder
