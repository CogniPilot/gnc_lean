import GNC.Dynamics.GravityField

/-! Third directional derivative of inverse-square gravity. This supplies
the physical remainder for a quadratic-gravity, exact-angle response family.
The bound is uniform in direction and dimension and is sharp on a radial ray.
-/
noncomputable section
open Real Set MeasureTheory
open scoped RealInnerProductSpace
namespace GNC.Gravity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def third (μ : ℝ) (q v : E) : E :=
  (9*μ*‖v‖^2/‖q‖^5-45*μ*⟪q,v⟫^2/‖q‖^7) • v +
  (-45*μ*⟪q,v⟫*‖v‖^2/‖q‖^7+105*μ*⟪q,v⟫^3/‖q‖^9) • q

/-- Differentiate the actual Hessian along the same fixed direction. -/
theorem hessian_diagonal_derivative (μ : ℝ) {f : ℝ → E} {v : E} {t : ℝ}
    (hf : HasDerivAt f v t) (hz : f t ≠ 0) :
    HasDerivAt (fun s => hessian μ (f s) v v) (third μ (f t) v) t := by
  have hn : ‖f t‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hr := norm_derivative hf hz
  have hi := hf.inner ℝ (hasDerivAt_const t v)
  have ha := (hasDerivAt_const t (3*μ)).div (hr.pow 5) (pow_ne_zero 5 hn)
  have hb := ((hi.pow 2).const_mul (15*μ)).div (hr.pow 7) (pow_ne_zero 7 hn)
  have hv := (hi.smul_const v).add (hi.smul_const v) |>.add (hf.const_smul ⟪v,v⟫)
  convert (ha.smul hv).sub (hb.smul hf) using 1
  · ext s
    simp [hessian, pow_two, mul_assoc]
  · dsimp [third]
    simp only [inner_zero_right, real_inner_self_eq_norm_sq]
    match_scalars <;> field_simp <;> ring

theorem third_polynomial_bound (c L : ℝ) (hL : 0 ≤ L) (hc : c^2 ≤ L) :
    9*L^3+45*c^2*L^2-165*c^4*L+175*c^6 ≤ 64*L^3 := by
  have hp := mul_nonneg (sub_nonneg.mpr hc)
    (show 0 ≤ 175*c^4+10*c^2*L+55*L^2 by positivity)
  nlinarith

theorem normalized_third_sq (k v : E) (hk : ‖k‖ = 1) :
    ‖(3*‖v‖^2-15*⟪k,v⟫^2) • v+(-15*⟪k,v⟫*‖v‖^2+35*⟪k,v⟫^3) • k‖^2 =
      9*‖v‖^6+45*⟪k,v⟫^2*‖v‖^4-165*⟪k,v⟫^4*‖v‖^2+175*⟪k,v⟫^6 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right]
  simp only [real_inner_self_eq_norm_sq, hk, real_inner_comm v k]
  ring

theorem normalized_third_bound (k v : E) (hk : ‖k‖ = 1) :
    ‖(3*‖v‖^2-15*⟪k,v⟫^2) • v+(-15*⟪k,v⟫*‖v‖^2+35*⟪k,v⟫^3) • k‖ ≤
      8*‖v‖^3 := by
  have hcs : ⟪k,v⟫^2 ≤ ‖v‖^2 := by
    have hh := abs_real_inner_le_norm k v
    rw [hk,one_mul] at hh
    nlinarith [sq_abs ⟪k,v⟫, abs_nonneg ⟪k,v⟫, norm_nonneg v]
  have hp := third_polynomial_bound ⟪k,v⟫ (‖v‖^2) (sq_nonneg _) hcs
  have he := normalized_third_sq k v hk
  have hnon : 0 ≤ ‖v‖^3 := by positivity
  nlinarith [norm_nonneg ((3*‖v‖^2-15*⟪k,v⟫^2) • v+
    (-15*⟪k,v⟫*‖v‖^2+35*⟪k,v⟫^3) • k)]

theorem third_bound (μ : ℝ) (hμ : 0 ≤ μ) (q v : E) (hq : q ≠ 0) :
    ‖third μ q v‖ ≤ (24*μ/‖q‖^5)*‖v‖^3 := by
  have hn : 0 < ‖q‖ := norm_pos_iff.mpr hq
  let k := ‖q‖⁻¹ • q
  have hk : ‖k‖ = 1 := by simp [k,norm_smul,hn.ne']
  have he : third μ q v = (3*μ/‖q‖^5) •
      ((3*‖v‖^2-15*⟪k,v⟫^2) • v+(-15*⟪k,v⟫*‖v‖^2+35*⟪k,v⟫^3) • k) := by
    dsimp [third,k]
    rw [real_inner_smul_left]
    match_scalars <;> field_simp <;> ring
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  have hb := mul_le_mul_of_nonneg_left (normalized_third_bound k v hk)
    (show 0 ≤ 3*μ/‖q‖^5 by positivity)
  convert hb using 1
  ring

theorem third_continuous_segment (μ : ℝ) (q v : E) (hd : ‖v‖ < ‖q‖) :
    ContinuousOn (fun s : ℝ => third μ (q+s • v) v) (Icc (0:ℝ) 1) := by
  intro s hs
  have hn : 0 < ‖q+s • v‖ := norm_pos_iff.mpr (segment_nonzero q v hd s hs)
  apply ContinuousAt.continuousWithinAt
  unfold third
  fun_prop (disch := positivity)

variable [CompleteSpace E]

/-- Exact integral remainder after the quadratic gravity term. -/
theorem taylor_second_integral (μ : ℝ) (q v : E) (hd : ‖v‖ < ‖q‖) :
    field μ (q+v)-field μ q-gradient μ q v-(1/2:ℝ) • hessian μ q v v =
      ∫ s in (0:ℝ)..1, ((1-s)^2/2) • third μ (q+s • v) v := by
  let F : ℝ → E := fun s => field μ (q+s • v)+(1-s) • gradient μ (q+s • v) v+
    ((1-s)^2/2) • hessian μ (q+s • v) v v
  have hder (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
      HasDerivAt F (((1-s)^2/2) • third μ (q+s • v) v) s := by
    have hz := segment_nonzero q v hd s hs
    have hp : HasDerivAt (fun t : ℝ => q+t • v) v s := by
      simpa using ((hasDerivAt_id s).smul_const v).const_add q
    have hweight : HasDerivAt (fun t : ℝ => (1-t)^2/2) (-(1-s)) s := by
      convert (((hasDerivAt_id s).const_sub 1).pow 2).div_const 2 using 1
      simp only [id_eq]
      ring
    convert ((field_derivative μ hp hz).add
      (((hasDerivAt_id s).const_sub 1).smul (gradient_derivative μ hp hz v))).add
      (hweight.smul (hessian_diagonal_derivative μ hp hz)) using 1
    simp only [neg_smul,one_smul,id_eq]
    module
  have hc : ContinuousOn (fun s : ℝ => (1-s)^2/2) (Icc (0:ℝ) 1) :=
    ((continuousOn_const.sub continuousOn_id).pow 2).div_const (2:ℝ)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => hder s (by simpa using hs))
    ((hc.smul (third_continuous_segment μ q v hd)).intervalIntegrable_of_Icc (by norm_num))
  dsimp [F] at hi
  norm_num only [sub_self,zero_pow (by decide : 2 ≠ 0),zero_div,zero_smul,
    add_zero,zero_smul,sub_zero,one_smul,one_pow] at hi
  rw [hi]
  module

/-- Uniform cubic remainder on a displacement ball. Every coefficient is
derived from the physical third derivative; no integrator allowance appears. -/
theorem remainder_cubic (μ : ℝ) (hμ : 0 ≤ μ) (q d : E) {r D : ℝ}
    (hD : D < r) (hq : r ≤ ‖q‖) (hd : ‖d‖ ≤ D) :
    ‖field μ (q+d)-field μ q-gradient μ q d-(1/2:ℝ) • hessian μ q d d‖ ≤
      (4*μ/(r-D)^5)*‖d‖^3 := by
  have hsep : ‖d‖ < ‖q‖ := hd.trans_lt (hD.trans_le hq)
  have hpos : 0 < r-D := sub_pos.mpr hD
  rw [taylor_second_integral μ q d hsep]
  let C := 24*μ*‖d‖^3/(r-D)^5
  have hb (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
      ‖((1-s)^2/2) • third μ (q+s • d) d‖ ≤ ((1-s)^2/2)*C := by
    have hn := segment_norm_lower q d s hs.1
    have hr : r-D ≤ ‖q+s • d‖ := by
      have hm := mul_le_mul_of_nonneg_right hs.2 (norm_nonneg d)
      linarith
    have ht := third_bound μ hμ (q+s • d) d (segment_nonzero q d hsep s hs)
    have hcoef : 24*μ/‖q+s • d‖^5 ≤ 24*μ/(r-D)^5 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (pow_le_pow_left₀ hpos.le hr 5)
    have hc : ‖third μ (q+s • d) d‖ ≤ C := by
      exact (ht.trans (mul_le_mul_of_nonneg_right hcoef (by positivity))).trans_eq (by dsimp [C]; ring)
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left hc (by positivity)
  have hi := intervalIntegral.norm_integral_le_of_norm_le (by norm_num : (0:ℝ) ≤ 1)
    (Filter.Eventually.of_forall fun s hs => hb s ⟨hs.1.le,hs.2⟩)
    (((((continuous_const.sub continuous_id).pow 2).div_const (2:ℝ)).mul_const C).intervalIntegrable
      (μ := volume) 0 1)
  have hp (s : ℝ) : HasDerivAt (fun t : ℝ => t/2-t^2/2+t^3/6) ((1-s)^2/2) s := by
    convert (((hasDerivAt_id s).div_const 2).sub (((hasDerivAt_id s).pow 2).div_const 2)).add
      (((hasDerivAt_id s).pow 3).div_const 6) using 1
    simp only [id_eq]
    ring
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s (_ : s ∈ uIcc (0:ℝ) 1) => hp s)
    ((((continuous_const.sub continuous_id).pow 2).div_const (2:ℝ)).intervalIntegrable
      (μ := volume) 0 1)
  rw [intervalIntegral.integral_mul_const,he] at hi
  norm_num at hi
  convert hi using 1
  dsimp [C]
  ring

end GNC.Gravity
