import GNC.Dynamics.Gravity
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! Differentiation of the actual inverse-square gravitational field and its
Taylor remainder. The ambient norm is from a real inner-product space. -/
noncomputable section
open Real Set MeasureTheory
open scoped RealInnerProductSpace
namespace GNC.Gravity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem norm_derivative {f : ℝ → E} {v : E} {t : ℝ}
    (hf : HasDerivAt f v t) (hz : f t ≠ 0) :
    HasDerivAt (fun s => ‖f s‖) (⟪f t,v⟫/‖f t‖) t := by
  have hn : ‖f t‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have he := hf.norm_sq.sqrt (pow_ne_zero 2 hn)
  simpa only [Real.sqrt_sq (norm_nonneg _), mul_div_mul_left _ _ (two_ne_zero : (2:ℝ) ≠ 0)] using he

def field (μ : ℝ) (q : E) : E := (-μ/‖q‖^3) • q

def gradient (μ : ℝ) (q v : E) : E :=
  (3*μ*⟪q,v⟫/‖q‖^5) • q - (μ/‖q‖^3) • v

def hessian (μ : ℝ) (q u v : E) : E :=
  (3*μ/‖q‖^5) • (⟪q,u⟫ • v + ⟪q,v⟫ • u + ⟪u,v⟫ • q) -
    (15*μ*⟪q,u⟫*⟪q,v⟫/‖q‖^7) • q

/-- The derivative of the physical gravity field, in any direction. -/
theorem field_derivative (μ : ℝ) {f : ℝ → E} {v : E} {t : ℝ}
    (hf : HasDerivAt f v t) (hz : f t ≠ 0) :
    HasDerivAt (fun s => field μ (f s)) (gradient μ (f t) v) t := by
  have hn : ‖f t‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hd := (hasDerivAt_const t (-μ)).div ((norm_derivative hf hz).pow 3) (pow_ne_zero 3 hn)
  convert hd.smul hf using 1
  dsimp [gradient]
  match_scalars <;> field_simp <;> ring

/-- Differentiating the gravity gradient gives the symmetric Hessian (19). -/
theorem gradient_derivative (μ : ℝ) {f : ℝ → E} {u : E} {t : ℝ}
    (hf : HasDerivAt f u t) (hz : f t ≠ 0) (v : E) :
    HasDerivAt (fun s => gradient μ (f s) v) (hessian μ (f t) u v) t := by
  have hn : ‖f t‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hr := norm_derivative hf hz
  have hi := hf.inner ℝ (hasDerivAt_const t v)
  have hfirst := (hi.const_mul (3*μ)).div (hr.pow 5) (pow_ne_zero 5 hn)
  have hsecond := (hasDerivAt_const t μ).div (hr.pow 3) (pow_ne_zero 3 hn)
  convert (hfirst.smul hf).sub (hsecond.smul_const v) using 1
  dsimp [hessian]
  simp only [inner_zero_right, add_zero]
  match_scalars <;> field_simp <;> ring

theorem hessian_symmetric (μ : ℝ) (q u v : E) : hessian μ q u v = hessian μ q v u := by
  unfold hessian
  rw [real_inner_comm v u]
  module

/-- The gravity-gradient tensor written in radial projection form, equation (16). -/
theorem gradient_radial (μ : ℝ) (q v : E) :
    gradient μ q v = (μ/‖q‖^3) • ((3*⟪q,v⟫/‖q‖^2) • q - v) := by
  unfold gradient
  by_cases hn : ‖q‖ = 0
  · simp [hn]
  · match_scalars <;> field_simp <;> ring

/-- A dimension-independent version of the Hessian's scalar polynomial bound. -/
theorem hessian_polynomial_bound (c L : ℝ) (hL : 0 ≤ L) (hc : c^2 ≤ L) :
    5*c^4 - 2*c^2*L + L^2 ≤ 4*L^2 := by
  have hp := mul_nonneg (sub_nonneg.mpr hc) (show 0 ≤ 3*L+5*c^2 by positivity)
  nlinarith

theorem normalized_hessian_sq (k v : E) (hk : ‖k‖ = 1) :
    ‖(2*⟪k,v⟫) • v + (‖v‖^2-5*⟪k,v⟫^2) • k‖^2 =
      5*⟪k,v⟫^4 - 2*⟪k,v⟫^2*‖v‖^2 + ‖v‖^4 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right]
  simp only [real_inner_self_eq_norm_sq, hk, real_inner_comm v k]
  ring

theorem normalized_hessian_bound (k v : E) (hk : ‖k‖ = 1) :
    ‖(2*⟪k,v⟫) • v + (‖v‖^2-5*⟪k,v⟫^2) • k‖ ≤ 2*‖v‖^2 := by
  have hcs : ⟪k,v⟫^2 ≤ ‖v‖^2 := by
    have hh := abs_real_inner_le_norm k v
    rw [hk, one_mul] at hh
    nlinarith [sq_abs ⟪k,v⟫, abs_nonneg ⟪k,v⟫, norm_nonneg v]
  have hp := hessian_polynomial_bound ⟪k,v⟫ (‖v‖^2) (sq_nonneg _) hcs
  have he := normalized_hessian_sq k v hk
  nlinarith [norm_nonneg ((2*⟪k,v⟫) • v + (‖v‖^2-5*⟪k,v⟫^2) • k), sq_nonneg ‖v‖]

/-- The Hessian bound used in Lemma 3, proved for arbitrary displacement vectors. -/
theorem hessian_bound (μ : ℝ) (hμ : 0 ≤ μ) (q v : E) (hq : q ≠ 0) :
    ‖hessian μ q v v‖ ≤ (6*μ/‖q‖^4) * ‖v‖^2 := by
  have hn : 0 < ‖q‖ := norm_pos_iff.mpr hq
  let k := ‖q‖⁻¹ • q
  have hk : ‖k‖ = 1 := by simp [k, norm_smul, abs_of_pos hn, hn.ne']
  have he : hessian μ q v v = (3*μ/‖q‖^4) •
      ((2*⟪k,v⟫) • v + (‖v‖^2-5*⟪k,v⟫^2) • k) := by
    dsimp [hessian, k]
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
    match_scalars <;> field_simp <;> ring
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hb := mul_le_mul_of_nonneg_left (normalized_hessian_bound k v hk)
    (show 0 ≤ 3*μ/‖q‖^4 by positivity)
  convert hb using 1 <;> ring

theorem segment_norm_lower (q v : E) (s : ℝ) (hs : 0 ≤ s) :
    ‖q‖ - s*‖v‖ ≤ ‖q+s • v‖ := by
  have hh := norm_sub_norm_le q (-s • v)
  simpa [sub_eq_add_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs] using hh

theorem segment_nonzero (q v : E) (hd : ‖v‖ < ‖q‖) (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
    q+s • v ≠ 0 := by
  apply norm_pos_iff.mp
  have h := segment_norm_lower q v s hs.1
  have hh := mul_le_mul_of_nonneg_right hs.2 (norm_nonneg v)
  nlinarith

theorem hessian_continuous_segment (μ : ℝ) (q v : E) (hd : ‖v‖ < ‖q‖) :
    ContinuousOn (fun s : ℝ => hessian μ (q+s • v) v v) (Icc 0 1) := by
  intro s hs
  have hn : 0 < ‖q+s • v‖ := norm_pos_iff.mpr (segment_nonzero q v hd s hs)
  apply ContinuousAt.continuousWithinAt
  unfold hessian
  fun_prop (disch := positivity)

variable [CompleteSpace E]

/-- The exact integral remainder (17), for the actual gravity field. -/
theorem taylor_integral (μ : ℝ) (q v : E) (hd : ‖v‖ < ‖q‖) :
    field μ (q+v) - field μ q - gradient μ q v =
      ∫ s in (0:ℝ)..1, (1-s) • hessian μ (q+s • v) v v := by
  let F : ℝ → E := fun s => field μ (q+s • v) + (1-s) • gradient μ (q+s • v) v
  have hder (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
      HasDerivAt F ((1-s) • hessian μ (q+s • v) v v) s := by
    have hq := segment_nonzero q v hd s hs
    have hp : HasDerivAt (fun x : ℝ => q+x • v) v s := by
      simpa using ((hasDerivAt_id s).smul_const v).const_add q
    convert (field_derivative μ hp hq).add
      (((hasDerivAt_id s).const_sub 1).smul (gradient_derivative μ hp hq v)) using 1
    simp only [neg_smul, one_smul, id_eq]; module
  have hc : ContinuousOn (fun s : ℝ => (1-s) • hessian μ (q+s • v) v v) (Icc 0 1) :=
    (continuousOn_const.sub continuousOn_id).smul (hessian_continuous_segment μ q v hd)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => hder s (by simpa using hs)) (hc.intervalIntegrable_of_Icc (by norm_num))
  dsimp [F] at he
  simp only [sub_self, zero_smul, add_zero, zero_smul, sub_zero, one_smul] at he
  rw [he]; abel

/-- Antiderivative for the scalar envelope in the proof of Lemma 3. -/
def envelopePrimitive (μ r d s : ℝ) : ℝ :=
  μ * (3/(r-s*d)^2 + 2*(d-r)/(r-s*d)^3)

theorem envelope_derivative (μ r d s : ℝ) (hrs : r-s*d ≠ 0) :
    HasDerivAt (envelopePrimitive μ r d) (6*μ*d^2*(1-s)/(r-s*d)^4) s := by
  have hz := ((hasDerivAt_id s).mul_const d).const_sub r
  have h2 := (hasDerivAt_const s (3:ℝ)).div (hz.pow 2) (pow_ne_zero 2 hrs)
  have h3 := (hasDerivAt_const s (2*(d-r))).div (hz.pow 3) (pow_ne_zero 3 hrs)
  convert (h2.add h3).const_mul μ using 1
  dsimp
  field_simp
  ring

theorem envelope_integral (μ r d : ℝ) (hd : 0 ≤ d) (hdr : d < r) :
    (∫ s in (0:ℝ)..1, 6*μ*d^2*(1-s)/(r-s*d)^4) = remainderBound μ r d := by
  have hr : 0 < r := lt_of_le_of_lt hd hdr
  have hs (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) : 0 < r-s*d := by
    nlinarith [mul_le_mul_of_nonneg_right hs.2 hd]
  have hc : ContinuousOn (fun s : ℝ => 6*μ*d^2*(1-s)/(r-s*d)^4) (Icc 0 1) := by
    intro s hss
    have hh := hs s hss
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := positivity)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hss => envelope_derivative μ r d s (hs s (by simpa using hss)).ne')
    (hc.intervalIntegrable_of_Icc (by norm_num))]
  unfold envelopePrimitive remainderBound
  have hr0 := hr.ne'
  have hrd : r-d ≠ 0 := (sub_pos.mpr hdr).ne'
  simp only [zero_mul, one_mul, sub_zero]
  field_simp
  ring

/-- Lemma 3: the full gravity Taylor remainder bound, without assumed
derivative formulas, integral identities, or Hessian estimates. -/
theorem remainder_bound (μ : ℝ) (hμ : 0 ≤ μ) (q v : E) (hd : ‖v‖ < ‖q‖) :
    ‖field μ (q+v) - field μ q - gradient μ q v‖ ≤ remainderBound μ ‖q‖ ‖v‖ := by
  rw [taylor_integral μ q v hd, ← envelope_integral μ ‖q‖ ‖v‖ (norm_nonneg v) hd]
  have hp (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) : 0 < ‖q‖-s*‖v‖ := by
    nlinarith [mul_le_mul_of_nonneg_right hs.2 (norm_nonneg v)]
  apply intervalIntegral.norm_integral_le_of_norm_le (by norm_num)
  · apply Filter.Eventually.of_forall
    intro s hs
    have hss : s ∈ Icc (0:ℝ) 1 := ⟨hs.1.le, hs.2⟩
    have hn := hp s hss
    have he := hessian_bound μ hμ (q+s • v) v (segment_nonzero q v hd s hss)
    have hnorm := segment_norm_lower q v s hss.1
    have hd4 := pow_le_pow_left₀ hn.le hnorm 4
    have hrat : 6*μ/‖q+s • v‖^4 ≤ 6*μ/(‖q‖-s*‖v‖)^4 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hd4
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hs.2)]
    have hmul := mul_le_mul_of_nonneg_left
      (he.trans (mul_le_mul_of_nonneg_right hrat (sq_nonneg ‖v‖)))
      (sub_nonneg.mpr hs.2)
    convert hmul using 1 <;> ring
  · apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
    intro s hs
    have hn := hp s hs
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := positivity)

end GNC.Gravity
