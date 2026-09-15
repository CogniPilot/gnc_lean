import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

/-! Appendix C: strict positivity of h, proved by four differentiations and
mathlib's mean value theorem. No trigonometric series are assumed.
-/
noncomputable section
open Real Set
namespace GNC.Coefficients

def h (t : ℝ) := t^2 + t*sin t + 4*cos t - 4
def h₁ (t : ℝ) := 2*t + t*cos t - 3*sin t
def h₂ (t : ℝ) := 2 - 2*cos t - t*sin t
def h₃ (t : ℝ) := sin t - t*cos t

theorem deriv_h (t : ℝ) : HasDerivAt h (h₁ t) t := by
  convert ((((hasDerivAt_id t).pow 2).add
    ((hasDerivAt_id t).mul (hasDerivAt_sin t))).add
    ((hasDerivAt_cos t).const_mul 4)).sub_const 4 using 1; dsimp [h, h₁]; ring

theorem deriv_h₁ (t : ℝ) : HasDerivAt h₁ (h₂ t) t := by
  convert (((hasDerivAt_id t).const_mul 2).add
    ((hasDerivAt_id t).mul (hasDerivAt_cos t))).sub
    ((hasDerivAt_sin t).const_mul 3) using 1; dsimp [h₁, h₂]; ring

theorem deriv_h₂ (t : ℝ) : HasDerivAt h₂ (h₃ t) t := by
  convert (((hasDerivAt_cos t).const_mul 2).const_sub 2).sub
    ((hasDerivAt_id t).mul (hasDerivAt_sin t)) using 1; dsimp [h₂, h₃]; ring

theorem deriv_h₃ (t : ℝ) : HasDerivAt h₃ (t*sin t) t := by
  convert (hasDerivAt_sin t).sub ((hasDerivAt_id t).mul (hasDerivAt_cos t))
    using 1; dsimp [h₃]; ring

private theorem positive_from_derivative {f f' : ℝ → ℝ}
    (hd : ∀ t, HasDerivAt f (f' t) t) (hz : f 0 = 0)
    (hp : ∀ t ∈ Ioo 0 π, 0 < f' t) : ∀ t ∈ Ioo 0 π, 0 < f t := by
  have hm : StrictMonoOn f (Icc 0 π) :=
    strictMonoOn_of_deriv_pos (convex_Icc _ _)
      (fun t _ => (hd t).continuousAt.continuousWithinAt) (by
        intro t ht
        rw [interior_Icc] at ht
        rw [(hd t).deriv]
        exact hp t ht)
  intro t ht
  have hh := hm (show 0 ∈ Icc (0 : ℝ) π from ⟨le_rfl, pi_pos.le⟩)
    ⟨ht.1.le, ht.2.le⟩ ht.1
  simpa [hz] using hh

theorem h₃_pos : ∀ t ∈ Ioo 0 π, 0 < h₃ t :=
  positive_from_derivative deriv_h₃ (by simp [h₃])
    (fun t ht => mul_pos ht.1 (sin_pos_of_pos_of_lt_pi ht.1 ht.2))

theorem h₂_pos : ∀ t ∈ Ioo 0 π, 0 < h₂ t :=
  positive_from_derivative deriv_h₂ (by simp [h₂]) h₃_pos

theorem h₁_pos : ∀ t ∈ Ioo 0 π, 0 < h₁ t :=
  positive_from_derivative deriv_h₁ (by simp [h₁]) h₂_pos

/-- The strict inequality claimed in (C2)–(C3). -/
theorem h_pos : ∀ t ∈ Ioo 0 π, 0 < h t :=
  positive_from_derivative deriv_h (by simp [h]) h₁_pos

/-- The coefficient β of (46), using cot x = cos x / sin x. -/
def beta (t : ℝ) := 1 - (t/2) * (cos (t/2) / sin (t/2))
/-- The coefficient α=β' of (66), written without reciprocal trig notation. -/
def alpha (t : ℝ) := t / (4 * sin (t/2)^2) - cos (t/2) / (2 * sin (t/2))

theorem beta_pos (t : ℝ) (ht : 0 < t) (htπ : t < π) : 0 < beta t := by
  have hh : t/2 ∈ Ioo (0 : ℝ) π := ⟨by linarith, by linarith⟩
  have hs : 0 < sin (t/2) := sin_pos_of_pos_of_lt_pi hh.1 hh.2
  have he : beta t = h₃ (t/2) / sin (t/2) := by
    unfold beta h₃
    field_simp
  rw [he]
  exact div_pos (h₃_pos _ hh) hs

/-- The derivative assertion α=β' in (66), checked analytically. -/
theorem beta_derivative (t : ℝ) (ht : 0 < t) (htπ : t < π) :
    HasDerivAt beta (alpha t) t := by
  have hs0 : sin (t/2) ≠ 0 := (sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)).ne'
  have ht2 := (hasDerivAt_id t).div_const 2
  have hs := (hasDerivAt_sin (t/2)).comp t ht2
  have hc := (hasDerivAt_cos (t/2)).comp t ht2
  convert (ht2.mul (hc.div hs hs0)).const_sub 1 using 1
  dsimp only [Function.comp_apply, id_eq, Pi.div_apply]
  unfold alpha
  field_simp
  nlinarith [sin_sq_add_cos_sq (t/2),
    congrArg (fun x : ℝ => t*x) (sin_sq_add_cos_sq (t/2))]

/-- The rational/trigonometric identity (C1). -/
theorem alpha_sub_two_beta (t : ℝ) (ht : 0 < t) (htπ : t < π) :
    alpha t - 2*beta t/t = h t / (4*t*sin (t/2)^2) := by
  have hs : sin (t/2) ≠ 0 := (sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)).ne'
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hsin : sin t = 2*sin (t/2)*cos (t/2) := by
    convert sin_two_mul (t/2) using 1; congr 1; ring
  have hcos : cos t = 1 - 2*sin (t/2)^2 := by
    have hh := cos_two_mul' (t/2)
    have hh2 := sin_sq_add_cos_sq (t/2)
    rw [show 2*(t/2) = t by ring] at hh
    nlinarith
  unfold alpha beta h
  rw [hsin, hcos]
  field_simp
  ring

/-- The crucial coefficient ordering m_a > 2 m_p in Lemma 4. -/
theorem alpha_gt_two_beta_div (t : ℝ) (ht : 0 < t) (htπ : t < π) :
    2*beta t/t < alpha t := by
  have hs : 0 < sin (t/2) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hh : 0 < h t / (4*t*sin (t/2)^2) := div_pos (h_pos t ⟨ht, htπ⟩) (by positivity)
  rw [← alpha_sub_two_beta t ht htπ] at hh
  linarith

/-- The direction maximization step of Lemma 4, after reducing to its two
nonnegative spectral coefficients. The reduction to those coefficients is separate. -/
theorem direction_bound (a b l : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : 2*b ≤ a) (hl1 : l ≤ 1) :
    (Real.sqrt l * a + Real.sqrt (l*(a^2 - 4*b^2) + 4*b^2))/2 ≤ a := by
  have hsq : 0 ≤ a^2 - 4*b^2 := by nlinarith
  have hrad : l*(a^2 - 4*b^2) + 4*b^2 ≤ a^2 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1-l) hsq]
  have hfirst : Real.sqrt l ≤ 1 := (Real.sqrt_le_iff).mpr ⟨by norm_num, by simpa using hl1⟩
  have hsecond : Real.sqrt (l*(a^2-4*b^2)+4*b^2) ≤ a :=
    (Real.sqrt_le_iff).mpr ⟨ha, hrad⟩
  nlinarith [mul_le_mul_of_nonneg_right hfirst ha]

end GNC.Coefficients
