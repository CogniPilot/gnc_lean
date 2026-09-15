import GNC.Analysis.MixedFlow
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! Real elementary modes for `y'' = q y`, with the zero mode filled in.
These functions will sum a matrix exponential after a quadratic relation in
the square of its generator. No Taylor or Magnus truncation is assumed. -/
noncomputable section
namespace GNC.QuadraticModes
open Real

def C (q t : ℝ) : ℝ :=
  if 0 < q then cosh (sqrt q * t)
  else if q < 0 then cos (sqrt (-q) * t) else 1

def S (q t : ℝ) : ℝ :=
  if 0 < q then sinh (sqrt q * t) / sqrt q
  else if q < 0 then sin (sqrt (-q) * t) / sqrt (-q) else t

def J (q t : ℝ) : ℝ := if q = 0 then t^2 / 2 else (C q t - 1) / q

@[simp] theorem C_zero (q : ℝ) : C q 0 = 1 := by simp [C]
@[simp] theorem S_zero (q : ℝ) : S q 0 = 0 := by simp [S]
@[simp] theorem J_zero (q : ℝ) : J q 0 = 0 := by simp [J]

theorem derivative_C (q t : ℝ) : HasDerivAt (C q) (q * S q t) t := by
  by_cases hp : 0 < q
  · have hn := ne_of_gt (sqrt_pos.2 hp)
    have hs := sq_sqrt hp.le
    convert (hasDerivAt_cosh (sqrt q*t)).comp t ((hasDerivAt_id t).const_mul (sqrt q)) using 1
    · funext s; simp [C, hp]
    · simp only [S, if_pos hp]
      field_simp
      rw [hs]
  · by_cases hm : q < 0
    · have hn := ne_of_gt (sqrt_pos.2 (neg_pos.2 hm))
      have hs := sq_sqrt (neg_nonneg.2 hm.le)
      convert (hasDerivAt_cos (sqrt (-q)*t)).comp t
        ((hasDerivAt_id t).const_mul (sqrt (-q))) using 1
      · funext s; simp [C, hp, hm]
      · simp only [S, if_neg hp, if_pos hm]
        field_simp
        rw [hs]; ring
    · have hz : q = 0 := le_antisymm (le_of_not_gt hp) (le_of_not_gt hm)
      subst q
      convert hasDerivAt_const t (1 : ℝ) using 1
      · funext s; simp [C]
      · simp

theorem derivative_S (q t : ℝ) : HasDerivAt (S q) (C q t) t := by
  by_cases hp : 0 < q
  · have hn := ne_of_gt (sqrt_pos.2 hp)
    convert ((hasDerivAt_sinh (sqrt q*t)).comp t
      ((hasDerivAt_id t).const_mul (sqrt q))).div_const (sqrt q) using 1
    · funext s; simp [S, hp]
    · simp [C, hp, hn]
  · by_cases hm : q < 0
    · have hn := ne_of_gt (sqrt_pos.2 (neg_pos.2 hm))
      convert ((hasDerivAt_sin (sqrt (-q)*t)).comp t
        ((hasDerivAt_id t).const_mul (sqrt (-q)))).div_const (sqrt (-q)) using 1
      · funext s; simp [S, hp, hm]
      · simp [C, hp, hm, hn]
    · convert hasDerivAt_id t using 1
      · funext s; simp [S, hp, hm]
      · simp [C, hp, hm]

theorem derivative_J (q t : ℝ) : HasDerivAt (J q) (S q t) t := by
  by_cases hz : q = 0
  · subst q
    convert ((hasDerivAt_id t).pow 2).div_const 2 using 1
    · funext s; simp [J]
    · simp [S]
  · convert ((derivative_C q t).sub_const 1).div_const q using 1
    · funext s; simp [J, hz]
    · field_simp

theorem C_eq_one_add (q t : ℝ) : C q t = 1 + q * J q t := by
  by_cases hz : q = 0
  · simp [C, J, hz]
  · simp only [J, if_neg hz]
    field_simp
    ring

end GNC.QuadraticModes
