import GNC.Magnus.MagnusJet
import GNC.Lie.Euclidean

/-! Norm bounds on the degree-five Magnus residual of the first-order hold.

The formal jet of `GNC.Magnus.MagnusJet` fixes the degree-five coefficient of
the right Magnus exponent for the linear generator `N(t) = N₀ + t N₁` as

  `-(1/240) [N₁,[N₀,N₁]] - (1/720) [N₀,[N₀,[N₀,N₁]]]`.

This file bounds that coefficient in any submultiplicative norm (Corollary 1,
Eq. (12)), rewrites the bound relative to the third-order correction
`(T³/12)[N₀,N₁]` (Proposition 3, Eq. (18)), specializes the rotational part
to Euclidean cross products for the truncation constants `S²W/240` and
`SW³/720` of Theorem 4 (Eq. (29)), and records the crossover arithmetic of
Corollary 3 with exact rationals.

Throughout, `a` plays the role of `N₀` and `b` the role of `N₁`, matching the
generator `a + t b` of `flowCoeff` with `c = 0`. -/
noncomputable section
namespace GNC.Magnus
open Matrix
open scoped Matrix

section Submultiplicative

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

omit [NormedAlgebra ℝ A] in
/-- The commutator is bounded by twice the product of the norms. -/
theorem norm_comm_le (x y : A) : ‖comm x y‖ ≤ 2 * ‖x‖ * ‖y‖ := by
  unfold comm
  calc ‖x * y - y * x‖ ≤ ‖x * y‖ + ‖y * x‖ := norm_sub_le _ _
    _ ≤ ‖x‖ * ‖y‖ + ‖y‖ * ‖x‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = 2 * ‖x‖ * ‖y‖ := by ring

/-- The degree-five coefficient of the right Magnus exponent of `a + t b`
(the residual `Ξ₅` of Lemma 3): `-(1/240)[b,[a,b]] - (1/720)[a,[a,[a,b]]]`. -/
def residual5 (a b : A) : A :=
  -(1/240:ℝ) • comm b (comm a b) - (1/720:ℝ) • comm a (comm a (comm a b))

/-- `residual5` is exactly the degree-five coefficient of `exponent5 a b 0`. -/
theorem residual5_eq_coeff (a b : A) : residual5 a b = (exponent5 a b 0).coeff 5 := by
  rw [linear_degree_five]; rfl

/-- The residual is bounded by its two bracket terms with the coefficients
`1/240` and `1/720`. -/
theorem norm_residual5_le_brackets (a b : A) :
    ‖residual5 a b‖ ≤
      (1/240) * ‖comm b (comm a b)‖ + (1/720) * ‖comm a (comm a (comm a b))‖ := by
  unfold residual5
  calc ‖-(1/240:ℝ) • comm b (comm a b) - (1/720:ℝ) • comm a (comm a (comm a b))‖
      ≤ ‖-(1/240:ℝ) • comm b (comm a b)‖ + ‖(1/720:ℝ) • comm a (comm a (comm a b))‖ :=
        norm_sub_le _ _
    _ = (1/240) * ‖comm b (comm a b)‖ + (1/720) * ‖comm a (comm a (comm a b))‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]; norm_num

/-- Corollary 1, Eq. (12): in any submultiplicative norm the degree-five
residual `T⁵ Ξ₅` satisfies
`‖T⁵ Ξ₅‖ ≤ (T⁵/60) ‖N₀‖ ‖N₁‖² + (T⁵/90) ‖N₀‖³ ‖N₁‖`,
from `4/240 = 1/60` and `8/720 = 1/90`. -/
theorem norm_residual5_le (a b : A) (T : ℝ) (hT : 0 ≤ T) :
    ‖T^5 • residual5 a b‖ ≤ T^5/60 * ‖a‖ * ‖b‖^2 + T^5/90 * ‖a‖^3 * ‖b‖ := by
  have ha := norm_nonneg a
  have hb := norm_nonneg b
  have h1 : ‖comm a b‖ ≤ 2 * ‖a‖ * ‖b‖ := norm_comm_le a b
  have h2 : ‖comm b (comm a b)‖ ≤ 4 * ‖a‖ * ‖b‖^2 := by
    calc ‖comm b (comm a b)‖ ≤ 2 * ‖b‖ * ‖comm a b‖ := norm_comm_le _ _
      _ ≤ 2 * ‖b‖ * (2 * ‖a‖ * ‖b‖) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 4 * ‖a‖ * ‖b‖^2 := by ring
  have h3 : ‖comm a (comm a b)‖ ≤ 4 * ‖a‖^2 * ‖b‖ := by
    calc ‖comm a (comm a b)‖ ≤ 2 * ‖a‖ * ‖comm a b‖ := norm_comm_le _ _
      _ ≤ 2 * ‖a‖ * (2 * ‖a‖ * ‖b‖) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 4 * ‖a‖^2 * ‖b‖ := by ring
  have h4 : ‖comm a (comm a (comm a b))‖ ≤ 8 * ‖a‖^3 * ‖b‖ := by
    calc ‖comm a (comm a (comm a b))‖ ≤ 2 * ‖a‖ * ‖comm a (comm a b)‖ := norm_comm_le _ _
      _ ≤ 2 * ‖a‖ * (4 * ‖a‖^2 * ‖b‖) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = 8 * ‖a‖^3 * ‖b‖ := by ring
  have hres := norm_residual5_le_brackets a b
  have hT5 : 0 ≤ T^5 := pow_nonneg hT 5
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hT5]
  calc T^5 * ‖residual5 a b‖
      ≤ T^5 * ((1/240) * (4 * ‖a‖ * ‖b‖^2) + (1/720) * (8 * ‖a‖^3 * ‖b‖)) := by
        apply mul_le_mul_of_nonneg_left _ hT5
        calc ‖residual5 a b‖
            ≤ (1/240) * ‖comm b (comm a b)‖ + (1/720) * ‖comm a (comm a (comm a b))‖ := hres
          _ ≤ (1/240) * (4 * ‖a‖ * ‖b‖^2) + (1/720) * (8 * ‖a‖^3 * ‖b‖) :=
              add_le_add (mul_le_mul_of_nonneg_left h2 (by norm_num))
                (mul_le_mul_of_nonneg_left h4 (by norm_num))
    _ = T^5/60 * ‖a‖ * ‖b‖^2 + T^5/90 * ‖a‖^3 * ‖b‖ := by ring

/-- Proposition 3, Eq. (18): with `C = [N₀,N₁]` and the third-order correction
`(T³/12) C`, the residual relative to the correction is bounded by
`(T²/20) ‖[N₁,C]‖/‖C‖ + (T²/60) ‖[N₀,[N₀,C]]‖/‖C‖`,
using `T⁵/240 = (T³/12)(T²/20)` and `T⁵/720 = (T³/12)(T²/60)`. -/
theorem relative_residual (a b : A) (T : ℝ) (hT : 0 < T) (hC : comm a b ≠ 0) :
    ‖T^5 • residual5 a b‖ / ‖(T^3/12) • comm a b‖ ≤
      T^2/20 * ‖comm b (comm a b)‖ / ‖comm a b‖ +
      T^2/60 * ‖comm a (comm a (comm a b))‖ / ‖comm a b‖ := by
  have hCpos : 0 < ‖comm a b‖ := norm_pos_iff.mpr hC
  have hT3 : 0 < T^3/12 := by positivity
  have hT5 : 0 ≤ T^5 := by positivity
  have hden : ‖(T^3/12) • comm a b‖ = T^3/12 * ‖comm a b‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hT3]
  have hnum : ‖T^5 • residual5 a b‖ ≤
      T^5 * ((1/240) * ‖comm b (comm a b)‖ + (1/720) * ‖comm a (comm a (comm a b))‖) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hT5]
    exact mul_le_mul_of_nonneg_left (norm_residual5_le_brackets a b) hT5
  rw [hden, div_le_iff₀ (by positivity)]
  calc ‖T^5 • residual5 a b‖
      ≤ T^5 * ((1/240) * ‖comm b (comm a b)‖ + (1/720) * ‖comm a (comm a (comm a b))‖) := hnum
    _ = (T^2/20 * ‖comm b (comm a b)‖ / ‖comm a b‖ +
          T^2/60 * ‖comm a (comm a (comm a b))‖ / ‖comm a b‖) * (T^3/12 * ‖comm a b‖) := by
        field_simp
        ring

end Submultiplicative

section Rotational

/-- Euclidean cross-product bound `|x × y| ≤ |x| |y|` (Lagrange identity with
Cauchy-Schwarz), restated from `GNC.cross_enorm_le`. -/
theorem enorm_cross_le (x y : Vec3) : enorm (x ⨯₃ y) ≤ enorm x * enorm y :=
  cross_enorm_le x y

/-- Theorem 4 truncation constant, first term: with `|ω_A| ≤ W` and `|ω_B| ≤ S`,
`|(1/240) ω_B × (ω_A × ω_B)| ≤ S² W / 240`. -/
theorem coning_term_le (ωA ωB : Vec3) (W S : ℝ)
    (hA : enorm ωA ≤ W) (hB : enorm ωB ≤ S) :
    enorm ((1/240:ℝ) • (ωB ⨯₃ (ωA ⨯₃ ωB))) ≤ S^2 * W / 240 := by
  have hW : 0 ≤ W := (enorm_nonneg ωA).trans hA
  have hS : 0 ≤ S := (enorm_nonneg ωB).trans hB
  have h1 : enorm (ωA ⨯₃ ωB) ≤ W * S :=
    (enorm_cross_le _ _).trans (mul_le_mul hA hB (enorm_nonneg _) hW)
  have h2 : enorm (ωB ⨯₃ (ωA ⨯₃ ωB)) ≤ S * (W * S) :=
    (enorm_cross_le _ _).trans (mul_le_mul hB h1 (enorm_nonneg _) hS)
  rw [enorm_smul, abs_of_pos (by norm_num : (0:ℝ) < 1/240)]
  nlinarith [h2]

/-- Theorem 4 truncation constant, second term: with `|ω_A| ≤ W` and `|ω_B| ≤ S`,
`|(1/720) ω_A × (ω_A × (ω_A × ω_B))| ≤ W³ S / 720`. -/
theorem triple_term_le (ωA ωB : Vec3) (W S : ℝ)
    (hA : enorm ωA ≤ W) (hB : enorm ωB ≤ S) :
    enorm ((1/720:ℝ) • (ωA ⨯₃ (ωA ⨯₃ (ωA ⨯₃ ωB)))) ≤ W^3 * S / 720 := by
  have hW : 0 ≤ W := (enorm_nonneg ωA).trans hA
  have hS : 0 ≤ S := (enorm_nonneg ωB).trans hB
  have h1 : enorm (ωA ⨯₃ ωB) ≤ W * S :=
    (enorm_cross_le _ _).trans (mul_le_mul hA hB (enorm_nonneg _) hW)
  have h2 : enorm (ωA ⨯₃ (ωA ⨯₃ ωB)) ≤ W * (W * S) :=
    (enorm_cross_le _ _).trans (mul_le_mul hA h1 (enorm_nonneg _) hW)
  have h3 : enorm (ωA ⨯₃ (ωA ⨯₃ (ωA ⨯₃ ωB))) ≤ W * (W * (W * S)) :=
    (enorm_cross_le _ _).trans (mul_le_mul hA h2 (enorm_nonneg _) hW)
  rw [enorm_smul, abs_of_pos (by norm_num : (0:ℝ) < 1/720)]
  nlinarith [h3]

/-- Theorem 4, Eq. (29), truncation leg: the rotational degree-five terms scaled
by `h⁵` are bounded by `h⁵ (S² W / 240 + S W³ / 720)`. -/
theorem rotational_residual_le (ωA ωB : Vec3) (W S h : ℝ) (hh : 0 ≤ h)
    (hA : enorm ωA ≤ W) (hB : enorm ωB ≤ S) :
    enorm (h^5 • ((1/240:ℝ) • (ωB ⨯₃ (ωA ⨯₃ ωB)) +
        (1/720:ℝ) • (ωA ⨯₃ (ωA ⨯₃ (ωA ⨯₃ ωB))))) ≤
      h^5 * (S^2 * W / 240 + S * W^3 / 720) := by
  have h5 : 0 ≤ h^5 := pow_nonneg hh 5
  rw [enorm_smul, abs_of_nonneg h5]
  apply mul_le_mul_of_nonneg_left _ h5
  calc enorm ((1/240:ℝ) • (ωB ⨯₃ (ωA ⨯₃ ωB)) +
          (1/720:ℝ) • (ωA ⨯₃ (ωA ⨯₃ (ωA ⨯₃ ωB))))
      ≤ enorm ((1/240:ℝ) • (ωB ⨯₃ (ωA ⨯₃ ωB))) +
          enorm ((1/720:ℝ) • (ωA ⨯₃ (ωA ⨯₃ (ωA ⨯₃ ωB)))) := enorm_add_le _ _
    _ ≤ S^2 * W / 240 + W^3 * S / 720 :=
        add_le_add (coning_term_le ωA ωB W S hA hB) (triple_term_le ωA ωB W S hA hB)
    _ = S^2 * W / 240 + S * W^3 / 720 := by ring

/-- The same bound for the signed rotational residual, in the form it takes
in `residual5` (coefficients `-1/240` and `-1/720`). -/
theorem rotational_residual_signed_le (ωA ωB : Vec3) (W S h : ℝ) (hh : 0 ≤ h)
    (hA : enorm ωA ≤ W) (hB : enorm ωB ≤ S) :
    enorm (h^5 • (-(1/240:ℝ) • (ωB ⨯₃ (ωA ⨯₃ ωB)) -
        (1/720:ℝ) • (ωA ⨯₃ (ωA ⨯₃ (ωA ⨯₃ ωB))))) ≤
      h^5 * (S^2 * W / 240 + S * W^3 / 720) := by
  have hrw : -(1/240:ℝ) • (ωB ⨯₃ (ωA ⨯₃ ωB)) -
      (1/720:ℝ) • (ωA ⨯₃ (ωA ⨯₃ (ωA ⨯₃ ωB))) =
      -((1/240:ℝ) • (ωB ⨯₃ (ωA ⨯₃ ωB)) +
        (1/720:ℝ) • (ωA ⨯₃ (ωA ⨯₃ (ωA ⨯₃ ωB)))) := by
    rw [neg_smul, sub_eq_add_neg, neg_add]
  rw [hrw, smul_neg, enorm_neg]
  exact rotational_residual_le ωA ωB W S h hh hA hB

end Rotational

section Crossover

/-! Corollary 3 crossover arithmetic. Both terms of Eq. (19) are proportional
to `h²`, so a measured relative residual `ρ₀` at `h₀ = 1/1600 s` scales as
`ρ₀ (h/h₀)²`; the crossover is where this reaches one percent. -/

/-- Corollary 3 (a): with `ρ₀ = 1.77 × 10⁻⁵` at `h₀ = 1/1600 s`, the one-percent
crossover interval satisfies `14.8 ms < h < 15.0 ms`, so the crossover sampling
rate `1/h` lies between `66.6 Hz` and `67.6 Hz`. -/
theorem crossover_half_mrad (h : ℝ) (hh : 0 < h)
    (hρ : (177 / 10^7 : ℝ) * (h / (1/1600))^2 = 1/100) :
    148/10^4 < h ∧ h < 150/10^4 := by
  have hsq : h^2 = 10^7 / (177 * 100 * 1600^2) := by
    field_simp at hρ ⊢
    linarith
  constructor
  · nlinarith [sq_nonneg (h - 148/10^4), sq_nonneg (h + 148/10^4)]
  · nlinarith [sq_nonneg (h - 150/10^4), sq_nonneg (h + 150/10^4)]

/-- Corollary 3 (a), frequency form: `66.6 Hz < 1/h < 67.6 Hz`. -/
theorem crossover_half_mrad_freq (h : ℝ) (hh : 0 < h)
    (hρ : (177 / 10^7 : ℝ) * (h / (1/1600))^2 = 1/100) :
    666/10 < 1/h ∧ 1/h < 676/10 := by
  obtain ⟨h1, h2⟩ := crossover_half_mrad h hh hρ
  constructor
  · rw [lt_div_iff₀ hh]; nlinarith
  · rw [div_lt_iff₀ hh]; nlinarith

/-- Corollary 3 (b): with `ρ₀ = 6.6 × 10⁻⁵` at `h₀ = 1/1600 s`, the one-percent
crossover interval satisfies `7.6 ms < h < 7.8 ms`, so the crossover sampling
rate lies between `128 Hz` and `132 Hz`. -/
theorem crossover_two_mrad (h : ℝ) (hh : 0 < h)
    (hρ : (66 / 10^6 : ℝ) * (h / (1/1600))^2 = 1/100) :
    76/10^4 < h ∧ h < 78/10^4 := by
  have hsq : h^2 = 10^6 / (66 * 100 * 1600^2) := by
    field_simp at hρ ⊢
    linarith
  constructor
  · nlinarith [sq_nonneg (h - 76/10^4), sq_nonneg (h + 76/10^4)]
  · nlinarith [sq_nonneg (h - 78/10^4), sq_nonneg (h + 78/10^4)]

/-- Corollary 3 (b), frequency form: `128 Hz < 1/h < 132 Hz`. -/
theorem crossover_two_mrad_freq (h : ℝ) (hh : 0 < h)
    (hρ : (66 / 10^6 : ℝ) * (h / (1/1600))^2 = 1/100) :
    128 < 1/h ∧ 1/h < 132 := by
  obtain ⟨h1, h2⟩ := crossover_two_mrad h hh hρ
  constructor
  · rw [lt_div_iff₀ hh]; nlinarith
  · rw [div_lt_iff₀ hh]; nlinarith

/-- Corollary 3 (c), body-rate crossover from the rotational leg alone: with the
relative term `(1/60)(|ω| h)²` at the deployed `h = 1/1600 s`, the one-percent
crossover rate satisfies `1235 rad/s < |ω| < 1245 rad/s` (the exact value is
`√1536000 ≈ 1239.4 rad/s`). -/
theorem crossover_body_rate (w : ℝ) (hw : 0 ≤ w)
    (hρ : (1/60 : ℝ) * (w * (1/1600))^2 = 1/100) :
    1235 < w ∧ w < 1245 := by
  have hsq : w^2 = 1536000 := by
    field_simp at hρ ⊢
    linarith
  constructor
  · nlinarith [sq_nonneg (w - 1235), sq_nonneg (w + 1235)]
  · nlinarith [sq_nonneg (w - 1245), sq_nonneg (w + 1245)]

end Crossover

end GNC.Magnus
