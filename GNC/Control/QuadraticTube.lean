import GNC.Control.IntegralTube
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Direct closure of a quadratic nonlinear response bound.

`a` bounds the retained response (including any separately certified numerical
defect). `b` is a response-weighted curvature bound. Neither requires a constant
linear generator. A single dimensionless check, `4*a*b < 1`, closes a region
of radius `2*a`, then bounds the actual trajectory by the smaller quadratic
root. No fixed-point iteration, convergence tolerance, or guessed tube radius
is used. A rational upper bound avoids even evaluating a square root.
-/
namespace GNC.QuadraticTube

/-- Direct exact-arithmetic evaluator. Failure means this sufficient test
does not certify a tube; it does not assert that the system is unsafe. -/
def closedRadius? (a b : ℚ) : Option ℚ :=
  if 0 < a ∧ 0 ≤ b ∧ 4*a*b < 1 then some (a/(1-2*a*b)) else none

end GNC.QuadraticTube

noncomputable section
open Set MeasureTheory
namespace GNC.QuadraticTube

/-- Stable expression for the smaller root, also defined when b = 0. -/
def radius (a b : ℝ) : ℝ := 2*a/(1+Real.sqrt (1-4*a*b))

theorem radius_properties {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    (hsmall : 4*a*b < 1) :
    a ≤ radius a b ∧ radius a b < 2*a ∧
      a+b*(radius a b)^2 = radius a b := by
  have hD : 0 < 1-4*a*b := by linarith
  have hs := Real.sqrt_pos.2 hD
  have hs2 := Real.sq_sqrt hD.le
  have hs1 : Real.sqrt (1-4*a*b) ≤ 1 := by
    have hab : 0 ≤ a*b := mul_nonneg ha.le hb
    nlinarith
  have hden : 0 < 1+Real.sqrt (1-4*a*b) := by positivity
  constructor
  · unfold radius
    apply (le_div_iff₀ hden).2
    nlinarith
  constructor
  · unfold radius
    apply (div_lt_iff₀ hden).2
    nlinarith
  · unfold radius
    field_simp
    ring_nf at hs2 ⊢
    nlinarith

/-- Purely rational alternative: one division, with no search or square root. -/
theorem rational_upper {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    (hsmall : 4*a*b < 1) :
    radius a b ≤ a/(1-2*a*b) ∧ a/(1-2*a*b) < 2*a := by
  have hD : 0 ≤ 1-4*a*b := by linarith
  have hs := Real.sqrt_nonneg (1-4*a*b)
  have hs2 := Real.sq_sqrt hD
  have hden : 0 < 1-2*a*b := by linarith
  have hroot : 0 < 1+Real.sqrt (1-4*a*b) := by positivity
  have hd1 : 1-4*a*b ≤ 1 := by nlinarith [mul_nonneg ha.le hb]
  have hdroot : 1-4*a*b ≤ Real.sqrt (1-4*a*b) := by nlinarith
  constructor
  · unfold radius
    apply (div_le_div_iff₀ hroot hden).2
    nlinarith
  · apply (div_lt_iff₀ hden).2
    nlinarith

theorem closedRadius?_sound {a b R : ℚ} (h : closedRadius? a b = some R) :
    0 < a ∧ 0 ≤ b ∧ 4*a*b < 1 ∧
      radius (a:ℝ) (b:ℝ) ≤ (R:ℝ) ∧ (R:ℝ) < 2*(a:ℝ) := by
  unfold closedRadius? at h
  split_ifs at h with hc
  · have he : a/(1-2*a*b) = R := Option.some.inj h
    subst R
    refine ⟨hc.1, hc.2.1, hc.2.2, ?_⟩
    have hr := rational_upper (a := (a:ℝ)) (b := (b:ℝ))
      (by exact_mod_cast hc.1) (by exact_mod_cast hc.2.1) (by exact_mod_cast hc.2.2)
    simpa using hr

/-- Close the nonlinear feedback using continuity and a maximum on the time
interval. The hypotheses concern a local, prefix-wise response estimate;
they do not assume that the actual trajectory stays in the proposed tube. -/
theorem bound {f : ℝ → ℝ} {T a b : ℝ}
    (hT : 0 ≤ T) (ha : 0 < a) (hb : 0 ≤ b) (hsmall : 4*a*b < 1)
    (hf : Continuous f) (hinit : f 0 ≤ a)
    (hnonneg : ∀ t ∈ Icc 0 T, 0 ≤ f t)
    (hresponse : ∀ R ∈ Icc (0:ℝ) (2*a), ∀ t ∈ Icc 0 T,
      (∀ s ∈ Icc 0 t, f s ≤ R) → f t ≤ a+b*R^2) :
    ∀ t ∈ Icc 0 T, f t ≤ radius a b := by
  have hbudget : a+b*(2*a)^2 < 2*a := by
    nlinarith [mul_lt_mul_of_pos_left hsmall ha]
  have hcoarse := IntegralTube.prefix_closure hf (hinit.trans_lt (by linarith))
    (a := 0) (b := T) (level := 2*a) (fun t ht hprefix =>
      (hresponse (2*a) ⟨by positivity, le_rfl⟩ t ht hprefix).trans_lt hbudget)
  obtain ⟨s, hs, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hT)
    hf.continuousOn
  have hm := hresponse (f s) ⟨hnonneg s hs, (hcoarse s hs).le⟩ s hs
    (fun u hu => hmax ⟨hu.1,hu.2.trans hs.2⟩)
  obtain ⟨_, hr, he⟩ := radius_properties ha hb hsmall
  have hfactor : 0 < 1-b*(f s+radius a b) := by
    have hmul := mul_le_mul_of_nonneg_left
      (add_le_add (hcoarse s hs).le hr.le) hb
    nlinarith
  have hmroot : f s ≤ radius a b := by
    by_contra h
    have hp := mul_pos (sub_pos.mpr (lt_of_not_ge h)) hfactor
    nlinarith
  exact fun t ht => (hmax ht).trans hmroot

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Keep the reference's time-varying curvature inside the response integral.
Replacing it by its maximum is optional, not part of the closure theorem. -/
theorem weighted_response (K : ℝ → E →L[ℝ] E) (r : ℝ → E) (c : ℝ → ℝ)
    {t R b : ℝ} (ht : 0 ≤ t) (hK : Continuous K) (hr : Continuous r)
    (hc : Continuous c) (hc0 : ∀ s ∈ Icc 0 t, 0 ≤ c s)
    (hbound : ∀ s ∈ Icc 0 t, ‖r s‖ ≤ c s*R^2)
    (hgain : (∫ s in 0..t, ‖K s‖*c s) ≤ b) :
    ‖∫ s in 0..t, K s (r s)‖ ≤ b*R^2 := by
  have hp := intervalIntegral.integral_mono_on (μ := volume) ht
    ((hK.clm_apply hr).norm.intervalIntegrable 0 t)
    (((hK.norm.mul hc).mul_const (R^2)).intervalIntegrable 0 t) (fun s hs => by
      calc
        ‖K s (r s)‖ ≤ ‖K s‖*‖r s‖ := (K s).le_opNorm _
        _ ≤ ‖K s‖*(c s*R^2) := mul_le_mul_of_nonneg_left (hbound s hs) (norm_nonneg _)
        _ = _ := by dsimp; ring)
  rw [intervalIntegral.integral_mul_const] at hp
  exact (intervalIntegral.norm_integral_le_integral_norm ht).trans
    (hp.trans (mul_le_mul_of_nonneg_right hgain (sq_nonneg _)))

/-- Apply the quadratic theorem to an actual variation-of-constants identity.
The kernel may come from any time-varying linear system. A computed Magnus
kernel must first have its numerical and truncation defects accounted for
in the displayed identity and the certified bound on `y`.
-/
theorem from_response (p y r : ℝ → E) (K : ℝ → ℝ → E →L[ℝ] E) (c : ℝ → ℝ)
    {T a b : ℝ} (hT : 0 ≤ T) (ha : 0 < a) (hb : 0 ≤ b) (hsmall : 4*a*b < 1)
    (hp : Continuous p) (hr : Continuous r) (hc : Continuous c)
    (hK : ∀ t ∈ Icc 0 T, Continuous (K t))
    (hc0 : ∀ t ∈ Icc 0 T, 0 ≤ c t)
    (hi : ‖p 0‖ ≤ a) (hy : ∀ t ∈ Icc 0 T, ‖y t‖ ≤ a)
    (hid : ∀ t ∈ Icc 0 T, p t = y t+∫ s in 0..t, K t s (r s))
    (hrem : ∀ t ∈ Icc 0 T, ‖p t‖ ≤ 2*a → ‖r t‖ ≤ c t*‖p t‖^2)
    (hgain : ∀ t ∈ Icc 0 T, (∫ s in 0..t, ‖K t s‖*c s) ≤ b) :
    ∀ t ∈ Icc 0 T, ‖p t‖ ≤ radius a b := by
  apply bound hT ha hb hsmall hp.norm hi (fun t _ => norm_nonneg (p t))
  intro R hR t ht hprefix
  have hw := weighted_response (K t) r c ht.1 (hK t ht) hr hc
    (fun s hs => hc0 s ⟨hs.1,hs.2.trans ht.2⟩) (fun s hs => by
      have hsT : s ∈ Icc 0 T := ⟨hs.1,hs.2.trans ht.2⟩
      exact (hrem s hsT ((hprefix s hs).trans hR.2)).trans
        (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _) (hprefix s hs) 2) (hc0 s hsT))) (hgain t ht)
  rw [hid t ht]
  exact (norm_add_le _ _).trans (add_le_add (hy t ht) hw)

end GNC.QuadraticTube
