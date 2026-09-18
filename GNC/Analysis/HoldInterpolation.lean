import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic

/-! # Hold interpolation error bounds

Interpolation error bounds for sampled inputs on one inter-sample interval,
formalizing the interpolation legs of the mixed-invariant preintegration
error theory:

* Theorem 2 (FOH interpolation error): the linear interpolant through the
  endpoint samples of `[0, h]` is within `M2 h^2 / 8` of a twice
  differentiable input with `‖U''‖ ≤ M2` (part (a)), and within `M1 h / 2`
  of a Lipschitz input with constant `M1` (part (b));
* Proposition 5 (online a posteriori certificate): if the error against a
  single-line FOH model is at most `r` at the sample nodes `t_j = j h` and its
  second derivative is bounded by `M2`, the error on the whole estimator
  interval is at most `r + M2 h^2 / 8`;
* Theorem 5 (quadratic interpolation error, eq 34): the centered parabola
  through the nodes `-h, 0, h` is within `(√3 / 27) M3 h^3` of a three times
  differentiable input with `‖U'''‖ ≤ M3` on `[0, h]`;
* the interpolation gain identity of eq (35) and the numeric value of its
  constant `8 √3 / 27 ≈ 0.513`.

All vector statements are proved over a real inner product space by pairing
the error with a unit vector, which reduces them to scalar statements proved
with repeated applications of Rolle's theorem. -/

noncomputable section
open Set
open scoped RealInnerProductSpace

namespace GNC.Hold

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ## Interpolants -/

/-- The first-order hold (linear interpolant) of `U` through the endpoint
samples `U 0` and `U h` of the interval `[0, h]`. -/
def linInterp (U : ℝ → E) (h t : ℝ) : E := (1 - t / h) • U 0 + (t / h) • U h

/-- The centered quadratic interpolant of `U` through the nodes `-h, 0, h`
(eq 31 with `A = u_j`, `B = (u_{j+1} - u_{j-1}) / (2h)` and
`C = (u_{j+1} - 2 u_j + u_{j-1}) / (2h^2)`). -/
def quadInterp (U : ℝ → E) (h t : ℝ) : E :=
  U 0 + (t / (2 * h)) • (U h - U (-h)) + (t ^ 2 / (2 * h ^ 2)) • (U h - (2 : ℝ) • U 0 + U (-h))

theorem linInterp_zero (U : ℝ → E) (h : ℝ) : linInterp U h 0 = U 0 := by
  simp [linInterp]

theorem linInterp_right (U : ℝ → E) {h : ℝ} (hh : h ≠ 0) : linInterp U h h = U h := by
  simp [linInterp, div_self hh]

theorem quadInterp_zero (U : ℝ → E) (h : ℝ) : quadInterp U h 0 = U 0 := by
  simp [quadInterp]

theorem quadInterp_right (U : ℝ → E) {h : ℝ} (hh : h ≠ 0) : quadInterp U h h = U h := by
  unfold quadInterp
  rw [show h / (2 * h) = 1 / 2 by field_simp, show h ^ 2 / (2 * h ^ 2) = 1 / 2 by field_simp]
  module

theorem quadInterp_left (U : ℝ → E) {h : ℝ} (hh : h ≠ 0) : quadInterp U h (-h) = U (-h) := by
  unfold quadInterp
  rw [show -h / (2 * h) = -(1 / 2) by field_simp,
    show (-h) ^ 2 / (2 * h ^ 2) = 1 / 2 by field_simp]
  module

/-- A convex combination of two vectors of norm at most `r` has norm at most `r`. -/
theorem norm_linInterp_le {U : ℝ → E} {h r t : ℝ} (hh : 0 < h) (ht : t ∈ Icc 0 h)
    (h0 : ‖U 0‖ ≤ r) (h1 : ‖U h‖ ≤ r) : ‖linInterp U h t‖ ≤ r := by
  have hθ0 : 0 ≤ t / h := div_nonneg ht.1 hh.le
  have hθ1 : t / h ≤ 1 := (div_le_one hh).2 ht.2
  calc ‖linInterp U h t‖ ≤ ‖(1 - t / h) • U 0‖ + ‖(t / h) • U h‖ := norm_add_le _ _
    _ = (1 - t / h) * ‖U 0‖ + t / h * ‖U h‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (by linarith), abs_of_nonneg hθ0]
    _ ≤ (1 - t / h) * r + t / h * r := by
        gcongr
        linarith
    _ = r := by ring

/-! ## Scalar reduction tools -/

/-- Every vector has a unit-or-zero direction `v` with `⟪e, v⟫ = ‖e‖`. -/
theorem exists_inner_eq_norm (e : E) : ∃ v : E, ‖v‖ ≤ 1 ∧ ⟪e, v⟫ = ‖e‖ := by
  by_cases he : e = 0
  · exact ⟨0, by simp, by simp [he]⟩
  · have hn : ‖e‖ ≠ 0 := norm_ne_zero_iff.2 he
    refine ⟨‖e‖⁻¹ • e, ?_, ?_⟩
    · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
    · rw [real_inner_smul_right, real_inner_self_eq_norm_sq, sq, ← mul_assoc,
        inv_mul_cancel₀ hn, one_mul]

/-- Pairing a differentiable curve with a fixed vector differentiates termwise. -/
theorem hasDerivAt_inner_const {U : ℝ → E} {U' : E} {s : ℝ} (hU : HasDerivAt U U' s) (v : E) :
    HasDerivAt (fun τ => ⟪U τ, v⟫) ⟪U', v⟫ s := by
  have := hU.inner ℝ (hasDerivAt_const s v)
  simpa using this

/-- Rolle's theorem with the derivative supplied on the closed interval. -/
theorem rolle_icc {g g' : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hg : ∀ x ∈ Icc a b, HasDerivAt g (g' x) x) (h0 : g a = g b) :
    ∃ c ∈ Ioo a b, g' c = 0 :=
  exists_hasDerivAt_eq_zero hab (fun x hx => (hg x hx).continuousAt.continuousWithinAt) h0
    (fun x hx => hg x (Ioo_subset_Icc_self hx))

/-- Generalized Rolle: three zeros force a zero of the second derivative. -/
theorem rolle_two {g g' g'' : ℝ → ℝ} {a b c : ℝ} (hab : a < b) (hbc : b < c)
    (hg : ∀ x ∈ Icc a c, HasDerivAt g (g' x) x)
    (hg' : ∀ x ∈ Icc a c, HasDerivAt g' (g'' x) x)
    (ha : g a = 0) (hb : g b = 0) (hc : g c = 0) :
    ∃ ξ ∈ Ioo a c, g'' ξ = 0 := by
  obtain ⟨ξ₁, hξ₁, h1⟩ :=
    rolle_icc hab (fun x hx => hg x ⟨hx.1, hx.2.trans hbc.le⟩) (ha.trans hb.symm)
  obtain ⟨ξ₂, hξ₂, h2⟩ :=
    rolle_icc hbc (fun x hx => hg x ⟨hab.le.trans hx.1, hx.2⟩) (hb.trans hc.symm)
  obtain ⟨ξ, hξ, h3⟩ := rolle_icc (hξ₁.2.trans hξ₂.1)
    (fun x hx => hg' x ⟨hξ₁.1.le.trans hx.1, hx.2.trans hξ₂.2.le⟩) (h1.trans h2.symm)
  exact ⟨ξ, ⟨hξ₁.1.trans hξ.1, hξ.2.trans hξ₂.2⟩, h3⟩

/-- Generalized Rolle: four zeros force a zero of the third derivative. -/
theorem rolle_three {g g' g'' g''' : ℝ → ℝ} {a b c d : ℝ} (hab : a < b) (hbc : b < c)
    (hcd : c < d)
    (hg : ∀ x ∈ Icc a d, HasDerivAt g (g' x) x)
    (hg' : ∀ x ∈ Icc a d, HasDerivAt g' (g'' x) x)
    (hg'' : ∀ x ∈ Icc a d, HasDerivAt g'' (g''' x) x)
    (ha : g a = 0) (hb : g b = 0) (hc : g c = 0) (hd : g d = 0) :
    ∃ ξ ∈ Ioo a d, g''' ξ = 0 := by
  have hbd : b < d := hbc.trans hcd
  have hac : a < c := hab.trans hbc
  obtain ⟨ξ₁, hξ₁, h1⟩ :=
    rolle_icc hab (fun x hx => hg x ⟨hx.1, hx.2.trans hbd.le⟩) (ha.trans hb.symm)
  obtain ⟨ξ₂, hξ₂, h2⟩ :=
    rolle_icc hbc (fun x hx => hg x ⟨hab.le.trans hx.1, hx.2.trans hcd.le⟩) (hb.trans hc.symm)
  obtain ⟨ξ₃, hξ₃, h3⟩ :=
    rolle_icc hcd (fun x hx => hg x ⟨hac.le.trans hx.1, hx.2⟩) (hc.trans hd.symm)
  obtain ⟨ξ, hξ, h4⟩ := rolle_two (hξ₁.2.trans hξ₂.1) (hξ₂.2.trans hξ₃.1)
    (fun x hx => hg' x ⟨hξ₁.1.le.trans hx.1, hx.2.trans hξ₃.2.le⟩)
    (fun x hx => hg'' x ⟨hξ₁.1.le.trans hx.1, hx.2.trans hξ₃.2.le⟩) h1 h2 h3
  exact ⟨ξ, ⟨hξ₁.1.trans hξ.1, hξ.2.trans hξ₃.2⟩, h4⟩

/-! ## Theorem 2(a): FOH error for a twice differentiable input -/

/-- Scalar form of Theorem 2(a): pointwise Lagrange remainder of the linear
interpolant, `|f t - ℓ t| ≤ (M2 / 2) t (h - t)`. -/
theorem scalar_linear_error {f f' f'' : ℝ → ℝ} {h M2 : ℝ} (hh : 0 < h)
    (hf : ∀ s ∈ Icc 0 h, HasDerivAt f (f' s) s)
    (hf' : ∀ s ∈ Icc 0 h, HasDerivAt f' (f'' s) s)
    (hM : ∀ s ∈ Icc 0 h, |f'' s| ≤ M2) {t : ℝ} (ht : t ∈ Icc 0 h) :
    |f t - ((1 - t / h) * f 0 + t / h * f h)| ≤ M2 / 2 * t * (h - t) := by
  rcases eq_or_lt_of_le ht.1 with h0 | h0
  · rw [← h0]; simp
  rcases eq_or_lt_of_le ht.2 with h1 | h1
  · rw [h1]; simp [div_self hh.ne']
  have hwt : t * (h - t) ≠ 0 := (mul_pos h0 (sub_pos.2 h1)).ne'
  set K : ℝ := (f t - ((1 - t / h) * f 0 + t / h * f h)) / (t * (h - t)) with hK
  have hgd : ∀ s ∈ Icc 0 h, HasDerivAt
      (fun s => f s - ((1 - s / h) * f 0 + s / h * f h) - K * (s * (h - s)))
      (f' s - (f h - f 0) / h - K * (h - 2 * s)) s := by
    intro s hs
    have e1 : HasDerivAt (fun s => (1 - s / h) * f 0 + s / h * f h) ((f h - f 0) / h) s := by
      have := (((hasDerivAt_const s (1 : ℝ)).sub ((hasDerivAt_id' (x := s)).div_const h)).mul_const
        (f 0)).add (((hasDerivAt_id' (x := s)).div_const h).mul_const (f h))
      convert this using 1; ring
    have e2 : HasDerivAt (fun s => K * (s * (h - s))) (K * (h - 2 * s)) s := by
      have := ((hasDerivAt_id' (x := s)).mul
        ((hasDerivAt_const s h).sub (hasDerivAt_id' (x := s)))).const_mul K
      refine this.congr_deriv ?_
      simp only [Pi.sub_apply]; ring
    exact ((hf s hs).sub e1).sub e2
  have hgd' : ∀ s ∈ Icc 0 h, HasDerivAt
      (fun s => f' s - (f h - f 0) / h - K * (h - 2 * s)) (f'' s + 2 * K) s := by
    intro s hs
    have := ((hf' s hs).sub (hasDerivAt_const s ((f h - f 0) / h))).sub
      (((hasDerivAt_const s h).sub ((hasDerivAt_id' (x := s)).const_mul (2 : ℝ))).const_mul K)
    convert this using 1; ring
  obtain ⟨ξ, hξ, hξ0⟩ := rolle_two h0 h1 hgd hgd' (by simp)
    (by
      show f t - ((1 - t / h) * f 0 + t / h * f h) - K * (t * (h - t)) = 0
      rw [hK, div_mul_cancel₀ _ hwt, sub_self])
    (by simp [div_self hh.ne'])
  have hξ0' : f'' ξ + 2 * K = 0 := hξ0
  obtain ⟨hl, hu⟩ := abs_le.1 (hM ξ ⟨hξ.1.le, hξ.2.le⟩)
  have hKle : |K| ≤ M2 / 2 := by
    rw [abs_le]; constructor <;> linarith
  have hft : f t - ((1 - t / h) * f 0 + t / h * f h) = K * (t * (h - t)) :=
    (div_mul_cancel₀ _ hwt).symm
  rw [hft, abs_mul, abs_of_pos (mul_pos h0 (sub_pos.2 h1))]
  calc |K| * (t * (h - t)) ≤ M2 / 2 * (t * (h - t)) :=
        mul_le_mul_of_nonneg_right hKle (mul_pos h0 (sub_pos.2 h1)).le
    _ = M2 / 2 * t * (h - t) := by ring

/-- Theorem 2(a), pointwise form: for a twice differentiable input with
`‖U''‖ ≤ M2` on `[0, h]`, the FOH error at `t` is at most `(M2 / 2) t (h - t)`. -/
theorem linear_error_le {U U' U'' : ℝ → E} {h M2 : ℝ} (hh : 0 < h)
    (hU : ∀ s ∈ Icc 0 h, HasDerivAt U (U' s) s)
    (hU' : ∀ s ∈ Icc 0 h, HasDerivAt U' (U'' s) s)
    (hM : ∀ s ∈ Icc 0 h, ‖U'' s‖ ≤ M2) {t : ℝ} (ht : t ∈ Icc 0 h) :
    ‖U t - linInterp U h t‖ ≤ M2 / 2 * t * (h - t) := by
  obtain ⟨v, hv, hev⟩ := exists_inner_eq_norm (U t - linInterp U h t)
  have hM' : ∀ s ∈ Icc 0 h, |⟪U'' s, v⟫| ≤ M2 := fun s hs =>
    (abs_real_inner_le_norm _ _).trans
      ((mul_le_of_le_one_right (norm_nonneg _) hv).trans (hM s hs))
  have key := scalar_linear_error hh (fun s hs => hasDerivAt_inner_const (hU s hs) v)
    (fun s hs => hasDerivAt_inner_const (hU' s hs) v) hM' ht
  have hid : ⟪U t, v⟫ - ((1 - t / h) * ⟪U 0, v⟫ + t / h * ⟪U h, v⟫)
      = ⟪U t - linInterp U h t, v⟫ := by
    simp [linInterp, inner_sub_left, inner_add_left, real_inner_smul_left]
  rw [hid, hev] at key
  exact (le_abs_self _).trans key

/-- The parabola `t (h - t)` is at most `h^2 / 4` on `[0, h]`. -/
theorem mul_sub_le_sq_div_four (t h : ℝ) : t * (h - t) ≤ h ^ 2 / 4 := by
  nlinarith [sq_nonneg (h - 2 * t)]

/-- Theorem 2(a): the a priori FOH interpolation bound `M2 h^2 / 8`. -/
theorem linear_error_le_bound {U U' U'' : ℝ → E} {h M2 : ℝ} (hh : 0 < h)
    (hU : ∀ s ∈ Icc 0 h, HasDerivAt U (U' s) s)
    (hU' : ∀ s ∈ Icc 0 h, HasDerivAt U' (U'' s) s)
    (hM : ∀ s ∈ Icc 0 h, ‖U'' s‖ ≤ M2) {t : ℝ} (ht : t ∈ Icc 0 h) :
    ‖U t - linInterp U h t‖ ≤ M2 * h ^ 2 / 8 := by
  have hM2 : 0 ≤ M2 := (norm_nonneg _).trans (hM 0 ⟨le_rfl, hh.le⟩)
  refine (linear_error_le hh hU hU' hM ht).trans ?_
  have := mul_le_mul_of_nonneg_left (mul_sub_le_sq_div_four t h) hM2
  nlinarith

/-! ## Theorem 2(b): FOH error for a Lipschitz input -/

/-- Theorem 2(b), pointwise form: for an input that is `M1`-Lipschitz on
`[0, h]`, the FOH error at `t = θ h` is at most `2 M1 h θ (1 - θ)`. -/
theorem lipschitz_linear_error_le {U : ℝ → E} {h M1 : ℝ} (hh : 0 < h)
    (hL : ∀ s ∈ Icc 0 h, ∀ s' ∈ Icc 0 h, ‖U s - U s'‖ ≤ M1 * |s - s'|)
    {t : ℝ} (ht : t ∈ Icc 0 h) :
    ‖U t - linInterp U h t‖ ≤ 2 * M1 * h * (t / h) * (1 - t / h) := by
  have hθ0 : 0 ≤ t / h := div_nonneg ht.1 hh.le
  have hθ1 : t / h ≤ 1 := (div_le_one hh).2 ht.2
  have hsplit : U t - linInterp U h t = (1 - t / h) • (U t - U 0) + (t / h) • (U t - U h) := by
    unfold linInterp; module
  have h0 := hL t ht 0 ⟨le_rfl, hh.le⟩
  have h1 := hL t ht h ⟨hh.le, le_rfl⟩
  rw [sub_zero, abs_of_nonneg ht.1] at h0
  rw [abs_of_nonpos (by linarith [ht.2]), neg_sub] at h1
  have ht' : t = t / h * h := by field_simp
  calc ‖U t - linInterp U h t‖
      ≤ ‖(1 - t / h) • (U t - U 0)‖ + ‖(t / h) • (U t - U h)‖ := by
        rw [hsplit]; exact norm_add_le _ _
    _ = (1 - t / h) * ‖U t - U 0‖ + t / h * ‖U t - U h‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (by linarith), abs_of_nonneg hθ0]
    _ ≤ (1 - t / h) * (M1 * t) + t / h * (M1 * (h - t)) := by
        gcongr
        linarith
    _ = 2 * M1 * h * (t / h) * (1 - t / h) := by
        rw [ht']; field_simp; ring

/-- Theorem 2(b): the a priori FOH bound `M1 h / 2` for a Lipschitz input. -/
theorem lipschitz_linear_error_le_bound {U : ℝ → E} {h M1 : ℝ} (hh : 0 < h)
    (hL : ∀ s ∈ Icc 0 h, ∀ s' ∈ Icc 0 h, ‖U s - U s'‖ ≤ M1 * |s - s'|)
    {t : ℝ} (ht : t ∈ Icc 0 h) :
    ‖U t - linInterp U h t‖ ≤ M1 * h / 2 := by
  have hM1 : 0 ≤ M1 := by
    have := (norm_nonneg _).trans (hL h ⟨hh.le, le_rfl⟩ 0 ⟨le_rfl, hh.le⟩)
    rw [sub_zero, abs_of_pos hh] at this
    exact nonneg_of_mul_nonneg_left this hh
  refine (lipschitz_linear_error_le hh hL ht).trans ?_
  have hθ0 : 0 ≤ t / h := div_nonneg ht.1 hh.le
  have hθ1 : t / h ≤ 1 := (div_le_one hh).2 ht.2
  have hq : t / h * (1 - t / h) ≤ 1 / 4 := by nlinarith [sq_nonneg (1 - 2 * (t / h))]
  have := mul_le_mul_of_nonneg_left hq (mul_nonneg hM1 hh.le)
  nlinarith

/-- Theorem 2(b) from a `LipschitzOnWith` hypothesis. -/
theorem lipschitzOnWith_linear_error_le_bound {U : ℝ → E} {h : ℝ} {M1 : NNReal} (hh : 0 < h)
    (hL : LipschitzOnWith M1 U (Icc 0 h)) {t : ℝ} (ht : t ∈ Icc 0 h) :
    ‖U t - linInterp U h t‖ ≤ M1 * h / 2 :=
  lipschitz_linear_error_le_bound hh (fun s hs s' hs' => by
    have := hL.dist_le_mul s hs s' hs'
    rwa [dist_eq_norm, Real.dist_eq] at this) ht

/-! ## Proposition 5: online a posteriori certificate -/

/-- Every point of `[0, (n + 1) h]` lies in one of the `n + 1` sub-intervals
`[j h, (j + 1) h]`. -/
theorem exists_subinterval {h : ℝ} (n : ℕ) {t : ℝ}
    (ht : t ∈ Icc 0 (((n : ℝ) + 1) * h)) :
    ∃ j : ℕ, j ≤ n ∧ (j : ℝ) * h ≤ t ∧ t ≤ ((j : ℝ) + 1) * h := by
  induction n with
  | zero => exact ⟨0, le_rfl, by simpa using ht.1, by simpa using ht.2⟩
  | succ m ih =>
    by_cases hc : t ≤ ((m : ℝ) + 1) * h
    · obtain ⟨j, hj, h1, h2⟩ := ih ⟨ht.1, hc⟩
      exact ⟨j, hj.trans (Nat.le_succ m), h1, h2⟩
    · refine ⟨m + 1, le_rfl, ?_, ?_⟩
      · push_cast; linarith
      · push_cast at ht ⊢; linarith [ht.2]

/-- Proposition 5 (online error certificate): if `e` is twice differentiable on
`[0, n h]` with `‖e''‖ ≤ M2` and `‖e (j h)‖ ≤ r` at every node `j = 0, …, n`,
then `‖e t‖ ≤ r + M2 h^2 / 8` on the whole interval (eq 30). -/
theorem certificate {e e' e'' : ℝ → E} {h M2 r : ℝ} (n : ℕ) (hh : 0 < h)
    (he : ∀ s ∈ Icc 0 ((n : ℝ) * h), HasDerivAt e (e' s) s)
    (he' : ∀ s ∈ Icc 0 ((n : ℝ) * h), HasDerivAt e' (e'' s) s)
    (hM : ∀ s ∈ Icc 0 ((n : ℝ) * h), ‖e'' s‖ ≤ M2)
    (hnode : ∀ j : ℕ, j ≤ n → ‖e ((j : ℝ) * h)‖ ≤ r)
    {t : ℝ} (ht : t ∈ Icc 0 ((n : ℝ) * h)) :
    ‖e t‖ ≤ r + M2 * h ^ 2 / 8 := by
  have hM2 : 0 ≤ M2 := (norm_nonneg _).trans (hM 0 ⟨le_rfl, by positivity⟩)
  have hq : 0 ≤ M2 * h ^ 2 / 8 := by positivity
  cases n with
  | zero =>
    have ht0 : t = 0 := by
      have h2 := ht.2
      simp at h2
      linarith [ht.1]
    have := hnode 0 le_rfl
    simp at this
    rw [ht0]; linarith
  | succ m =>
    obtain ⟨j, hj, hj1, hj2⟩ := exists_subinterval m (by push_cast at ht; exact ht)
    have hjh : 0 ≤ (j : ℝ) * h := by positivity
    have hsub : ∀ s ∈ Icc 0 h, (j : ℝ) * h + s ∈ Icc 0 (((m + 1 : ℕ) : ℝ) * h) := by
      intro s hs
      refine ⟨by linarith [hs.1], ?_⟩
      have : (j : ℝ) + 1 ≤ (m : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hj
      push_cast
      nlinarith [hs.2]
    set V : ℝ → E := fun s => e ((j : ℝ) * h + s) with hV
    have hVd : ∀ s ∈ Icc 0 h, HasDerivAt V (e' ((j : ℝ) * h + s)) s := fun s hs =>
      (he _ (hsub s hs)).comp_const_add _ _
    have hVd' : ∀ s ∈ Icc 0 h,
        HasDerivAt (fun s => e' ((j : ℝ) * h + s)) (e'' ((j : ℝ) * h + s)) s := fun s hs =>
      (he' _ (hsub s hs)).comp_const_add _ _
    have hVM : ∀ s ∈ Icc 0 h, ‖e'' ((j : ℝ) * h + s)‖ ≤ M2 := fun s hs => hM _ (hsub s hs)
    have hτ : t - (j : ℝ) * h ∈ Icc 0 h := ⟨by linarith, by linarith⟩
    have hint := linear_error_le_bound hh hVd hVd' hVM hτ
    have hV0 : ‖V 0‖ ≤ r := by simpa [hV] using hnode j (hj.trans (Nat.le_succ m))
    have hVh : ‖V h‖ ≤ r := by
      have := hnode (j + 1) (Nat.succ_le_succ hj)
      push_cast at this
      simpa [hV, add_mul] using this
    have hlin := norm_linInterp_le hh hτ hV0 hVh
    have hVt : V (t - (j : ℝ) * h) = e t := by simp [hV]
    calc ‖e t‖ = ‖(V (t - (j : ℝ) * h) - linInterp V h (t - (j : ℝ) * h))
          + linInterp V h (t - (j : ℝ) * h)‖ := by rw [sub_add_cancel, hVt]
      _ ≤ ‖V (t - (j : ℝ) * h) - linInterp V h (t - (j : ℝ) * h)‖
          + ‖linInterp V h (t - (j : ℝ) * h)‖ := norm_add_le _ _
      _ ≤ M2 * h ^ 2 / 8 + r := add_le_add hint hlin
      _ = r + M2 * h ^ 2 / 8 := add_comm _ _

/-! ## Theorem 5: quadratic interpolation error -/

/-- Scalar form of Theorem 5: pointwise Lagrange remainder of the centered
parabola, `|f t - p t| ≤ (M3 / 6) |(t + h) t (t - h)|` for `t ∈ [0, h]`. -/
theorem scalar_quadratic_error {f f' f'' f''' : ℝ → ℝ} {h M3 : ℝ} (hh : 0 < h)
    (hf : ∀ s ∈ Icc (-h) h, HasDerivAt f (f' s) s)
    (hf' : ∀ s ∈ Icc (-h) h, HasDerivAt f' (f'' s) s)
    (hf'' : ∀ s ∈ Icc (-h) h, HasDerivAt f'' (f''' s) s)
    (hM : ∀ s ∈ Icc (-h) h, |f''' s| ≤ M3) {t : ℝ} (ht : t ∈ Icc 0 h) :
    |f t - (f 0 + t / (2 * h) * (f h - f (-h)) + t ^ 2 / (2 * h ^ 2) * (f h - 2 * f 0 + f (-h)))|
      ≤ M3 / 6 * |(t + h) * t * (t - h)| := by
  have hM3 : 0 ≤ M3 := (abs_nonneg _).trans (hM 0 ⟨by linarith, hh.le⟩)
  rcases eq_or_lt_of_le ht.1 with h0 | h0
  · rw [← h0]; simp
  rcases eq_or_lt_of_le ht.2 with h1 | h1
  · rw [h1]
    have : f h - (f 0 + h / (2 * h) * (f h - f (-h)) + h ^ 2 / (2 * h ^ 2) * (f h - 2 * f 0 + f (-h)))
        = 0 := by field_simp; ring
    rw [this]; simp
  have hneg : -h < 0 := by linarith
  have hwt : (t + h) * t * (t - h) ≠ 0 := by
    have : (t + h) * t * (t - h) < 0 := by
      have : 0 < (t + h) * t := by positivity
      nlinarith
    exact this.ne
  set B : ℝ := (f h - f (-h)) / (2 * h) with hB
  set C : ℝ := (f h - 2 * f 0 + f (-h)) / (2 * h ^ 2) with hC
  have hp : ∀ s, f 0 + s / (2 * h) * (f h - f (-h)) + s ^ 2 / (2 * h ^ 2) * (f h - 2 * f 0 + f (-h))
      = f 0 + B * s + C * s ^ 2 := fun s => by rw [hB, hC]; ring
  rw [hp]
  set K : ℝ := (f t - (f 0 + B * t + C * t ^ 2)) / ((t + h) * t * (t - h)) with hK
  have hgd : ∀ s ∈ Icc (-h) h, HasDerivAt
      (fun s => f s - (f 0 + B * s + C * s ^ 2) - K * ((s + h) * s * (s - h)))
      (f' s - (B + 2 * C * s) - K * (3 * s ^ 2 - h ^ 2)) s := by
    intro s hs
    have e1 : HasDerivAt (fun s => f 0 + B * s + C * s ^ 2) (B + 2 * C * s) s := by
      have := ((hasDerivAt_const s (f 0)).add ((hasDerivAt_id' (x := s)).const_mul B)).add
        ((hasDerivAt_pow 2 s).const_mul C)
      convert this using 1; push_cast; ring
    have e2 : HasDerivAt (fun s => K * ((s + h) * s * (s - h))) (K * (3 * s ^ 2 - h ^ 2)) s := by
      have := ((((hasDerivAt_id' (x := s)).add_const h).mul (hasDerivAt_id' (x := s))).mul
        ((hasDerivAt_id' (x := s)).sub_const h)).const_mul K
      refine this.congr_deriv ?_
      simp only [Pi.mul_apply]; ring
    exact ((hf s hs).sub e1).sub e2
  have hgd' : ∀ s ∈ Icc (-h) h, HasDerivAt
      (fun s => f' s - (B + 2 * C * s) - K * (3 * s ^ 2 - h ^ 2))
      (f'' s - 2 * C - K * (6 * s)) s := by
    intro s hs
    have := ((hf' s hs).sub ((hasDerivAt_const s B).add
      ((hasDerivAt_id' (x := s)).const_mul (2 * C)))).sub
      ((((hasDerivAt_pow 2 s).const_mul (3 : ℝ)).sub (hasDerivAt_const s (h ^ 2))).const_mul K)
    convert this using 1; push_cast; ring
  have hgd'' : ∀ s ∈ Icc (-h) h, HasDerivAt
      (fun s => f'' s - 2 * C - K * (6 * s)) (f''' s - 6 * K) s := by
    intro s hs
    have := ((hf'' s hs).sub (hasDerivAt_const s (2 * C))).sub
      (((hasDerivAt_id' (x := s)).const_mul (6 : ℝ)).const_mul K)
    convert this using 1; ring
  obtain ⟨ξ, hξ, hξ0⟩ := rolle_three hneg h0 h1 hgd hgd' hgd''
    (by
      show f (-h) - (f 0 + B * -h + C * (-h) ^ 2) - K * ((-h + h) * -h * (-h - h)) = 0
      rw [hB, hC]; field_simp; ring)
    (by simp)
    (by
      show f t - (f 0 + B * t + C * t ^ 2) - K * ((t + h) * t * (t - h)) = 0
      rw [hK, div_mul_cancel₀ _ hwt, sub_self])
    (by
      show f h - (f 0 + B * h + C * h ^ 2) - K * ((h + h) * h * (h - h)) = 0
      rw [hB, hC]; field_simp; ring)
  have hξ0' : f''' ξ - 6 * K = 0 := hξ0
  obtain ⟨hl, hu⟩ := abs_le.1 (hM ξ ⟨hξ.1.le, hξ.2.le⟩)
  have hKle : |K| ≤ M3 / 6 := by
    rw [abs_le]; constructor <;> linarith
  have hft : f t - (f 0 + B * t + C * t ^ 2) = K * ((t + h) * t * (t - h)) :=
    (div_mul_cancel₀ _ hwt).symm
  rw [hft, abs_mul]
  exact mul_le_mul_of_nonneg_right hKle (abs_nonneg _)

/-- The cubic node polynomial `|(t + h) t (t - h)| = t (h^2 - t^2)` on `[0, h]`
is at most `2 h^3 / (3 √3)`, so `(M3 / 6) |(t + h) t (t - h)| ≤ (√3 / 27) M3 h^3`.
The extremum is at `t = h / √3`, via the factorization
`2 h^3 - 3 √3 t (h^2 - t^2) = (√3 t - h)^2 (√3 t + 2 h)`. -/
theorem cubic_node_bound {h M3 t : ℝ} (hh : 0 < h) (hM3 : 0 ≤ M3) (ht : t ∈ Icc 0 h) :
    M3 / 6 * |(t + h) * t * (t - h)| ≤ Real.sqrt 3 / 27 * M3 * h ^ 3 := by
  set s : ℝ := Real.sqrt 3 with hs_def
  have hs : s ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 < s := Real.sqrt_pos.2 (by norm_num)
  have habs : |(t + h) * t * (t - h)| = t * (h ^ 2 - t ^ 2) := by
    rw [abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (by linarith [ht.1]) ht.1) (by linarith [ht.2]))]; ring
  rw [habs]
  have key : 2 * h ^ 3 - 3 * s * t * (h ^ 2 - t ^ 2) = (s * t - h) ^ 2 * (s * t + 2 * h) := by
    linear_combination (-(s * t ^ 3)) * hs
  have h1 : 3 * s * t * (h ^ 2 - t ^ 2) ≤ 2 * h ^ 3 := by
    have : 0 ≤ (s * t - h) ^ 2 * (s * t + 2 * h) :=
      mul_nonneg (sq_nonneg _) (by nlinarith [ht.1])
    linarith
  have h2 : 9 * (t * (h ^ 2 - t ^ 2)) ≤ 2 * s * h ^ 3 := by
    have hprod := mul_le_mul_of_nonneg_left h1 hs0.le
    have hid : 2 * s * h ^ 3 - 9 * (t * (h ^ 2 - t ^ 2))
        = s * (2 * h ^ 3 - 3 * s * t * (h ^ 2 - t ^ 2)) := by
      linear_combination (3 * t * (h ^ 2 - t ^ 2)) * hs
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h2 hM3]

/-- Theorem 5, pointwise form: for a three times differentiable input with
`‖U'''‖ ≤ M3` on `[-h, h]`, the centered quadratic interpolation error at
`t ∈ [0, h]` is at most `(M3 / 6) |(t + h) t (t - h)|`. -/
theorem quadratic_error_le {U U' U'' U''' : ℝ → E} {h M3 : ℝ} (hh : 0 < h)
    (hU : ∀ s ∈ Icc (-h) h, HasDerivAt U (U' s) s)
    (hU' : ∀ s ∈ Icc (-h) h, HasDerivAt U' (U'' s) s)
    (hU'' : ∀ s ∈ Icc (-h) h, HasDerivAt U'' (U''' s) s)
    (hM : ∀ s ∈ Icc (-h) h, ‖U''' s‖ ≤ M3) {t : ℝ} (ht : t ∈ Icc 0 h) :
    ‖U t - quadInterp U h t‖ ≤ M3 / 6 * |(t + h) * t * (t - h)| := by
  obtain ⟨v, hv, hev⟩ := exists_inner_eq_norm (U t - quadInterp U h t)
  have hM' : ∀ s ∈ Icc (-h) h, |⟪U''' s, v⟫| ≤ M3 := fun s hs =>
    (abs_real_inner_le_norm _ _).trans
      ((mul_le_of_le_one_right (norm_nonneg _) hv).trans (hM s hs))
  have key := scalar_quadratic_error hh (fun s hs => hasDerivAt_inner_const (hU s hs) v)
    (fun s hs => hasDerivAt_inner_const (hU' s hs) v)
    (fun s hs => hasDerivAt_inner_const (hU'' s hs) v) hM' ht
  have hid : ⟪U t, v⟫ - (⟪U 0, v⟫ + t / (2 * h) * (⟪U h, v⟫ - ⟪U (-h), v⟫)
      + t ^ 2 / (2 * h ^ 2) * (⟪U h, v⟫ - 2 * ⟪U 0, v⟫ + ⟪U (-h), v⟫))
      = ⟪U t - quadInterp U h t, v⟫ := by
    simp only [quadInterp, inner_sub_left, inner_add_left, real_inner_smul_left]
  rw [hid, hev] at key
  exact (le_abs_self _).trans key

/-- Theorem 5 (eq 34): the a priori centered quadratic interpolation bound
`(√3 / 27) M3 h^3 ≈ 0.0642 M3 h^3` on `[0, h]`. -/
theorem quadratic_error_le_bound {U U' U'' U''' : ℝ → E} {h M3 : ℝ} (hh : 0 < h)
    (hU : ∀ s ∈ Icc (-h) h, HasDerivAt U (U' s) s)
    (hU' : ∀ s ∈ Icc (-h) h, HasDerivAt U' (U'' s) s)
    (hU'' : ∀ s ∈ Icc (-h) h, HasDerivAt U'' (U''' s) s)
    (hM : ∀ s ∈ Icc (-h) h, ‖U''' s‖ ≤ M3) {t : ℝ} (ht : t ∈ Icc 0 h) :
    ‖U t - quadInterp U h t‖ ≤ Real.sqrt 3 / 27 * M3 * h ^ 3 := by
  have hM3 : 0 ≤ M3 := (norm_nonneg _).trans (hM 0 ⟨by linarith, hh.le⟩)
  exact (quadratic_error_le hh hU hU' hU'' hM ht).trans (cubic_node_bound hh hM3 ht)

/-! ## Interpolation gain (eq 35) -/

/-- Eq (35): the ratio of the quadratic bound (34) to the FOH bound of
Theorem 2(a) is `(8 √3 / 27) (M3 h / M2)`. -/
theorem interpolation_gain {M2 M3 h : ℝ} (hM2 : M2 ≠ 0) (hh : h ≠ 0) :
    Real.sqrt 3 / 27 * M3 * h ^ 3 / (M2 * h ^ 2 / 8) = 8 * Real.sqrt 3 / 27 * (M3 * h / M2) := by
  field_simp

/-- Numeric value of the gain constant: `0.513 < 8 √3 / 27 < 0.514`. -/
theorem gain_constant_bounds : 0.513 < 8 * Real.sqrt 3 / 27 ∧ 8 * Real.sqrt 3 / 27 < 0.514 := by
  have hlo : (1.731375 : ℝ) < Real.sqrt 3 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hhi : Real.sqrt 3 < (1.73475 : ℝ) := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  constructor <;> linarith

end GNC.Hold
