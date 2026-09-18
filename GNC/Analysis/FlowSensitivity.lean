import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-! # Flow sensitivity and error composition

Operator-norm versions of the preintegration paper's Theorem 3 (flow
sensitivity, equations (26)-(28)), Lemma 5 (error composition) and the
composition arithmetic of Theorem 4 (equation (29)).

The rotation factor is modelled by a normed ring `A` (the 3x3 matrices with
the operator norm); rotations are the elements of norm at most one. The
bi-invariant geodesic distance of the paper is replaced throughout by the
operator-norm distance `‖R - R̂‖`, which the geodesic distance dominates:
`‖R - R̂‖ = 2 sin(θ/2) ≤ θ` for a relative rotation of angle `θ`. All bounds
are polynomial in the interval length; no Gronwall factor appears. -/
noncomputable section
namespace GNC.Analysis
open Set

section Rotation
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

/-- Drift of a relative rotation, the core of equation (26). If `Φ` solves
`Φ' = W Φ` on `[0, h]` from `Φ 0 = 1`, stays in the unit ball and the angular
velocity satisfies `‖W t‖ ≤ ε`, then `‖Φ t - 1‖ ≤ ε t` on `[0, h]`. -/
theorem rotation_drift {h ε : ℝ} (Φ W : ℝ → A)
    (hΦ : ∀ t ∈ Icc 0 h, HasDerivAt Φ (W t * Φ t) t) (h0 : Φ 0 = 1)
    (hΦn : ∀ t ∈ Icc 0 h, ‖Φ t‖ ≤ 1) (hW : ∀ t ∈ Icc 0 h, ‖W t‖ ≤ ε) :
    ∀ t ∈ Icc 0 h, ‖Φ t - 1‖ ≤ ε * t := by
  have hcont : ContinuousOn Φ (Icc 0 h) :=
    fun t ht => (hΦ t ht).continuousAt.continuousWithinAt
  have hderiv : ∀ t ∈ Ico 0 h, HasDerivWithinAt Φ (W t * Φ t) (Ici t) t :=
    fun t ht => (hΦ t (Ico_subset_Icc_self ht)).hasDerivWithinAt
  have hbound : ∀ t ∈ Ico 0 h, ‖W t * Φ t‖ ≤ ε := by
    intro t ht
    have ht' := Ico_subset_Icc_self ht
    calc ‖W t * Φ t‖ ≤ ‖W t‖ * ‖Φ t‖ := norm_mul_le _ _
      _ ≤ ε * 1 := mul_le_mul (hW t ht') (hΦn t ht') (norm_nonneg _)
          ((norm_nonneg _).trans (hW t ht'))
      _ = ε := mul_one ε
  intro t ht
  have := norm_image_sub_le_of_norm_deriv_right_le_segment hcont hderiv hbound t ht
  simpa [h0] using this

/-- Equation (26) of Theorem 3 in operator-norm form. If the true attitude is
`R = Φ R̂` with `Φ` the relative rotation of `rotation_drift`, then
`‖R t - R̂ t‖ ≤ ε_ω t` on `[0, h]`. The paper states the bound for the
bi-invariant geodesic distance `d(R, R̂)`, which dominates the operator-norm
distance used here. -/
theorem attitude_sensitivity {h εω : ℝ} (Φ W R Rhat : ℝ → A)
    (hΦ : ∀ t ∈ Icc 0 h, HasDerivAt Φ (W t * Φ t) t) (h0 : Φ 0 = 1)
    (hΦn : ∀ t ∈ Icc 0 h, ‖Φ t‖ ≤ 1) (hW : ∀ t ∈ Icc 0 h, ‖W t‖ ≤ εω)
    (hR : ∀ t, R t = Φ t * Rhat t) (hRhat : ∀ t ∈ Icc 0 h, ‖Rhat t‖ ≤ 1) :
    ∀ t ∈ Icc 0 h, ‖R t - Rhat t‖ ≤ εω * t := by
  intro t ht
  have hdrift := rotation_drift Φ W hΦ h0 hΦn hW t ht
  calc ‖R t - Rhat t‖ = ‖(Φ t - 1) * Rhat t‖ := by rw [hR t, sub_mul, one_mul]
    _ ≤ ‖Φ t - 1‖ * ‖Rhat t‖ := norm_mul_le _ _
    _ ≤ (εω * t) * 1 := mul_le_mul hdrift (hRhat t ht) (norm_nonneg _)
        ((norm_nonneg _).trans hdrift)
    _ = εω * t := mul_one _

end Rotation

section Rate
variable {A : Type*} [NormedRing A]

/-- The velocity-error rate of Theorem 3: with
`ė_v = R (a - â) + (R - R̂) â`, `‖R‖ ≤ 1`, `‖a - â‖ ≤ ε_a`, `‖R - R̂‖ ≤ ε_ω t`
and `‖â‖ ≤ ā`, the rate is bounded by `ε_a + ε_ω ā t`. -/
theorem velocity_rate_bound {εa εω abar t : ℝ} (R Rhat a ahat : A)
    (hR : ‖R‖ ≤ 1) (ha : ‖a - ahat‖ ≤ εa) (hRR : ‖R - Rhat‖ ≤ εω * t)
    (hahat : ‖ahat‖ ≤ abar) :
    ‖R * (a - ahat) + (R - Rhat) * ahat‖ ≤ εa + εω * abar * t := by
  calc ‖R * (a - ahat) + (R - Rhat) * ahat‖
      ≤ ‖R * (a - ahat)‖ + ‖(R - Rhat) * ahat‖ := norm_add_le _ _
    _ ≤ ‖R‖ * ‖a - ahat‖ + ‖R - Rhat‖ * ‖ahat‖ :=
        add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ ≤ 1 * εa + (εω * t) * abar :=
        add_le_add
          (mul_le_mul hR ha (norm_nonneg _) zero_le_one)
          (mul_le_mul hRR hahat (norm_nonneg _) ((norm_nonneg _).trans hRR))
    _ = εa + εω * abar * t := by ring

end Rate

section Translation
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Equation (27) of Theorem 3. If `e_v 0 = 0` and the velocity-error rate
satisfies `‖ė_v t‖ ≤ ε_a + ε_ω ā t` on `[0, h]`, then
`‖e_v t‖ ≤ ε_a t + ε_ω ā t² / 2` on `[0, h]`. -/
theorem velocity_sensitivity {h εa εω abar : ℝ} (ev ev' : ℝ → E)
    (hd : ∀ t ∈ Icc 0 h, HasDerivAt ev (ev' t) t) (h0 : ev 0 = 0)
    (hb : ∀ t ∈ Icc 0 h, ‖ev' t‖ ≤ εa + εω * abar * t) :
    ∀ t ∈ Icc 0 h, ‖ev t‖ ≤ εa * t + εω * abar * t ^ 2 / 2 := by
  have hcont : ContinuousOn ev (Icc 0 h) :=
    fun t ht => (hd t ht).continuousAt.continuousWithinAt
  have hderiv : ∀ t ∈ Ico 0 h, HasDerivWithinAt ev (ev' t) (Ici t) t :=
    fun t ht => (hd t (Ico_subset_Icc_self ht)).hasDerivWithinAt
  have hB : ∀ x : ℝ, HasDerivAt (fun t : ℝ => εa * t + εω * abar * t ^ 2 / 2)
      (εa + εω * abar * x) x := by
    intro x
    have h1 : HasDerivAt (fun t : ℝ => εa * t) (εa * 1) x :=
      (hasDerivAt_id x).const_mul εa
    have h2 : HasDerivAt (fun t : ℝ => εω * abar * t ^ 2 / 2)
        (εω * abar * (((2 : ℕ) : ℝ) * x ^ (2 - 1)) / 2) x :=
      ((hasDerivAt_pow 2 x).const_mul (εω * abar)).div_const 2
    convert h1.add h2 using 1
    push_cast
    ring
  have ha : ‖ev 0‖ ≤ εa * 0 + εω * abar * 0 ^ 2 / 2 := by simp [h0]
  intro t ht
  exact image_norm_le_of_norm_deriv_right_le_deriv_boundary hcont hderiv ha hB
    (fun x hx => hb x (Ico_subset_Icc_self hx)) ht

/-- Equation (28) of Theorem 3. If `e_p 0 = 0`, `ė_p = e_v` and the velocity
error satisfies the bound of equation (27) on `[0, h]`, then
`‖e_p t‖ ≤ ε_a t² / 2 + ε_ω ā t³ / 6` on `[0, h]`. -/
theorem position_sensitivity {h εa εω abar : ℝ} (ep ev : ℝ → E)
    (hd : ∀ t ∈ Icc 0 h, HasDerivAt ep (ev t) t) (h0 : ep 0 = 0)
    (hv : ∀ t ∈ Icc 0 h, ‖ev t‖ ≤ εa * t + εω * abar * t ^ 2 / 2) :
    ∀ t ∈ Icc 0 h, ‖ep t‖ ≤ εa * t ^ 2 / 2 + εω * abar * t ^ 3 / 6 := by
  have hcont : ContinuousOn ep (Icc 0 h) :=
    fun t ht => (hd t ht).continuousAt.continuousWithinAt
  have hderiv : ∀ t ∈ Ico 0 h, HasDerivWithinAt ep (ev t) (Ici t) t :=
    fun t ht => (hd t (Ico_subset_Icc_self ht)).hasDerivWithinAt
  have hB : ∀ x : ℝ,
      HasDerivAt (fun t : ℝ => εa * t ^ 2 / 2 + εω * abar * t ^ 3 / 6)
        (εa * x + εω * abar * x ^ 2 / 2) x := by
    intro x
    have h1 : HasDerivAt (fun t : ℝ => εa * t ^ 2 / 2)
        (εa * (((2 : ℕ) : ℝ) * x ^ (2 - 1)) / 2) x :=
      ((hasDerivAt_pow 2 x).const_mul εa).div_const 2
    have h2 : HasDerivAt (fun t : ℝ => εω * abar * t ^ 3 / 6)
        (εω * abar * (((3 : ℕ) : ℝ) * x ^ (3 - 1)) / 6) x :=
      ((hasDerivAt_pow 3 x).const_mul (εω * abar)).div_const 6
    convert h1.add h2 using 1
    push_cast
    ring
  have ha : ‖ep 0‖ ≤ εa * 0 ^ 2 / 2 + εω * abar * 0 ^ 3 / 6 := by simp [h0]
  intro t ht
  exact image_norm_le_of_norm_deriv_right_le_deriv_boundary hcont hderiv ha hB
    (fun x hx => hv x (Ico_subset_Icc_self hx)) ht

/-- Equations (27) and (28) together: the velocity and position errors that
start from zero and are driven by a rate bounded by `ε_a + ε_ω ā t` obey the
polynomial bounds of Theorem 3 on `[0, h]`. -/
theorem translation_sensitivity {h εa εω abar : ℝ} (ep ev ev' : ℝ → E)
    (hdv : ∀ t ∈ Icc 0 h, HasDerivAt ev (ev' t) t) (hv0 : ev 0 = 0)
    (hb : ∀ t ∈ Icc 0 h, ‖ev' t‖ ≤ εa + εω * abar * t)
    (hdp : ∀ t ∈ Icc 0 h, HasDerivAt ep (ev t) t) (hp0 : ep 0 = 0) :
    (∀ t ∈ Icc 0 h, ‖ev t‖ ≤ εa * t + εω * abar * t ^ 2 / 2) ∧
    (∀ t ∈ Icc 0 h, ‖ep t‖ ≤ εa * t ^ 2 / 2 + εω * abar * t ^ 3 / 6) := by
  have hv := velocity_sensitivity ev ev' hdv hv0 hb
  exact ⟨hv, position_sensitivity ep ev hdp hp0 hv⟩

end Translation

section Composition
variable {A : Type*} [NormedRing A] [NormOneClass A]

/-- A product of elements of norm at most one has norm at most one. -/
theorem norm_list_prod_le_one (l : List A) (hl : ∀ x ∈ l, ‖x‖ ≤ 1) :
    ‖l.prod‖ ≤ 1 := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.prod_cons]
    have hx : ‖x‖ ≤ 1 := hl x (List.mem_cons_self ..)
    have hl' : ∀ y ∈ l, ‖y‖ ≤ 1 := fun y hy => hl y (List.mem_cons_of_mem x hy)
    calc ‖x * l.prod‖ ≤ ‖x‖ * ‖l.prod‖ := norm_mul_le _ _
      _ ≤ 1 * 1 := mul_le_mul hx (ih hl') (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1

omit [NormOneClass A] in
/-- The one-step composition estimate: for `‖x'‖ ≤ 1` and `‖y‖ ≤ 1`,
`‖x y - x' y'‖ ≤ ‖x - x'‖ + ‖y - y'‖`. -/
theorem norm_mul_sub_mul_le (x x' y y' : A) (hx' : ‖x'‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    ‖x * y - x' * y'‖ ≤ ‖x - x'‖ + ‖y - y'‖ := by
  have key : x * y - x' * y' = (x - x') * y + x' * (y - y') := by noncomm_ring
  calc ‖x * y - x' * y'‖ = ‖(x - x') * y + x' * (y - y')‖ := by rw [key]
    _ ≤ ‖(x - x') * y‖ + ‖x' * (y - y')‖ := norm_add_le _ _
    _ ≤ ‖x - x'‖ * ‖y‖ + ‖x'‖ * ‖y - y'‖ :=
        add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ ≤ ‖x - x'‖ * 1 + 1 * ‖y - y'‖ :=
        add_le_add (mul_le_mul_of_nonneg_left hy (norm_nonneg _))
          (mul_le_mul_of_nonneg_right hx' (norm_nonneg _))
    _ = ‖x - x'‖ + ‖y - y'‖ := by rw [mul_one, one_mul]

/-- Lemma 5 (error composition) in operator-norm form: for two families of
rotations `a b : Fin n → A` of norm at most one, the ordered products satisfy
`‖∏ a_i - ∏ b_i‖ ≤ ∑ ‖a_i - b_i‖`. -/
theorem norm_ofFn_prod_sub_le :
    ∀ {n : ℕ} (a b : Fin n → A), (∀ i, ‖a i‖ ≤ 1) → (∀ i, ‖b i‖ ≤ 1) →
      ‖(List.ofFn a).prod - (List.ofFn b).prod‖ ≤ ∑ i, ‖a i - b i‖
  | 0, a, b, _, _ => by simp
  | n + 1, a, b, ha, hb => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons,
      Fin.sum_univ_succ]
    have hP : ‖(List.ofFn fun i : Fin n => a i.succ).prod‖ ≤ 1 :=
      norm_list_prod_le_one _ (by
        intro x hx
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
        exact ha _)
    have ih : ‖(List.ofFn fun i : Fin n => a i.succ).prod -
        (List.ofFn fun i : Fin n => b i.succ).prod‖ ≤
        ∑ i : Fin n, ‖a i.succ - b i.succ‖ :=
      norm_ofFn_prod_sub_le (fun i : Fin n => a i.succ)
        (fun i : Fin n => b i.succ) (fun i => ha _) (fun i => hb _)
    exact (norm_mul_sub_mul_le _ _ _ _ (hb 0) hP).trans (add_le_add_right ih _)

/-- The arithmetic of Theorem 4, equation (29): over one second split into
`n` subintervals of length `h` (so `n h = 1`), if every subinterval
contributes an attitude error of at most `h ι + h⁵ τ`, the sum of the
contributions is at most `ι + h⁴ τ`. In the paper `ι = M₂ h² / 8` is the
interpolation leg and `τ = S² W / 240 + S W³ / 720` the truncation leg. -/
theorem subinterval_sum_bound (n : ℕ) {h ι τ : ℝ} (hn : (n : ℝ) * h = 1)
    (e : Fin n → ℝ) (he : ∀ i, e i ≤ h * ι + h ^ 5 * τ) :
    ∑ i, e i ≤ ι + h ^ 4 * τ := by
  calc ∑ i, e i ≤ ∑ _i : Fin n, (h * ι + h ^ 5 * τ) :=
        Finset.sum_le_sum fun i _ => he i
    _ = (n : ℝ) * (h * ι + h ^ 5 * τ) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = ((n : ℝ) * h) * ι + ((n : ℝ) * h) * h ^ 4 * τ := by ring
    _ = ι + h ^ 4 * τ := by rw [hn]; ring

/-- Theorem 4, the per-second attitude bound, assembled from Lemma 5 and the
per-subinterval bounds. With `n` subintervals of length `h`, `n h = 1`, true
and integrated per-subinterval rotation increments `a i` and `b i` of norm at
most one, and per-subinterval errors `‖a i - b i‖ ≤ h ι + h⁵ τ`, the
composed one-second attitudes differ by at most `ι + h⁴ τ`. -/
theorem per_second_bound (n : ℕ) {h ι τ : ℝ} (hn : (n : ℝ) * h = 1)
    (a b : Fin n → A) (ha : ∀ i, ‖a i‖ ≤ 1) (hb : ∀ i, ‖b i‖ ≤ 1)
    (he : ∀ i, ‖a i - b i‖ ≤ h * ι + h ^ 5 * τ) :
    ‖(List.ofFn a).prod - (List.ofFn b).prod‖ ≤ ι + h ^ 4 * τ :=
  (norm_ofFn_prod_sub_le a b ha hb).trans
    (subinterval_sum_bound n hn (fun i => ‖a i - b i‖) he)

end Composition

end GNC.Analysis
