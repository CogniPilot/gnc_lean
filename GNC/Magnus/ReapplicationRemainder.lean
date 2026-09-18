import GNC.Magnus.MagnusFlow
import GNC.Lie.Euclidean

/-! Exact reapplication at the delayed horizon (Theorem 6, Eqs. (36)-(37))
and the second-order bias-relinearization remainder (Proposition 8,
Eq. (38)), in an abstract normed-algebra form.

The comparison argument is the one of Theorem 3: a curve `g` driven by a
body velocity `V`, and the first-order exponential `exp (s • V 0)`, are
compared through the product `g s * exp (-s • V 0)`, whose derivative is
`g s * (V s - V 0) * exp (-s • V 0)`.  The norm-one hypotheses on the
curve and on the exponentials stand in for the orthogonality used in the
paper. -/
noncomputable section
namespace GNC.Magnus
open NormedSpace Set

section Comparison
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

/-- The curvature product `g s * exp (-s • V0)` and its derivative. -/
theorem product_curve_derivative {g V : ℝ → A} (V0 : A) {s : ℝ}
    (hg : HasDerivAt g (g s * V s) s) :
    HasDerivAt (fun u => g u * exp ((-u) • V0))
      (g s * (V s - V0) * exp ((-s) • V0)) s := by
  have hE := (hasDerivAt_exp_smul_const' V0 (-s)).scomp s (hasDerivAt_id s).neg
  convert hg.mul hE using 1
  simp only [Function.comp_apply, neg_one_smul]
  noncomm_ring

/-- Theorem 3's comparison applied to a curve and its first-order exponential:
if the body velocity deviates from its initial value at most linearly,
`‖V s - V0‖ ≤ K s`, then the curve deviates from `exp (s • V0)` at most
quadratically, `K s² / 2`, on the unit interval. -/
theorem first_order_comparison {g V : ℝ → A} {V0 : A} {K : ℝ}
    (hg0 : g 0 = 1)
    (hg : ∀ s ∈ Icc (0:ℝ) 1, HasDerivAt g (g s * V s) s)
    (hgn : ∀ s ∈ Icc (0:ℝ) 1, ‖g s‖ ≤ 1)
    (hen : ∀ s ∈ Icc (0:ℝ) 1, ‖exp ((-s) • V0)‖ ≤ 1)
    (hep : ∀ s ∈ Icc (0:ℝ) 1, ‖exp (s • V0)‖ ≤ 1)
    (hV : ∀ s ∈ Icc (0:ℝ) 1, ‖V s - V0‖ ≤ K * s) :
    ∀ s ∈ Icc (0:ℝ) 1, ‖g s - exp (s • V0)‖ ≤ K * s ^ 2 / 2 := by
  set h : ℝ → A := fun u => g u * exp ((-u) • V0) with hh
  have hd : ∀ s ∈ Icc (0:ℝ) 1,
      HasDerivAt (fun u => h u - 1) (g s * (V s - V0) * exp ((-s) • V0)) s :=
    fun s hs => (product_curve_derivative V0 (hg s hs)).sub_const 1
  have hbound : ∀ s ∈ Icc (0:ℝ) 1, ‖h s - 1‖ ≤ K * s ^ 2 / 2 := by
    intro s hs
    refine image_norm_le_of_norm_deriv_right_le_deriv_boundary
      (f := fun u => h u - 1) (a := 0) (b := 1)
      (f' := fun s => g s * (V s - V0) * exp ((-s) • V0))
      (B := fun s => K * s ^ 2 / 2) (B' := fun s => K * s)
      (fun u hu => (hd u hu).continuousAt.continuousWithinAt)
      (fun u hu => (hd u (Ico_subset_Icc_self hu)).hasDerivWithinAt)
      (by simp [hh, hg0]) (fun u => ?_) (fun u hu => ?_) hs
    · have := ((hasDerivAt_pow 2 u).const_mul K).div_const 2
      convert this using 1
      ring
    · have hu' := Ico_subset_Icc_self hu
      calc ‖g u * (V u - V0) * exp ((-u) • V0)‖
          ≤ ‖g u * (V u - V0)‖ * ‖exp ((-u) • V0)‖ := norm_mul_le _ _
        _ ≤ (‖g u‖ * ‖V u - V0‖) * ‖exp ((-u) • V0)‖ :=
            mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
        _ ≤ (1 * (K * u)) * 1 := by
            have h1 := hgn u hu'
            have h2 := hV u hu'
            have h3 := hen u hu'
            have h4 : 0 ≤ K * u := le_trans (norm_nonneg _) h2
            gcongr
        _ = K * u := by ring
  intro s hs
  have hsplit : g s - exp (s • V0) = (h s - 1) * exp (s • V0) := by
    simp only [hh, sub_mul, one_mul, mul_assoc, neg_smul,
      MixedInvariant.exp_cancel', mul_one]
  rw [hsplit]
  calc ‖(h s - 1) * exp (s • V0)‖ ≤ ‖h s - 1‖ * ‖exp (s • V0)‖ := norm_mul_le _ _
    _ ≤ (K * s ^ 2 / 2) * 1 := by
        have h1 := hbound s hs
        have h2 := hep s hs
        have h0 : 0 ≤ K * s ^ 2 / 2 := le_trans (norm_nonneg _) h1
        gcongr
    _ = K * s ^ 2 / 2 := by ring

omit [CompleteSpace A] in
/-- Mean value: a body velocity with derivative bounded by `K` on the unit
interval is `K`-Lipschitz from its initial value. -/
theorem velocity_lipschitz {V V' : ℝ → A} {V0 : A} {K : ℝ}
    (hV0 : V 0 = V0)
    (hV : ∀ s ∈ Icc (0:ℝ) 1, HasDerivAt V (V' s) s)
    (hK : ∀ s ∈ Icc (0:ℝ) 1, ‖V' s‖ ≤ K) :
    ∀ s ∈ Icc (0:ℝ) 1, ‖V s - V0‖ ≤ K * s := by
  intro s hs
  have := norm_image_sub_le_of_norm_deriv_right_le_segment (a := 0) (b := 1)
    (f := V) (f' := V') (C := K)
    (fun u hu => (hV u hu).continuousAt.continuousWithinAt)
    (fun u hu => (hV u (Ico_subset_Icc_self hu)).hasDerivWithinAt)
    (fun u hu => hK u (Ico_subset_Icc_self hu)) s hs
  simpa [hV0] using this

/-- Proposition 8, Eq. (38), abstract form: along the bias ray
`b0 + s • db` with `‖db‖ = δ`, the curvature bound `‖V'‖ ≤ 2 T_D² δ²`
of the paper gives a relinearization remainder at `s = 1` of at most
`(T_D δ)²`, the remainder being measured against the first-order
exponential `exp V0` with `V0 = J db`. -/
theorem second_order_remainder {g V V' : ℝ → A} {V0 : A} {TD δ : ℝ}
    (hg0 : g 0 = 1)
    (hg : ∀ s ∈ Icc (0:ℝ) 1, HasDerivAt g (g s * V s) s)
    (hgn : ∀ s ∈ Icc (0:ℝ) 1, ‖g s‖ ≤ 1)
    (hen : ∀ s ∈ Icc (0:ℝ) 1, ‖exp ((-s) • V0)‖ ≤ 1)
    (hep : ∀ s ∈ Icc (0:ℝ) 1, ‖exp (s • V0)‖ ≤ 1)
    (hV0 : V 0 = V0)
    (hV : ∀ s ∈ Icc (0:ℝ) 1, HasDerivAt V (V' s) s)
    (hK : ∀ s ∈ Icc (0:ℝ) 1, ‖V' s‖ ≤ 2 * TD ^ 2 * δ ^ 2) :
    ‖g 1 - exp V0‖ ≤ (TD * δ) ^ 2 := by
  have h := first_order_comparison hg0 hg hgn hen hep
    (velocity_lipschitz hV0 hV hK) 1 ⟨zero_le_one, le_rfl⟩
  rw [one_smul] at h
  calc ‖g 1 - exp V0‖ ≤ 2 * TD ^ 2 * δ ^ 2 * 1 ^ 2 / 2 := h
    _ = (TD * δ) ^ 2 := by ring

end Comparison

section Horizon

/-- The per-interval factor `-h I + (h²/12) [Δω]ˣ` of Eq. (33) has norm at
most `h (1 + h s / 12)` when `‖[Δω]ˣ‖ ≤ s`. -/
theorem interval_factor_norm_le {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    [NormOneClass A]
    {S : A} {h s : ℝ} (hh : 0 ≤ h) (hS : ‖S‖ ≤ s) :
    ‖(-h) • (1 : A) + (h ^ 2 / 12) • S‖ ≤ h * (1 + h * s / 12) := by
  calc ‖(-h) • (1 : A) + (h ^ 2 / 12) • S‖
      ≤ ‖(-h) • (1 : A)‖ + ‖(h ^ 2 / 12) • S‖ := norm_add_le _ _
    _ = h + h ^ 2 / 12 * ‖S‖ := by
        rw [norm_smul, norm_smul, norm_one, mul_one, Real.norm_eq_abs,
          Real.norm_eq_abs, abs_neg, abs_of_nonneg hh,
          abs_of_nonneg (by positivity)]
    _ ≤ h + h ^ 2 / 12 * s := by gcongr
    _ = h * (1 + h * s / 12) := by ring

/-- The horizon constant of Eq. (38): `n` intervals of step `h` whose
factors satisfy `‖D_j‖ ≤ h (1 + h s / 12)` have
`T_D = ∑ ‖D_j‖ ≤ T_tot (1 + h s / 12)` with `T_tot = n h`. -/
theorem horizon_constant_le {E : Type*} [SeminormedAddGroup E] {n : ℕ}
    (D : Fin n → E) {h s : ℝ}
    (hD : ∀ j, ‖D j‖ ≤ h * (1 + h * s / 12)) :
    ∑ j, ‖D j‖ ≤ (n * h) * (1 + h * s / 12) := by
  calc ∑ j, ‖D j‖ ≤ ∑ _j : Fin n, h * (1 + h * s / 12) :=
        Finset.sum_le_sum fun j _ => hD j
    _ = (n * h) * (1 + h * s / 12) := by simp [mul_assoc]

end Horizon

section Skew
open Matrix

/-- Frobenius identity for the cross-product matrix:
`∑ (skew x)_{ij}² = 2 ‖x‖²`. -/
theorem skew_sum_sq (x : Vec3) :
    ∑ i, ∑ j, (skew x i j) ^ 2 = 2 * lengthSq x := by
  simp [skew, Fin.sum_univ_succ, lengthSq]; ring

/-- Two coordinates of a vector satisfy `|x i| + |x j| ≤ √2 ‖x‖` when
`i ≠ j`; stated for the three coordinate pairs. -/
theorem abs_add_abs_le_sqrt_two_enorm (x : Vec3) (i j : Fin 3) (hij : i ≠ j) :
    |x i| + |x j| ≤ Real.sqrt 2 * enorm x := by
  have hc : 0 ≤ Real.sqrt 2 * enorm x := mul_nonneg (Real.sqrt_nonneg 2) (enorm_nonneg x)
  have key : (|x i| + |x j|) ^ 2 ≤ (Real.sqrt 2 * enorm x) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num), enorm_sq]
    have h2 : (|x i| + |x j|) ^ 2 ≤ 2 * (x i ^ 2 + x j ^ 2) := by
      nlinarith [sq_nonneg (|x i| - |x j|), sq_abs (x i), sq_abs (x j)]
    have h3 : x i ^ 2 + x j ^ 2 ≤ lengthSq x := by
      fin_cases i <;> fin_cases j <;> simp at hij <;>
        simp [lengthSq] <;> nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2)]
    linarith
  nlinarith [abs_nonneg (x i), abs_nonneg (x j)]

open scoped Matrix.Norms.Operator in
/-- In the `L∞`-induced operator norm (the norm used for the algebra
`Mat5`), `‖[x]ˣ‖ ≤ √2 ‖x‖`. -/
theorem skew_linfty_opNorm_le (x : Vec3) : ‖skew x‖ ≤ Real.sqrt 2 * enorm x := by
  have hc : 0 ≤ Real.sqrt 2 * enorm x := mul_nonneg (Real.sqrt_nonneg 2) (enorm_nonneg x)
  rw [← NNReal.coe_mk _ hc, ← coe_nnnorm, NNReal.coe_le_coe, linfty_opNNNorm_def]
  refine Finset.sup_le fun i _ => ?_
  rw [← NNReal.coe_le_coe, NNReal.coe_sum, NNReal.coe_mk]
  simp only [coe_nnnorm, Real.norm_eq_abs]
  fin_cases i <;> simp [skew, Fin.sum_univ_succ]
  · linarith [abs_add_abs_le_sqrt_two_enorm x 2 1 (by decide)]
  · linarith [abs_add_abs_le_sqrt_two_enorm x 2 0 (by decide)]
  · linarith [abs_add_abs_le_sqrt_two_enorm x 1 0 (by decide)]

open scoped Matrix.Norms.Frobenius in
/-- In the Frobenius norm, `‖[x]ˣ‖ = √2 ‖x‖` exactly. -/
theorem skew_frobenius_norm (x : Vec3) : ‖skew x‖ = Real.sqrt 2 * enorm x := by
  rw [frobenius_norm_def]
  simp only [Real.norm_eq_abs, Real.rpow_two, sq_abs, skew_sum_sq]
  rw [← Real.sqrt_eq_rpow, Real.sqrt_mul (by norm_num), ← enorm_sq,
    Real.sqrt_sq (enorm_nonneg x)]

end Skew

section Reapplication
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

/-- Theorem 6: a right-injected horizon correction `X0 ↦ X0 * D` (with
`D = exp δˣ` in the implementation) is transported to the end of the window
by conjugation with the buffered right factor; the left factor and the
initial state are untouched. -/
theorem horizon_correction (L X0 D : A) (R : Aˣ) :
    L * (X0 * D) * (R : A) = (L * X0 * (R : A)) * ((↑R⁻¹ : A) * D * R) :=
  reapplication L X0 D R

/-- Theorem 6, Eq. (36): for continuous left and right inputs there are
invertible factors `L`, `R`, chosen once and independent of the initial
state, such that every solution of `X' = M X + X N` equals `L X(0) R`. -/
theorem flow_factors_state_independent (M N : ℝ → A)
    (hM : Continuous M) (hN : Continuous N) :
    ∃ L R : ℝ → Aˣ, L 0 = 1 ∧ R 0 = 1 ∧
      ∀ X : ℝ → A, (∀ t, HasDerivAt X (M t * X t + X t * N t) t) →
        ∀ t, X t = (L t : A) * X 0 * (R t : A) := by
  obtain ⟨L, R, hL0, hR0, hflow⟩ := exists_mixed_flows M N hM hN
  refine ⟨L, R, hL0, hR0, fun X hX t => ?_⟩
  have hu := mixed_flow_unique M N hM hN X (fun s => (L s : A) * X 0 * (R s : A))
    hX (hflow (X 0)).2 (by simp [hL0, hR0])
  exact congrFun hu t

/-- Eq. (36) with a constant left generator: the left factor is the
exponential `exp (t • M)` and the right factor is state-independent. -/
theorem flow_factors_const_left (M : A) (N : ℝ → A) (hN : Continuous N) :
    ∃ R : ℝ → Aˣ, R 0 = 1 ∧
      ∀ X : ℝ → A, (∀ t, HasDerivAt X (M * X t + X t * N t) t) →
        ∀ t, X t = exp (t • M) * X 0 * (R t : A) := by
  obtain ⟨R, hR0, hR⟩ := exists_right_unit_flow N hN
  refine ⟨R, hR0, fun X hX t => ?_⟩
  have hu := mixed_flow_unique (fun _ => M) N continuous_const hN X
    (fun s => exp (s • M) * X 0 * (R s : A)) hX
    (fun s => factor_derivative (hasDerivAt_exp_smul_const' M s) (hR s))
    (by simp [hR0])
  exact congrFun hu t

/-- Theorem 6, Eqs. (36)-(37): the flow started from the corrected state
`X(0) * D` is the uncorrected flow followed by the conjugated correction
`(R t)⁻¹ * D * R t`; no re-integration is needed. -/
theorem corrected_flow (M N : ℝ → A) (hM : Continuous M) (hN : Continuous N)
    (X X' : ℝ → A) (D : A)
    (hX : ∀ t, HasDerivAt X (M t * X t + X t * N t) t)
    (hX' : ∀ t, HasDerivAt X' (M t * X' t + X' t * N t) t)
    (h0 : X' 0 = X 0 * D) :
    ∃ R : ℝ → Aˣ, R 0 = 1 ∧ ∀ t, X' t = X t * ((↑(R t)⁻¹ : A) * D * R t) := by
  obtain ⟨L, R, _, hR0, hfac⟩ := flow_factors_state_independent M N hM hN
  refine ⟨R, hR0, fun t => ?_⟩
  rw [hfac X' hX' t, hfac X hX t, h0, horizon_correction]

end Reapplication
end GNC.Magnus
