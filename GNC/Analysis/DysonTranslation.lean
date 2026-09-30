import GNC.Analysis.DysonIntegral

/-! Actual-flow translation bounds for the triangular Peano--Baker construction.

Depth N counts generator insertions, in addition to the identity. A velocity
column consumes one insertion and a position column consumes two. Consequently
the three error powers are N+1, N, and N-1. Norm preservation of the actual
rotation is an explicit hypothesis (M=1); it is not inferred from coordinates.
The multiplication formulation also applies to embedded matrix columns.
-/
noncomputable section
open Set
namespace GNC.Dyson
variable {E : Type*} [NormedRing E] [NormedAlgebra ℝ E] [CompleteSpace E]

/-- Velocity column in the identity-plus-N-insertions triangular PB sum. -/
def velocityApprox (B a : ℝ → E) (N : ℕ) (t : ℝ) : E :=
  ∫ s in (0 : ℝ)..t, approx B N s * a s

/-- Position column in the same sum. Each time-column insertion consumes depth. -/
def positionApprox (B a : ℝ → E) : ℕ → ℝ → E
  | 0, _ => 0
  | N+1, t => ∫ s in (0 : ℝ)..t, velocityApprox B a N s

theorem velocityApprox_zero (B a : ℝ → E) (t : ℝ) :
    velocityApprox B a 0 t = 0 := by simp [velocityApprox, approx]

theorem positionApprox_one (B a : ℝ → E) (t : ℝ) :
    positionApprox B a 1 t = 0 := by simp [positionApprox, velocityApprox_zero]

theorem velocityApprox_continuous (B a : ℝ → E)
    (hB : Continuous B) (ha : Continuous a) (N : ℕ) :
    Continuous (velocityApprox B a N) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hc := (approx_continuous B hB N).mul ha
  exact (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).continuousAt

/-- The three components satisfy exactly the triangular PB depth recursion. -/
theorem triangular_depth_recursion (B a : ℝ → E) (N : ℕ) (t : ℝ) :
    (approx B (N+2) t, velocityApprox B a (N+1) t, positionApprox B a (N+1) t) =
    (1 + ∫ s in (0 : ℝ)..t, approx B (N+1) s * B s,
      ∫ s in (0 : ℝ)..t, approx B (N+1) s * a s,
      ∫ s in (0 : ℝ)..t, velocityApprox B a N s) := rfl

theorem velocityApprox_hasDerivAt (B a : ℝ → E)
    (hB : Continuous B) (ha : Continuous a) (N : ℕ) (t : ℝ) :
    HasDerivAt (velocityApprox B a N) (approx B N t * a t) t := by
  have hc := (approx_continuous B hB N).mul ha
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

theorem positionApprox_hasDerivAt (B a : ℝ → E)
    (hB : Continuous B) (ha : Continuous a) (N : ℕ) (t : ℝ) :
    HasDerivAt (positionApprox B a (N+1)) (velocityApprox B a N t) t := by
  have hc := velocityApprox_continuous B a hB ha N
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

/-- Integrating a rotation approximation transfers its uniform error with the
actual integrated acceleration magnitude, rather than a mean-rate factor. -/
theorem integral_mul_error_bound (R P a : ℝ → E) (ha : Continuous a)
    {t δ : ℝ} (ht : 0 ≤ t)
    (herr : ∀ s ∈ Icc 0 t, ‖R s - P s‖ ≤ δ) :
    ‖∫ s in (0 : ℝ)..t, (R s - P s) * a s‖ ≤
      δ * ∫ s in (0 : ℝ)..t, ‖a s‖ := by
  have hc : Continuous (fun s => δ * ‖a s‖) := continuous_const.mul ha.norm
  have hi := intervalIntegral.norm_integral_le_of_norm_le (μ := MeasureTheory.volume) ht
    (MeasureTheory.ae_of_all _ (fun s hs => show
      ‖(R s - P s) * a s‖ ≤ δ * ‖a s‖ from
        (norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right (herr s ⟨hs.1.le, hs.2⟩) (norm_nonneg _))))
    (hc.intervalIntegrable 0 t)
  simpa only [intervalIntegral.integral_const_mul] using hi

theorem velocity_error_integral (B R a v : ℝ → E)
    (hB : Continuous B) (hR : Continuous R) (ha : Continuous a)
    (hv : ∀ t, HasDerivAt v (R t * a t) t) (hv0 : v 0 = 0) (N : ℕ) (t : ℝ) :
    v t - velocityApprox B a N t =
      ∫ s in (0 : ℝ)..t, (R s - approx B N s) * a s := by
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hv s)
    ((hR.mul ha).intervalIntegrable 0 t)
  simp only [hv0, sub_zero] at hi
  simp_rw [sub_mul]
  have hs := intervalIntegral.integral_sub (μ := MeasureTheory.volume)
    ((hR.mul ha).intervalIntegrable 0 t)
    (((approx_continuous B hB N).mul ha).intervalIntegrable 0 t)
  simp only [Pi.mul_apply] at hs
  rw [hs, hi]
  rfl

theorem position_error_integral (B a v p : ℝ → E)
    (hB : Continuous B) (ha : Continuous a) (hv : Continuous v)
    (hp : ∀ t, HasDerivAt p (v t) t) (hp0 : p 0 = 0) (N : ℕ) (t : ℝ) :
    p t - positionApprox B a (N+1) t =
      ∫ s in (0 : ℝ)..t, v s - velocityApprox B a N s := by
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hp s)
    (hv.intervalIntegrable 0 t)
  simp only [hp0, sub_zero] at hi
  rw [intervalIntegral.integral_sub (hv.intervalIntegrable 0 t)
    ((velocityApprox_continuous B a hB ha N).intervalIntegrable 0 t), hi]
  rfl

/-- A uniform rotation remainder yields a velocity remainder. The acceleration
envelope is an integral bound on every prefix of the interval. -/
theorem velocity_error_bound (B R a v : ℝ → E)
    (hB : Continuous B) (hR : Continuous R) (ha : Continuous a)
    (hv : ∀ t, HasDerivAt v (R t * a t) t) (hv0 : v 0 = 0)
    {T δ A : ℝ} (hδ : 0 ≤ δ)
    (herr : ∀ t ∈ Icc 0 T, ‖R t - approx B N t‖ ≤ δ)
    (hA : ∀ t ∈ Icc 0 T, (∫ s in (0 : ℝ)..t, ‖a s‖) ≤ A) :
    ∀ t ∈ Icc 0 T, ‖v t - velocityApprox B a N t‖ ≤ δ * A := by
  intro t ht
  rw [velocity_error_integral B R a v hB hR ha hv hv0 N t]
  exact (integral_mul_error_bound R (approx B N) a ha ht.1
    (fun s hs => herr s ⟨hs.1, hs.2.trans ht.2⟩)).trans
      (mul_le_mul_of_nonneg_left (hA t ht) hδ)

/-- Full actual triangular-flow remainder at depth N+2. Writing the depth this
way avoids natural-number subtraction at the two initial exceptional depths.
R has N+3 factorial accuracy, v has N+2, and p has N+1.
The actual R ODE supplies the PB remainder; no error expansion is assumed. -/
theorem triangular_error_bound_majorant
    (B R a v p : ℝ → E) (b C : ℝ → ℝ)
    (hB : Continuous B) (ha : Continuous a) (hbcont : Continuous b)
    (hR : ∀ t, HasDerivAt R (R t * B t) t) (hR0 : R 0 = 1)
    (hv : ∀ t, HasDerivAt v (R t * a t) t) (hv0 : v 0 = 0)
    (hp : ∀ t, HasDerivAt p (v t) t) (hp0 : p 0 = 0)
    (hC : ∀ t, HasDerivAt C (b t) t) (hC0 : C 0 = 0)
    {T M ρ A : ℝ} (hT : 0 ≤ T) (hM : 0 ≤ M) (hρ : 0 ≤ ρ)
    (hb : ∀ t ∈ Icc 0 T, ‖B t‖ ≤ b t)
    (hCpos : ∀ t ∈ Icc 0 T, 0 ≤ C t)
    (hCrad : ∀ t ∈ Icc 0 T, C t ≤ ρ)
    (hmag : ∀ t ∈ Icc 0 T, ‖R t‖ ≤ M)
    (hacc : ∀ t ∈ Icc 0 T, (∫ s in (0 : ℝ)..t, ‖a s‖) ≤ A)
    (N : ℕ) :
    ‖R T - approx B (N+3) T‖ ≤ M * ρ^(N+3) / ((N+3).factorial : ℝ) ∧
    ‖v T - velocityApprox B a (N+2) T‖ ≤
      (M * ρ^(N+2) / ((N+2).factorial : ℝ)) * A ∧
    ‖p T - positionApprox B a (N+2) T‖ ≤
      T * (M * ρ^(N+1) / ((N+1).factorial : ℝ)) * A := by
  have hRc : Continuous R := continuous_iff_continuousAt.mpr (fun t => (hR t).continuousAt)
  have hvc : Continuous v := continuous_iff_continuousAt.mpr (fun t => (hv t).continuousAt)
  have he (n : ℕ) (t : ℝ) (ht : t ∈ Icc 0 T) :
      ‖R t - approx B n t‖ ≤ M * ρ^n / (n.factorial : ℝ) := by
    apply (approx_error_bound_majorant B R b C hB hbcont hR hR0 hC hC0
      hT hM hb hCpos hmag n t ht).trans
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hCpos t ht) (hCrad t ht) n) hM)
      (by positivity)
  refine ⟨he _ T ⟨hT, le_rfl⟩, ?_, ?_⟩
  · exact velocity_error_bound B R a v hB hRc ha hv hv0 (by positivity)
      (he (N+2)) hacc T ⟨hT, le_rfl⟩
  · rw [position_error_integral B a v p hB ha hvc hp hp0 (N+1) T]
    have hh := velocity_error_bound B R a v hB hRc ha hv hv0
      (N := N+1) (by positivity) (he (N+1)) hacc
    have hi := intervalIntegral.norm_integral_le_of_norm_le (μ := MeasureTheory.volume) hT
      (MeasureTheory.ae_of_all _ (fun s hs => hh s ⟨hs.1.le, hs.2⟩))
      (intervalIntegrable_const : IntervalIntegrable
        (fun _ : ℝ => M * ρ^(N+1) / ((N+1).factorial : ℝ) * A)
        MeasureTheory.volume 0 T)
    apply hi.trans_eq
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
    ring

/-- Nonnegative integral mass on a prefix is bounded by its endpoint mass. -/
theorem integral_prefix_le (b : ℝ → ℝ) (hb : Continuous b) {T A : ℝ}
    (hpos : ∀ t ∈ Icc 0 T, 0 ≤ b t)
    (hmass : (∫ t in (0 : ℝ)..T, b t) ≤ A) :
    ∀ t ∈ Icc 0 T, (∫ s in (0 : ℝ)..t, b s) ≤ A := by
  intro t ht
  apply (intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc
      (fun s hs => hpos s ⟨hs.1.le, hs.2⟩)) (hb.intervalIntegrable 0 T)).trans hmass

/-- Endpoint integral envelopes alone suffice. This is the direct actual-flow
transfer result: b majorizes the rotation generator, its integral is at most ρ,
and the acceleration-norm integral is at most A. -/
theorem triangular_error_bound_integrated
    (B R a v p : ℝ → E) (b : ℝ → ℝ)
    (hB : Continuous B) (ha : Continuous a) (hbcont : Continuous b)
    (hR : ∀ t, HasDerivAt R (R t * B t) t) (hR0 : R 0 = 1)
    (hv : ∀ t, HasDerivAt v (R t * a t) t) (hv0 : v 0 = 0)
    (hp : ∀ t, HasDerivAt p (v t) t) (hp0 : p 0 = 0)
    {T M ρ A : ℝ} (hT : 0 ≤ T) (hM : 0 ≤ M) (hρ : 0 ≤ ρ)
    (hb : ∀ t ∈ Icc 0 T, ‖B t‖ ≤ b t)
    (hmass : (∫ t in (0 : ℝ)..T, b t) ≤ ρ)
    (hmag : ∀ t ∈ Icc 0 T, ‖R t‖ ≤ M)
    (hacc : (∫ t in (0 : ℝ)..T, ‖a t‖) ≤ A) (N : ℕ) :
    ‖R T - approx B (N+3) T‖ ≤ M * ρ^(N+3) / ((N+3).factorial : ℝ) ∧
    ‖v T - velocityApprox B a (N+2) T‖ ≤
      (M * ρ^(N+2) / ((N+2).factorial : ℝ)) * A ∧
    ‖p T - positionApprox B a (N+2) T‖ ≤
      T * (M * ρ^(N+1) / ((N+1).factorial : ℝ)) * A := by
  have hbpos : ∀ t ∈ Icc 0 T, 0 ≤ b t := fun t ht => (norm_nonneg _).trans (hb t ht)
  apply triangular_error_bound_majorant B R a v p b (fun t => ∫ s in (0 : ℝ)..t, b s)
    hB ha hbcont hR hR0 hv hv0 hp hp0 ?_ (by simp) hT hM hρ hb ?_ ?_ hmag ?_ N
  · intro t
    exact intervalIntegral.integral_hasDerivAt_right (hbcont.intervalIntegrable 0 t)
      hbcont.aestronglyMeasurable.stronglyMeasurableAtFilter hbcont.continuousAt
  · intro t ht
    exact intervalIntegral.integral_nonneg ht.1 (fun s hs => hbpos s ⟨hs.1, hs.2.trans ht.2⟩)
  · exact integral_prefix_le b hbcont hbpos hmass
  · exact integral_prefix_le (fun t => ‖a t‖) ha.norm (fun _ _ => norm_nonneg _) hacc

/-- The centered unit-interval FOH slope envelope has mass one quarter. -/
theorem integral_abs_centered :
    (∫ t in (0 : ℝ)..1, |t - 1/2|) = 1/4 := by
  have hc : Continuous (fun t : ℝ => |t - 1/2|) := by fun_prop
  have hl : (∫ t in (0 : ℝ)..(1/2), |t - 1/2|) =
      ∫ t in (0 : ℝ)..(1/2), (1/2 - t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1/2)] at ht
    change |t - 1/2| = 1/2 - t
    rw [abs_of_nonpos (by linarith [ht.2])]
    ring
  have hr : (∫ t in (1/2 : ℝ)..1, |t - 1/2|) =
      ∫ t in (1/2 : ℝ)..1, (t - 1/2) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num : (1/2 : ℝ) ≤ 1)] at ht
    exact abs_of_nonneg (by linarith [ht.1])
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable 0 (1/2)) (hc.intervalIntegrable (1/2) 1), hl, hr]
  rw [intervalIntegral.integral_sub (f := fun _ : ℝ => (1/2 : ℝ)) (g := fun t : ℝ => t)
      intervalIntegrable_const (continuous_id.intervalIntegrable _ _),
    intervalIntegral.integral_sub (f := fun t : ℝ => t) (g := fun _ : ℝ => (1/2 : ℝ))
      (continuous_id.intervalIntegrable _ _) intervalIntegrable_const]
  norm_num [integral_id]

/-- Centered-FOH specialization. The coefficient L bounds the norm of the
conjugated slope (for example L=‖G‖ with an invariant operator norm).
No assertion about a particular matrix norm or basis is hidden here. -/
theorem triangular_error_bound_centered
    (B R a v p : ℝ → E)
    (hB : Continuous B) (ha : Continuous a)
    (hR : ∀ t, HasDerivAt R (R t * B t) t) (hR0 : R 0 = 1)
    (hv : ∀ t, HasDerivAt v (R t * a t) t) (hv0 : v 0 = 0)
    (hp : ∀ t, HasDerivAt p (v t) t) (hp0 : p 0 = 0)
    {M L A : ℝ} (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hb : ∀ t ∈ Icc 0 1, ‖B t‖ ≤ |t-1/2| * L)
    (hmag : ∀ t ∈ Icc 0 1, ‖R t‖ ≤ M)
    (hacc : (∫ t in (0 : ℝ)..1, ‖a t‖) ≤ A) (N : ℕ) :
    ‖R 1 - approx B (N+3) 1‖ ≤ M * (L/4)^(N+3) / ((N+3).factorial : ℝ) ∧
    ‖v 1 - velocityApprox B a (N+2) 1‖ ≤
      (M * (L/4)^(N+2) / ((N+2).factorial : ℝ)) * A ∧
    ‖p 1 - positionApprox B a (N+2) 1‖ ≤
      (M * (L/4)^(N+1) / ((N+1).factorial : ℝ)) * A := by
  have hm : (∫ t in (0 : ℝ)..1, |t-1/2| * L) ≤ L/4 := by
    rw [intervalIntegral.integral_mul_const, integral_abs_centered]
    exact le_of_eq (by ring)
  simpa only [one_mul] using triangular_error_bound_integrated
    B R a v p (fun t => |t-1/2| * L) hB ha (by fun_prop)
    hR hR0 hv hv0 hp hp0 (by norm_num) hM (by positivity) hb hm hmag hacc N

/-- Physical position in normalized time satisfies p'=T v. This version keeps
the physical hold duration explicit. Here a already includes the time-scaling
factor T, so A bounds the integrated physical acceleration impulse. -/
theorem triangular_error_bound_centered_physical
    (B R a v p : ℝ → E)
    (hB : Continuous B) (ha : Continuous a)
    (hR : ∀ t, HasDerivAt R (R t * B t) t) (hR0 : R 0 = 1)
    (hv : ∀ t, HasDerivAt v (R t * a t) t) (hv0 : v 0 = 0)
    {T M L A : ℝ} (hT : 0 ≤ T) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hp : ∀ t, HasDerivAt p (T • v t) t) (hp0 : p 0 = 0)
    (hb : ∀ t ∈ Icc 0 1, ‖B t‖ ≤ |t-1/2| * L)
    (hmag : ∀ t ∈ Icc 0 1, ‖R t‖ ≤ M)
    (hacc : (∫ t in (0 : ℝ)..1, ‖a t‖) ≤ A) (N : ℕ) :
    ‖R 1 - approx B (N+3) 1‖ ≤ M * (L/4)^(N+3) / ((N+3).factorial : ℝ) ∧
    ‖v 1 - velocityApprox B a (N+2) 1‖ ≤
      (M * (L/4)^(N+2) / ((N+2).factorial : ℝ)) * A ∧
    ‖p 1 - T • positionApprox B a (N+2) 1‖ ≤
      T * ((M * (L/4)^(N+1) / ((N+1).factorial : ℝ)) * A) := by
  have hvc : Continuous v := continuous_iff_continuousAt.mpr (fun t => (hv t).continuousAt)
  let p₀ : ℝ → E := fun t => ∫ s in (0 : ℝ)..t, v s
  have hd (t : ℝ) : HasDerivAt p₀ (v t) t :=
    intervalIntegral.integral_hasDerivAt_right (hvc.intervalIntegrable 0 t)
      hvc.aestronglyMeasurable.stronglyMeasurableAtFilter hvc.continuousAt
  obtain ⟨hr, hvb, hpb⟩ := triangular_error_bound_centered B R a v p₀ hB ha hR hR0
    hv hv0 hd (by simp [p₀]) hM hL hb hmag hacc N
  refine ⟨hr, hvb, ?_⟩
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hp s)
    ((continuous_const.smul hvc).intervalIntegrable 0 1)
  have he : p 1 = T • p₀ 1 := by
    simpa only [hp0, sub_zero, intervalIntegral.integral_smul, p₀] using hi.symm
  rw [he, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hT]
  exact mul_le_mul_of_nonneg_left hpb hT

end GNC.Dyson
