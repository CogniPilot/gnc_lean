import GNC.Magnus.FohParameterSensitivity

/-! First and second slope coefficients of the actual right linear ODE.
The Dyson coefficients are constructed as definite integrals. A cubic
Grönwall remainder proves the quadratic expansion without assuming any
parameter regularity or either variation equation for the original family.
-/
noncomputable section
open Set Filter Asymptotics
open scoped Topology
namespace GNC.Magnus
variable {E : Type*} [NormedRing E] [NormedAlgebra ℝ E] [CompleteSpace E]

def fohRightForcedIntegral (U : ℝ → Eˣ) (H : ℝ → E) (t : ℝ) : E :=
  (∫ s in (0 : ℝ)..t, H s * ((U s)⁻¹).val) * (U t).val

theorem foh_rightForcedIntegral_derivative (U : ℝ → Eˣ) (A H : ℝ → E)
    (hU : ∀ t, HasDerivAt (fun s => (U s).val) ((U t).val * A t) t)
    (hH : Continuous H) (t : ℝ) :
    HasDerivAt (fohRightForcedIntegral U H)
      (fohRightForcedIntegral U H t * A t + H t) t := by
  have hi : Continuous (fun t => ((U t)⁻¹).val) := continuous_iff_continuousAt.mpr
    (fun t => (foh_inverse_derivative U A hU t).continuousAt)
  have hc := hH.mul hi
  have hp := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  convert hp.mul (hU t) using 1
  simp only [fohRightForcedIntegral, Pi.mul_apply, mul_assoc, Units.inv_mul, mul_one]
  exact add_comm _ _

def fohDysonSecond (U : ℝ → Eˣ) (B : ℝ → E) : ℝ → E :=
  fohRightForcedIntegral U (fun t => fohSensitivityIntegral U B t * B t)

@[simp] theorem foh_dysonSecond_initial (U : ℝ → Eˣ) (B : ℝ → E) :
    fohDysonSecond U B 0 = 0 := by simp [fohDysonSecond, fohRightForcedIntegral]

/-- The second coefficient solves the variation equation because of its
integral definition; that equation is not assumed. -/
theorem foh_dysonSecond_derivative (U : ℝ → Eˣ) (A B : ℝ → E)
    (hU : ∀ t, HasDerivAt (fun s => (U s).val) ((U t).val * A t) t)
    (hB : Continuous B) (t : ℝ) :
    HasDerivAt (fohDysonSecond U B)
      (fohDysonSecond U B t * A t + fohSensitivityIntegral U B t * B t) t := by
  have hz : Continuous (fohSensitivityIntegral U B) := continuous_iff_continuousAt.mpr
    (fun t => (foh_sensitivityIntegral_derivative U A B hU hB t).continuousAt)
  exact foh_rightForcedIntegral_derivative U A _ hU (hz.mul hB) t

/-- Chronological ordering of the two interaction-picture insertions for
the right-composed equation. Earlier factors occur on the left. -/
theorem foh_dysonSecond_ordered_integral (U : ℝ → Eˣ) (B : ℝ → E) (T : ℝ) :
    fohDysonSecond U B T =
      (∫ s in (0 : ℝ)..T,
        (∫ u in (0 : ℝ)..s, fohConjugatedInput U B u) * fohConjugatedInput U B s) * (U T).val := by
  simp only [fohDysonSecond, fohRightForcedIntegral, fohSensitivityIntegral,
    fohConjugatedInput, mul_assoc]

omit [CompleteSpace E] in
/-- Exact second-order remainder estimate for actual trajectories. -/
theorem foh_slope_cubic_remainder_bound
    (A B : ℝ → E) (R : ℝ → ℝ → E) (Z₁ Z₂ : ℝ → E)
    {T e Ka Kb M : ℝ} (hT : 0 ≤ T) (he : |e| ≤ 1)
    (hKa : 0 ≤ Ka) (hKb : 0 ≤ Kb) (hM : 0 ≤ M)
    (hA : ∀ t ∈ Icc 0 T, ‖A t‖ ≤ Ka)
    (hB : ∀ t ∈ Icc 0 T, ‖B t‖ ≤ Kb)
    (hZb : ∀ t ∈ Icc 0 T, ‖Z₂ t‖ ≤ M)
    (hR : ∀ q t, t ∈ Icc 0 T → HasDerivAt (R q) (R q t * (A t + q • B t)) t)
    (hR0 : ∀ q, R q 0 = 1) (hZ10 : Z₁ 0 = 0) (hZ20 : Z₂ 0 = 0)
    (hZ1 : ∀ t ∈ Icc 0 T, HasDerivAt Z₁ (Z₁ t * A t + R 0 t * B t) t)
    (hZ2 : ∀ t ∈ Icc 0 T, HasDerivAt Z₂ (Z₂ t * A t + Z₁ t * B t) t) :
    ‖R e T - R 0 T - e • Z₁ T - e ^ 2 • Z₂ T‖ ≤
      (M * Kb * T * Real.exp ((Ka + Kb) * T)) * |e| ^ 3 := by
  let F : ℝ → E := fun t => R e t - R 0 t - e • Z₁ t - e ^ 2 • Z₂ t
  let D : ℝ → E := fun t => F t * (A t + e • B t) + e ^ 3 • (Z₂ t * B t)
  have hd (t : ℝ) (ht : t ∈ Icc 0 T) : HasDerivAt F (D t) t := by
    have h := (((hR e t ht).sub (hR 0 t ht)).sub ((hZ1 t ht).const_smul e)).sub
      ((hZ2 t ht).const_smul (e ^ 2))
    convert h using 1
    dsimp [D, F]
    simp only [zero_smul, add_zero, sub_mul, mul_add, mul_smul_comm, smul_mul_assoc,
      smul_add, smul_sub, smul_smul]
    module
  have hb (t : ℝ) (ht : t ∈ Ico 0 T) :
      ‖D t‖ ≤ (Ka + Kb) * ‖F t‖ + |e| ^ 3 * (M * Kb) := by
    have ht' := Ico_subset_Icc_self ht
    have hc : ‖A t + e • B t‖ ≤ Ka + Kb := by
      calc
        _ ≤ ‖A t‖ + ‖e • B t‖ := norm_add_le _ _
        _ = ‖A t‖ + |e| * ‖B t‖ := by rw [norm_smul, Real.norm_eq_abs]
        _ ≤ Ka + 1 * Kb := add_le_add (hA t ht')
          (mul_le_mul he (hB t ht') (norm_nonneg _) (by norm_num))
        _ = _ := by ring
    calc
      ‖D t‖ ≤ ‖F t * (A t + e • B t)‖ + ‖e ^ 3 • (Z₂ t * B t)‖ := norm_add_le _ _
      _ ≤ ‖F t‖ * ‖A t + e • B t‖ + |e| ^ 3 * (‖Z₂ t‖ * ‖B t‖) := by
        rw [norm_smul, Real.norm_eq_abs, abs_pow]
        exact add_le_add (norm_mul_le _ _)
          (mul_le_mul_of_nonneg_left (norm_mul_le _ _) (by positivity))
      _ ≤ ‖F t‖ * (Ka + Kb) + |e| ^ 3 * (M * Kb) :=
        add_le_add (mul_le_mul_of_nonneg_left hc (norm_nonneg _))
          (mul_le_mul_of_nonneg_left (mul_le_mul (hZb t ht') (hB t ht') (norm_nonneg _) hM)
            (by positivity))
      _ = _ := by ring
  have hg := norm_le_gronwallBound_of_norm_deriv_right_le
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hd t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (show ‖F 0‖ ≤ (0 : ℝ) by simp [F, hR0, hZ10, hZ20]) hb T ⟨hT, le_rfl⟩
  have hu := GNC.ArcGronwall.gronwall_upper (δ := 0) (add_nonneg hKa hKb)
    (mul_nonneg (by positivity : 0 ≤ |e| ^ 3) (mul_nonneg hM hKb)) hT
  simp only [sub_zero] at hg
  calc
    _ ≤ _ := hg.trans hu
    _ = _ := by ring

/-- The two constructed Dyson coefficients give a genuine cubic remainder
for every actual parameterized flow, without parameter assumptions. -/
theorem foh_actual_slope_cubic_isBigO (A B : ℝ → E) (R : ℝ → ℝ → Eˣ)
    (hA : Continuous A) (hB : Continuous B)
    (hR : ∀ e t, HasDerivAt (fun u => (R e u).val)
      ((R e t).val * (A t + e • B t)) t)
    (hR0 : ∀ e, R e 0 = 1) {T : ℝ} (hT : 0 ≤ T) :
    (fun e => (R e T).val - (R 0 T).val - e • fohSensitivityIntegral (R 0) B T -
      e ^ 2 • fohDysonSecond (R 0) B T) =O[𝓝 0] (fun e : ℝ => e ^ 3) := by
  have hu : ∀ t, HasDerivAt (fun u => (R 0 u).val) ((R 0 t).val * A t) t := by
    intro t
    simpa only [zero_smul, add_zero] using hR 0 t
  obtain ⟨Ka, ha⟩ := isCompact_Icc.exists_bound_of_continuousOn (hA.continuousOn (s := Icc 0 T))
  obtain ⟨Kb, hb⟩ := isCompact_Icc.exists_bound_of_continuousOn (hB.continuousOn (s := Icc 0 T))
  have hz : Continuous (fohDysonSecond (R 0) B) := continuous_iff_continuousAt.mpr
    (fun t => (foh_dysonSecond_derivative (R 0) A B hu hB t).continuousAt)
  obtain ⟨M, hm⟩ := isCompact_Icc.exists_bound_of_continuousOn (hz.continuousOn (s := Icc 0 T))
  have ha0 : 0 ≤ Ka := (norm_nonneg _).trans (ha 0 ⟨le_rfl, hT⟩)
  have hb0 : 0 ≤ Kb := (norm_nonneg _).trans (hb 0 ⟨le_rfl, hT⟩)
  have hm0 : 0 ≤ M := (norm_nonneg _).trans (hm 0 ⟨le_rfl, hT⟩)
  apply IsBigO.of_bound (M * Kb * T * Real.exp ((Ka + Kb) * T))
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1)] with e he
  have he' : |e| ≤ 1 := (by simpa [Metric.mem_ball, Real.dist_eq] using he : |e| < 1).le
  simpa only [Real.norm_eq_abs, abs_pow] using
    foh_slope_cubic_remainder_bound A B (fun e t => (R e t).val)
      (fohSensitivityIntegral (R 0) B) (fohDysonSecond (R 0) B) hT he' ha0 hb0 hm0 ha hb hm
      (fun e t _ => hR e t) (fun e => by simp [hR0])
      (by simp [fohSensitivityIntegral]) (foh_dysonSecond_initial _ _)
      (fun t _ => foh_sensitivityIntegral_derivative (R 0) A B hu hB t)
      (fun t _ => foh_dysonSecond_derivative (R 0) A B hu hB t)

/-- Second-order Peano expansion of the actual flow, with the actual
ordered-integral coefficient rather than an assumed variation solution. -/
theorem foh_actual_slope_quadratic_isLittleO (A B : ℝ → E) (R : ℝ → ℝ → Eˣ)
    (hA : Continuous A) (hB : Continuous B)
    (hR : ∀ e t, HasDerivAt (fun u => (R e u).val)
      ((R e t).val * (A t + e • B t)) t)
    (hR0 : ∀ e, R e 0 = 1) {T : ℝ} (hT : 0 ≤ T) :
    (fun e => (R e T).val - (R 0 T).val - e • fohSensitivityIntegral (R 0) B T -
      e ^ 2 • fohDysonSecond (R 0) B T) =o[𝓝 0] (fun e : ℝ => e ^ 2) :=
  (foh_actual_slope_cubic_isBigO A B R hA hB hR hR0 hT).trans_isLittleO
    (isLittleO_pow_pow (𝕜 := ℝ) (by norm_num : 2 < 3))

/-- The second difference quotient converges to the constructed second
Dyson coefficient. This is a Peano second variation, not an assertion
about differentiating Lean's `deriv` twice. -/
theorem foh_actual_slope_second_limit (A B : ℝ → E) (R : ℝ → ℝ → Eˣ)
    (hA : Continuous A) (hB : Continuous B)
    (hR : ∀ e t, HasDerivAt (fun u => (R e u).val)
      ((R e t).val * (A t + e • B t)) t)
    (hR0 : ∀ e, R e 0 = 1) {T : ℝ} (hT : 0 ≤ T) :
    Tendsto (fun e : ℝ => (e ^ 2)⁻¹ •
      ((R e T).val - (R 0 T).val - e • fohSensitivityIntegral (R 0) B T))
      (𝓝[≠] 0) (𝓝 (fohDysonSecond (R 0) B T)) := by
  have hz := (foh_actual_slope_quadratic_isLittleO A B R hA hB hR hR0 hT).tendsto_inv_smul_nhds_zero
  have hh := (hz.mono_left (show 𝓝[≠] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)).add_const (fohDysonSecond (R 0) B T)
  simp only [zero_add] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with e he
  have he0 : e ≠ 0 := by simpa using he
  rw [smul_sub, smul_smul, inv_mul_cancel₀ (pow_ne_zero 2 he0), one_smul, sub_add_cancel]

/-- First derivative and second difference quotient, both proved from the
actual family time ODE and the integral construction. -/
theorem foh_actual_slope_variations (A B : ℝ → E) (R : ℝ → ℝ → Eˣ)
    (hA : Continuous A) (hB : Continuous B)
    (hR : ∀ e t, HasDerivAt (fun u => (R e u).val)
      ((R e t).val * (A t + e • B t)) t)
    (hR0 : ∀ e, R e 0 = 1) {T : ℝ} (hT : 0 ≤ T) :
    HasDerivAt (fun e => (R e T).val) (fohSensitivityIntegral (R 0) B T) 0 ∧
    Tendsto (fun e : ℝ => (e ^ 2)⁻¹ •
      ((R e T).val - (R 0 T).val - e • fohSensitivityIntegral (R 0) B T))
      (𝓝[≠] 0) (𝓝 (fohDysonSecond (R 0) B T)) :=
  ⟨foh_parameter_integral_hasDerivAt A B R hA hB hR hR0 hT,
    foh_actual_slope_second_limit A B R hA hB hR hR0 hT⟩

end GNC.Magnus
