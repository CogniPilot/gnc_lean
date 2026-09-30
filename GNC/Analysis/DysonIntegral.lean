import GNC.Analysis.ArcGronwall
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-! An exact convergent ordered-integral representation with a full factorial
remainder, constructed directly from the actual right linear ODE. -/
noncomputable section
open Set Filter
open scoped Topology
namespace GNC.Dyson
variable {E : Type*} [NormedRing E] [NormedAlgebra ℝ E] [CompleteSpace E]

/-- n ordered terms; 0 terms gives zero, 1 term gives the identity. -/
def approx (B : ℝ → E) : ℕ → ℝ → E
  | 0, _ => 0
  | n+1, t => 1 + ∫ s in (0 : ℝ)..t, approx B n s * B s

theorem approx_continuous (B : ℝ → E) (hB : Continuous B) (n : ℕ) :
    Continuous (approx B n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    apply continuous_iff_continuousAt.mpr
    intro t
    have hc := ih.mul hB
    exact ((intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
      hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).const_add 1).continuousAt

theorem approx_error_integral (B Y : ℝ → E) (hB : Continuous B)
    (hY : ∀ t, HasDerivAt Y (Y t * B t) t) (hY0 : Y 0 = 1) (n : ℕ) (t : ℝ) :
    Y t - approx B (n+1) t = ∫ s in (0 : ℝ)..t, (Y s - approx B n s) * B s := by
  have hyc : Continuous Y := continuous_iff_continuousAt.mpr (fun t => (hY t).continuousAt)
  have hy := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hY s)
    ((hyc.mul hB).intervalIntegrable 0 t)
  simp_rw [sub_mul]
  have hs := intervalIntegral.integral_sub (μ := MeasureTheory.volume) ((hyc.mul hB).intervalIntegrable 0 t)
    (((approx_continuous B hB n).mul hB).intervalIntegrable 0 t)
  simp only [Pi.mul_apply] at hs
  rw [hs, hy, hY0]
  simp only [approx]
  abel

/-- Uniform actual-flow magnitude M gives the factorial remainder after n terms. -/
theorem approx_error_bound (B Y : ℝ → E) (hB : Continuous B)
    (hY : ∀ t, HasDerivAt Y (Y t * B t) t) (hY0 : Y 0 = 1)
    {T K M : ℝ} (hT : 0 ≤ T) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hb : ∀ t ∈ Icc 0 T, ‖B t‖ ≤ K) (hy : ∀ t ∈ Icc 0 T, ‖Y t‖ ≤ M)
    (n : ℕ) : ∀ t ∈ Icc 0 T,
      ‖Y t - approx B n t‖ ≤ M * (K*t)^n / (n.factorial : ℝ) := by
  induction n with
  | zero => intro t ht; simpa [approx] using hy t ht
  | succ n ih =>
    intro t ht
    rw [approx_error_integral B Y hB hY hY0 n t]
    have hc : Continuous (fun s : ℝ => M * K^(n+1) * s^n / (n.factorial : ℝ)) := by fun_prop
    have hi := intervalIntegral.norm_integral_le_of_norm_le (μ := MeasureTheory.volume) ht.1
      (MeasureTheory.ae_of_all _ (fun s hs => show
        ‖(Y s - approx B n s) * B s‖ ≤ M * K^(n+1) * s^n / (n.factorial : ℝ) from by
          have hsT : s ∈ Icc 0 T := ⟨hs.1.le, hs.2.trans ht.2⟩
          have hs0 : 0 ≤ s := hs.1.le
          calc
            _ ≤ ‖Y s - approx B n s‖ * ‖B s‖ := norm_mul_le _ _
            _ ≤ (M * (K*s)^n / (n.factorial : ℝ)) * K :=
              mul_le_mul (ih s hsT) (hb s hsT) (norm_nonneg _) (by positivity)
            _ = _ := by rw [mul_pow, pow_succ]; ring))
      (hc.intervalIntegrable 0 t)
    apply hi.trans_eq
    rw [intervalIntegral.integral_div, intervalIntegral.integral_const_mul, integral_pow]
    simp only [zero_pow (Nat.succ_ne_zero n), sub_zero, Nat.factorial_succ, Nat.cast_mul,
      Nat.cast_add, Nat.cast_one, mul_pow]
    field_simp
    <;> ring

/-- Exact convergence to the supplied actual ODE solution. -/
theorem approx_tendsto (B Y : ℝ → E) (hB : Continuous B)
    (hY : ∀ t, HasDerivAt Y (Y t * B t) t) (hY0 : Y 0 = 1)
    {T : ℝ} (hT : 0 ≤ T) :
    Tendsto (fun n => approx B n T) atTop (𝓝 (Y T)) := by
  have hyc : Continuous Y := continuous_iff_continuousAt.mpr (fun t => (hY t).continuousAt)
  obtain ⟨K, hb⟩ := isCompact_Icc.exists_bound_of_continuousOn (hB.continuousOn (s := Icc 0 T))
  obtain ⟨M, hy⟩ := isCompact_Icc.exists_bound_of_continuousOn (hyc.continuousOn (s := Icc 0 T))
  have hK : 0 ≤ K := (norm_nonneg _).trans (hb 0 ⟨le_rfl, hT⟩)
  have hM : 0 ≤ M := (norm_nonneg _).trans (hy 0 ⟨le_rfl, hT⟩)
  have he := approx_error_bound B Y hB hY hY0 hT hK hM hb hy
  have ht : Tendsto (fun n => M * (K*T)^n / (n.factorial : ℝ)) atTop (𝓝 0) := by
    simpa only [mul_zero, mul_div_assoc] using
      (FloorSemiring.tendsto_pow_div_factorial_atTop (K*T)).const_mul M
  have hn : Tendsto (fun n => ‖approx B n T - Y T‖) atTop (𝓝 0) :=
    squeeze_zero (fun _ => norm_nonneg _) (fun n => by rw [norm_sub_rev]; exact he n T ⟨hT, le_rfl⟩) ht
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hn


/-- A time-varying integrated majorant keeps the actual input envelope.
For norm-preserving flow take M=1. The tail then depends on integrated
slope magnitude, not the removed mean angular rate. -/
theorem approx_error_bound_majorant (B Y : ℝ → E) (b C : ℝ → ℝ)
    (hB : Continuous B) (hbcont : Continuous b)
    (hY : ∀ t, HasDerivAt Y (Y t * B t) t) (hY0 : Y 0 = 1)
    (hC : ∀ t, HasDerivAt C (b t) t) (hC0 : C 0 = 0)
    {T M : ℝ} (hT : 0 ≤ T) (hM : 0 ≤ M)
    (hb : ∀ t ∈ Icc 0 T, ‖B t‖ ≤ b t)
    (hCpos : ∀ t ∈ Icc 0 T, 0 ≤ C t)
    (hy : ∀ t ∈ Icc 0 T, ‖Y t‖ ≤ M) (n : ℕ) :
    ∀ t ∈ Icc 0 T, ‖Y t - approx B n t‖ ≤ M * (C t)^n / (n.factorial : ℝ) := by
  have hCc : Continuous C := continuous_iff_continuousAt.mpr (fun t => (hC t).continuousAt)
  induction n with
  | zero => intro t ht; simpa [approx] using hy t ht
  | succ n ih =>
    intro t ht
    rw [approx_error_integral B Y hB hY hY0 n t]
    have hc : Continuous (fun s : ℝ => M * (C s)^n / (n.factorial : ℝ) * b s) := by fun_prop
    have hi := intervalIntegral.norm_integral_le_of_norm_le (μ := MeasureTheory.volume) ht.1
      (MeasureTheory.ae_of_all _ (fun s hs => show
        ‖(Y s - approx B n s) * B s‖ ≤ M * (C s)^n / (n.factorial : ℝ) * b s from by
          have hsT : s ∈ Icc 0 T := ⟨hs.1.le, hs.2.trans ht.2⟩
          have hcs := hCpos s hsT
          calc
            _ ≤ ‖Y s - approx B n s‖ * ‖B s‖ := norm_mul_le _ _
            _ ≤ _ := mul_le_mul (ih s hsT) (hb s hsT) (norm_nonneg _) (by positivity)))
      (hc.intervalIntegrable 0 t)
    have hd (s : ℝ) : HasDerivAt
        (fun s => M * (C s)^(n+1) / ((n+1).factorial : ℝ))
        (M * (C s)^n / (n.factorial : ℝ) * b s) s := by
      convert (((hC s).pow (n+1)).const_mul M).div_const ((n+1).factorial : ℝ) using 1
      simp only [Nat.add_sub_cancel, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      have hn : (n : ℝ) + 1 ≠ 0 := by positivity
      field_simp
    apply hi.trans_eq
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s)
      (hc.intervalIntegrable 0 t)]
    simp [hC0]


/-- A supplied solution-magnitude bound is unnecessary for the constant-radius
certificate: Grönwall derives it directly from the ODE. -/
theorem flow_norm_bound [NormOneClass E] (B Y : ℝ → E)
    (hY : ∀ t, HasDerivAt Y (Y t * B t) t) (hY0 : Y 0 = 1)
    {T K : ℝ} (hT : 0 ≤ T) (hK : 0 ≤ K)
    (hb : ∀ t ∈ Icc 0 T, ‖B t‖ ≤ K) : ‖Y T‖ ≤ Real.exp (K*T) := by
  have hg := norm_le_gronwallBound_of_norm_deriv_right_le
    (fun t _ => (hY t).continuousAt.continuousWithinAt)
    (fun t _ => (hY t).hasDerivWithinAt)
    (show ‖Y 0‖ ≤ (1 : ℝ) by simp [hY0])
    (fun t ht => show ‖Y t * B t‖ ≤ K * ‖Y t‖ + 0 from by
      calc
        _ ≤ ‖Y t‖ * ‖B t‖ := norm_mul_le _ _
        _ ≤ ‖Y t‖ * K := mul_le_mul_of_nonneg_left (hb t ⟨ht.1, ht.2.le⟩) (norm_nonneg _)
        _ = _ := by ring) T ⟨hT, le_rfl⟩
  have hu := GNC.ArcGronwall.gronwall_upper (δ := 1) hK (le_refl 0) hT
  simpa using hg.trans (by simpa using hu)

theorem approx_error_bound_exp [NormOneClass E] (B Y : ℝ → E) (hB : Continuous B)
    (hY : ∀ t, HasDerivAt Y (Y t * B t) t) (hY0 : Y 0 = 1)
    {T K : ℝ} (hT : 0 ≤ T) (hK : 0 ≤ K)
    (hb : ∀ t ∈ Icc 0 T, ‖B t‖ ≤ K) (n : ℕ) :
    ‖Y T - approx B n T‖ ≤ Real.exp (K*T) * (K*T)^n / (n.factorial : ℝ) := by
  apply approx_error_bound B Y hB hY hY0 hT hK (Real.exp_pos _).le hb ?_ n T ⟨hT, le_rfl⟩
  intro t ht
  exact (flow_norm_bound B Y hY hY0 ht.1 hK (fun s hs => hb s ⟨hs.1, hs.2.trans ht.2⟩)).trans
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 hK))

end GNC.Dyson
