import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-! Growth bounds for continuous trajectories with derivative jumps at a
finite set of switches. The forcing budget retains each arc's duration.
Released derivative extension and Grönwall theorems supply the analysis.
-/
noncomputable section
set_option autoImplicit false
open Set Filter
open scoped Topology
namespace GNC.ArcGronwall
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem derivative_right (f d : ℝ → E) {a b : ℝ}
    (hf : ContinuousOn f (Icc a b)) (hd : ContinuousOn d (Icc a b))
    (hderiv : ∀ t ∈ Ioo a b, HasDerivAt f (d t) t) :
    ∀ t ∈ Ico a b, HasDerivWithinAt f (d t) (Ici t) t := by
  intro t ht
  by_cases ha : a < t
  · exact (hderiv t ⟨ha,ht.2⟩).hasDerivWithinAt
  · have he : t = a := by linarith [ht.1]
    subst t
    have hab : a < b := ht.2
    apply hasDerivWithinAt_Ici_of_tendsto_deriv
      (s := Ioo a b) (fun s hs => (hderiv s hs).differentiableAt.differentiableWithinAt)
      ((hf a ⟨le_rfl,hab.le⟩).mono Ioo_subset_Icc_self) (Ioo_mem_nhdsGT hab)
    have hlim : Tendsto d (𝓝[>] a) (𝓝 (d a)) :=
      (hd a ⟨le_rfl,hab.le⟩).tendsto.mono_left
        (le_inf inf_le_left (le_principal_iff.mpr (Icc_mem_nhdsGT hab)))
    apply hlim.congr'
    filter_upwards [Ioo_mem_nhdsGT hab] with s hs
    exact (hderiv s hs).deriv.symm

theorem gronwall_upper {δ K D t : ℝ} (hK : 0 ≤ K) (hD : 0 ≤ D) (ht : 0 ≤ t) :
    gronwallBound δ K D t ≤ (δ+D*t)*Real.exp (K*t) := by
  by_cases hzero : K = 0
  · simp [gronwallBound,hzero]
  · have hpos : 0 < K := lt_of_le_of_ne hK (Ne.symm hzero)
    have he := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-(K*t)))
      (Real.exp_pos (K*t)).le
    rw [← Real.exp_add,neg_add_cancel,Real.exp_zero] at he
    have hf : (Real.exp (K*t)-1)/K ≤ t*Real.exp (K*t) :=
      (div_le_iff₀ hpos).mpr (by nlinarith)
    have hg := mul_le_mul_of_nonneg_left hf hD
    rw [gronwallBound_of_K_ne_0 hzero]
    calc
      _ = δ*Real.exp (K*t)+D*((Real.exp (K*t)-1)/K) := by ring
      _ ≤ δ*Real.exp (K*t)+D*(t*Real.exp (K*t)) := add_le_add le_rfl hg
      _ = _ := by ring

theorem growth (f d : ℝ → E) {a b K D B : ℝ}
    (ha : 0 ≤ a) (hK : 0 ≤ K) (hD : 0 ≤ D)
    (hf : ContinuousOn f (Icc a b)) (hd : ContinuousOn d (Icc a b))
    (hderiv : ∀ t ∈ Ioo a b, HasDerivAt f (d t) t)
    (hbound : ∀ t ∈ Ico a b, ‖d t‖ ≤ K*‖f t‖+D)
    (hi : ‖f a‖ ≤ Real.exp (K*a)*B) :
    ∀ t ∈ Icc a b, ‖f t‖ ≤ Real.exp (K*t)*(B+D*(t-a)) := by
  intro t ht
  have h := norm_le_gronwallBound_of_norm_deriv_right_le hf
    (derivative_right f d hf hd hderiv) hi hbound t ht
  have hu := gronwall_upper (δ := Real.exp (K*a)*B) hK hD (sub_nonneg.mpr ht.1)
  have hea : 1 ≤ Real.exp (K*a) := Real.one_le_exp (mul_nonneg hK ha)
  have he : Real.exp (K*a)*Real.exp (K*(t-a)) = Real.exp (K*t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hd0 : 0 ≤ D*(t-a) := mul_nonneg hD (sub_nonneg.mpr ht.1)
  have hm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hea hd0) (Real.exp_pos (K*(t-a))).le
  calc
    ‖f t‖ ≤ (Real.exp (K*a)*B+D*(t-a))*Real.exp (K*(t-a)) := h.trans hu
    _ ≤ Real.exp (K*a)*Real.exp (K*(t-a))*(B+D*(t-a)) := by nlinarith
    _ = _ := by rw [he]

def budget (nodes : ℕ → ℝ) (D : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, (nodes (k+1)-nodes k)*D k

/-- The endpoint bound uses accumulated input magnitude, including the
actual duration of every burn and coast; no common worst input is substituted. -/
theorem endpoint (f : ℝ → E) (d : ℕ → ℝ → E) (nodes D : ℕ → ℝ) (N : ℕ)
    {K : ℝ} (hK : 0 ≤ K) (hn : Monotone nodes) (hzero : nodes 0 = 0)
    (hf : Continuous f) (hd : ∀ k < N, ContinuousOn (d k) (Icc (nodes k) (nodes (k+1))))
    (hderiv : ∀ k < N, ∀ t ∈ Ioo (nodes k) (nodes (k+1)), HasDerivAt f (d k t) t)
    (hD : ∀ k < N, 0 ≤ D k)
    (hbound : ∀ k < N, ∀ t ∈ Ico (nodes k) (nodes (k+1)), ‖d k t‖ ≤ K*‖f t‖+D k)
    (hi : f 0 = 0) :
    ‖f (nodes N)‖ ≤ Real.exp (K*nodes N)*budget nodes D N := by
  induction N with
  | zero => simp [hzero,hi,budget]
  | succ N ih =>
    have hprior := ih (fun k hk => hd k (by omega))
      (fun k hk => hderiv k (by omega)) (fun k hk => hD k (by omega))
      (fun k hk => hbound k (by omega))
    have ha : 0 ≤ nodes N := by rw [← hzero]; exact hn (Nat.zero_le N)
    have h := growth f (d N) ha hK (hD N (by omega)) hf.continuousOn
      (hd N (by omega)) (hderiv N (by omega)) (hbound N (by omega)) hprior
      (nodes (N+1)) ⟨hn (by omega),le_rfl⟩
    simpa only [budget,Finset.sum_range_succ,mul_comm (D N)] using h

theorem exp_two_bound {t : ℝ} (ht : t ≤ (3/5:ℝ)) : Real.exp (2*t) ≤ 4 := by
  have he : (Real.exp (6/5:ℝ))^5 ≤ (4:ℝ)^5 := by
    calc
      (Real.exp (6/5:ℝ))^5 = Real.exp (6:ℝ) := by
        rw [← Real.exp_nat_mul]
        norm_num
      _ = (Real.exp 1)^6 := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ (3:ℝ)^6 := by gcongr; exact Real.exp_one_lt_three.le
      _ ≤ _ := by norm_num
  exact (Real.exp_le_exp.mpr (by linarith)).trans
    (le_of_pow_le_pow_left₀ (by norm_num : (5:ℕ) ≠ 0) (by norm_num : (0:ℝ) ≤ 4) he)

end GNC.ArcGronwall
