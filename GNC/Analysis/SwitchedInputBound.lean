import GNC.Analysis.ArcGronwall

/-! Prefix input budgets and position bounds for switched trajectories.
The bounds retain each forcing magnitude and its elapsed active duration.
-/
noncomputable section
set_option autoImplicit false
open Set
namespace GNC.ArcGronwall
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def prefixBudget (nodes D : ℕ → ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  budget (fun k => min (nodes k) t) D N

theorem prefixBudget_nonneg (nodes D : ℕ → ℝ) (N : ℕ) (t : ℝ)
    (hn : Monotone nodes) (hD : ∀ k < N, 0 ≤ D k) : 0 ≤ prefixBudget nodes D N t := by
  unfold prefixBudget budget
  apply Finset.sum_nonneg
  intro k hk
  exact mul_nonneg (sub_nonneg.mpr (min_le_min_right t (hn (Nat.le_succ k))))
    (hD k (Finset.mem_range.mp hk))

theorem duration_mono {a b s t : ℝ} (hab : a ≤ b) (hst : s ≤ t) :
    min b s-min a s ≤ min b t-min a t := by
  simp only [min_def]
  split_ifs <;> linarith

theorem prefixBudget_mono (nodes D : ℕ → ℝ) (N : ℕ)
    (hn : Monotone nodes) (hD : ∀ k < N, 0 ≤ D k) :
    Monotone (prefixBudget nodes D N) := by
  intro s t hst
  unfold prefixBudget budget
  apply Finset.sum_le_sum
  intro k hk
  exact mul_le_mul_of_nonneg_right (duration_mono (hn (Nat.le_succ k)) hst)
    (hD k (Finset.mem_range.mp hk))

theorem prefixBudget_constant (nodes : ℕ → ℝ) (N : ℕ) (t B : ℝ)
    (hzero : nodes 0 = 0) (ht : t ∈ Icc (0:ℝ) (nodes N)) :
    prefixBudget nodes (fun _ => B) N t = t*B := by
  rw [prefixBudget,budget,← Finset.sum_mul,
    Finset.sum_range_sub (fun k => min (nodes k) t) N,hzero,
    min_eq_right ht.2,min_eq_left ht.1,sub_zero]

theorem prefix_bound (f : ℝ → E) (d : ℕ → ℝ → E) (nodes D : ℕ → ℝ) (N : ℕ)
    {K T : ℝ} (hK : 0 ≤ K) (hn : Monotone nodes) (hzero : nodes 0 = 0)
    (hT : T ∈ Icc (0:ℝ) (nodes N)) (hf : Continuous f)
    (hd : ∀ k < N, ContinuousOn (d k) (Icc 0 T))
    (hderiv : ∀ k < N, ∀ t ∈ Icc (0:ℝ) T,
      t ∈ Ioo (nodes k) (nodes (k+1)) → HasDerivAt f (d k t) t)
    (hD : ∀ k < N, 0 ≤ D k)
    (hbound : ∀ k < N, ∀ t ∈ Icc (0:ℝ) T, ‖d k t‖ ≤ K*‖f t‖+D k)
    (hi : f 0 = 0) :
    ‖f T‖ ≤ Real.exp (K*T)*prefixBudget nodes D N T := by
  have hzero' : min (nodes 0) T = 0 := by rw [hzero,min_eq_left hT.1]
  have hdom (k : ℕ) (t : ℝ)
      (ht : t ∈ Icc (min (nodes k) T) (min (nodes (k+1)) T)) : t ∈ Icc 0 T := by
    have hk : 0 ≤ nodes k := by rw [← hzero]; exact hn (Nat.zero_le k)
    exact ⟨(le_min hk hT.1).trans ht.1,ht.2.trans (min_le_right _ _)⟩
  have h := endpoint f d (fun k => min (nodes k) T) D N hK
    (fun i j hij => min_le_min_right T (hn hij)) hzero' hf
    (fun k hk => (hd k hk).mono (fun t ht => hdom k t ht))
    (by
      intro k hk t ht
      have htT := hdom k t (Ioo_subset_Icc_self ht)
      apply hderiv k hk t htT
      constructor
      · have hu : t < T := ht.2.trans_le (min_le_right _ _)
        rcases min_lt_iff.mp ht.1 with h | h
        · exact h
        · linarith
      · exact ht.2.trans_le (min_le_left _ _)) hD
    (fun k hk t ht => hbound k hk t (hdom k t (Ico_subset_Icc_self ht))) hi
  simpa only [min_eq_right hT.2,prefixBudget] using h

/-- Integrate a velocity bounded by an accumulated state-error budget.
No derivative at an input switch is required as an extra hypothesis. -/
theorem position (p v : ℝ → E) (nodes D : ℕ → ℝ) (N : ℕ)
    {K T : ℝ} (hK : 0 ≤ K) (hn : Monotone nodes) (hzero : nodes 0 = 0)
    (hT : T ∈ Icc (0:ℝ) (nodes N)) (hp : Continuous p) (hv : Continuous v)
    (hderiv : ∀ k < N, ∀ t ∈ Icc (0:ℝ) T,
      t ∈ Ioo (nodes k) (nodes (k+1)) → HasDerivAt p (v t) t)
    (hD : ∀ k < N, 0 ≤ D k)
    (hvbound : ∀ t ∈ Icc (0:ℝ) T,
      ‖v t‖ ≤ Real.exp (K*t)*prefixBudget nodes D N t)
    (hi : p 0 = 0) :
    ‖p T‖ ≤ T*Real.exp (K*T)*prefixBudget nodes D N T := by
  let B := Real.exp (K*T)*prefixBudget nodes D N T
  have hB : 0 ≤ B := mul_nonneg (Real.exp_pos _).le (prefixBudget_nonneg nodes D N T hn hD)
  have h := prefix_bound p (fun _ => v) nodes (fun _ => B) N (K := 0)
    (by norm_num) hn hzero hT hp (fun _ _ => hv.continuousOn) hderiv (fun _ _ => hB)
    (by
      intro k hk t ht
      simp only [zero_mul,zero_add]
      apply (hvbound t ht).trans
      exact mul_le_mul (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 hK))
        (prefixBudget_mono nodes D N hn hD ht.2)
        (prefixBudget_nonneg nodes D N t hn hD) (Real.exp_pos _).le) hi
  simpa only [zero_mul,Real.exp_zero,one_mul,prefixBudget_constant nodes N T B hzero hT,
    B,mul_assoc] using h

end GNC.ArcGronwall
