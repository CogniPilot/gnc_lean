import GNC.Analysis.SwitchedInputBound

/-! A finite-horizon comparison bound for second-order switched systems.
The actual acceleration difference may be nonlinear. A regional Lipschitz
bound and separate input budgets on each arc suffice.
-/
noncomputable section
set_option autoImplicit false
open Set
namespace GNC.ArcGronwall
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem second_order (p v : ℝ → E) (a : ℕ → ℝ → E) (nodes D : ℕ → ℝ) (N : ℕ)
    {T : ℝ} (hn : Monotone nodes) (hzero : nodes 0 = 0)
    (hT : T ∈ Icc (0:ℝ) (nodes N)) (hmax : T ≤ (3/5:ℝ))
    (hp : Continuous p) (hv : Continuous v)
    (ha : ∀ k < N, ContinuousOn (a k) (Icc 0 T))
    (hdp : ∀ k < N, ∀ t ∈ Icc (0:ℝ) T,
      t ∈ Ioo (nodes k) (nodes (k+1)) → HasDerivAt p (v t) t)
    (hdv : ∀ k < N, ∀ t ∈ Icc (0:ℝ) T,
      t ∈ Ioo (nodes k) (nodes (k+1)) → HasDerivAt v (a k t) t)
    (hD : ∀ k < N, 0 ≤ D k)
    (hbound : ∀ k < N, ∀ t ∈ Icc (0:ℝ) T, ‖a k t‖ ≤ 4*‖p t‖+D k)
    (hip : p 0 = 0) (hiv : v 0 = 0) :
    ‖p T‖ ≤ 4*T*prefixBudget nodes D N T ∧
    ‖v T‖ ≤ 4*prefixBudget nodes D N T := by
  let f : ℝ → E × E := fun t => ((2:ℝ) • p t,v t)
  let d : ℕ → ℝ → E × E := fun k t => ((2:ℝ) • v t,a k t)
  have hf : Continuous f := (hp.const_smul (2:ℝ)).prodMk hv
  have hd (k : ℕ) (hk : k < N) : ContinuousOn (d k) (Icc 0 T) :=
    ((hv.const_smul (2:ℝ)).continuousOn).prodMk (ha k hk)
  have hderiv (k : ℕ) (hk : k < N) (t : ℝ) (ht : t ∈ Icc (0:ℝ) T)
      (ha : t ∈ Ioo (nodes k) (nodes (k+1))) : HasDerivAt f (d k t) t :=
    ((hdp k hk t ht ha).const_smul (2:ℝ)).prodMk (hdv k hk t ht ha)
  have hb (k : ℕ) (hk : k < N) (t : ℝ) (ht : t ∈ Icc (0:ℝ) T) :
      ‖d k t‖ ≤ 2*‖f t‖+D k := by
    have h1 := norm_fst_le (f t)
    have h2 := norm_snd_le (f t)
    change ‖(2:ℝ) • p t‖ ≤ ‖f t‖ at h1
    change ‖v t‖ ≤ ‖f t‖ at h2
    norm_num only [norm_smul,Real.norm_eq_abs] at h1
    apply norm_prod_le_iff.mpr
    constructor
    · change ‖(2:ℝ) • v t‖ ≤ _
      norm_num only [norm_smul,Real.norm_eq_abs]
      linarith [hD k hk]
    · change ‖a k t‖ ≤ _
      linarith [hbound k hk t ht]
  have hi : f 0 = 0 := by simp [f,hip,hiv]
  have hvb (s : ℝ) (hs : s ∈ Icc (0:ℝ) T) :
      ‖v s‖ ≤ Real.exp (2*s)*prefixBudget nodes D N s := by
    have hdom : Icc (0:ℝ) s ⊆ Icc 0 T := Icc_subset_Icc_right hs.2
    have h := prefix_bound f d nodes D N (K := 2) (by norm_num) hn hzero
      ⟨hs.1,hs.2.trans hT.2⟩ hf (fun k hk => (hd k hk).mono hdom)
      (fun k hk t ht => hderiv k hk t (hdom ht)) hD
      (fun k hk t ht => hb k hk t (hdom ht)) hi
    exact (norm_snd_le (f s)).trans h
  have hpb := position p v nodes D N (K := 2) (by norm_num) hn hzero hT hp hv hdp hD hvb hip
  have hI := prefixBudget_nonneg nodes D N T hn hD
  have he := exp_two_bound hmax
  constructor
  · have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he hT.1) hI
    nlinarith
  · exact (hvb T ⟨hT.1,le_rfl⟩).trans (mul_le_mul_of_nonneg_right he hI)

end GNC.ArcGronwall
