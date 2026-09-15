import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.ODE.Gronwall

/-! Existence for continuous linear ODEs. Local existence and uniqueness
use mathlib's Picard–Lindelöf and Grönwall theorems. -/
noncomputable section
open Set Metric Filter
open scoped Topology NNReal
namespace GNC.LinearODE
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def SolutionOn (A : ℝ → E →L[ℝ] E) (f : ℝ → E) (s : Set ℝ) : Prop :=
  ∀ t ∈ s, HasDerivAt f (A t (f t)) t

theorem SolutionOn.mono {A : ℝ → E →L[ℝ] E} {f : ℝ → E} {s t : Set ℝ}
    (hf : SolutionOn A f s) (ht : t ⊆ s) : SolutionOn A f t := fun x hx => hf x (ht hx)

def step (K : ℝ≥0) : ℝ := 1/(2*((K:ℝ)+1))

theorem step_pos (K : ℝ≥0) : 0 < step K := by unfold step; positivity

/-- The existence time is independent of the initial state for a globally
bounded continuous linear coefficient. -/
theorem local_solution (A : ℝ → E →L[ℝ] E) (hA : Continuous A)
    (K : ℝ≥0) (hK : ∀ t, ‖A t‖ ≤ K) (t₀ : ℝ) (x : E) :
    ∃ f : ℝ → E, f t₀ = x ∧ SolutionOn A f (Ioo (t₀-step K) (t₀+step K)) := by
  let a : ℝ≥0 := ⟨‖x‖+1, by positivity⟩
  let L : ℝ≥0 := ⟨K*(2*‖x‖+1), by positivity⟩
  have he := step_pos K
  let tbase : Icc (t₀-step K) (t₀+step K) := ⟨t₀, by constructor <;> linarith⟩
  have hp : IsPicardLindelof (fun t y => A t y) tbase x a 0 L K := by
    constructor
    · intro t _
      exact (ContinuousLinearMap.lipschitzWith_of_opNorm_le (hK t)).lipschitzOnWith
    · intro y _
      exact (hA.clm_apply continuous_const).continuousOn
    · intro t _ y hy
      have hxy : ‖y-x‖ ≤ ‖x‖+1 := mem_closedBall_iff_norm.mp hy
      have hyb : ‖y‖ ≤ 2*‖x‖+1 := by linarith [norm_le_norm_sub_add y x]
      exact le_trans ((A t).le_opNorm y) (mul_le_mul (hK t) hyb (norm_nonneg y) K.2)
    · change (K:ℝ)*(2*‖x‖+1)*max (t₀+step K-t₀) (t₀-(t₀-step K)) ≤ ‖x‖+1-0
      simp only [add_sub_cancel_left, sub_sub_cancel, max_self, sub_zero]
      unfold step
      rw [← mul_div_assoc, div_le_iff₀ (by positivity : 0 < 2*((K:ℝ)+1))]
      nlinarith only [norm_nonneg x, show (0:ℝ) ≤ K from K.2]
  obtain ⟨f,hf₀,hf⟩ := hp.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  refine ⟨f,hf₀,fun t ht => ?_⟩
  exact (hf t ⟨ht.1.le,ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)

theorem unique (A : ℝ → E →L[ℝ] E) (K : ℝ≥0) (hK : ∀ t, ‖A t‖ ≤ K)
    {f g : ℝ → E} {a b t₀ : ℝ} (hf : SolutionOn A f (Ioo a b))
    (hg : SolutionOn A g (Ioo a b)) (ht : t₀ ∈ Ioo a b) (heq : f t₀ = g t₀) :
    EqOn f g (Ioo a b) :=
  ODE_solution_unique_of_mem_Ioo (s := fun _ => univ)
    (fun t _ => (ContinuousLinearMap.lipschitzWith_of_opNorm_le (hK t)).lipschitzOnWith)
    ht (fun t ht => ⟨hf t ht,mem_univ _⟩) (fun t ht => ⟨hg t ht,mem_univ _⟩) heq

theorem patch_eq_right (A : ℝ → E →L[ℝ] E) (K : ℝ≥0) (hK : ∀ t, ‖A t‖ ≤ K)
    {f g : ℝ → E} {a b c d t₀ : ℝ} (hf : SolutionOn A f (Ioo a b))
    (hg : SolutionOn A g (Ioo c d)) (ht : t₀ ∈ Ioo a b ∩ Ioo c d)
    (heq : f t₀ = g t₀) : EqOn (piecewise (Ioo a b) f g) g (Ioo c d) := by
  have hfg : EqOn f g (Ioo (max a c) (min b d)) :=
    unique A K hK (hf.mono (Ioo_subset_Ioo (le_max_left ..) (min_le_left ..)))
      (hg.mono (Ioo_subset_Ioo (le_max_right ..) (min_le_right ..)))
      ⟨max_lt ht.1.1 ht.2.1,lt_min ht.1.2 ht.2.2⟩ heq
  intro t ht
  by_cases htf : t ∈ Ioo a b
  · rw [piecewise, if_pos htf]
    exact hfg ⟨max_lt htf.1 ht.1,lt_min htf.2 ht.2⟩
  · rw [piecewise, if_neg htf]

theorem patch (A : ℝ → E →L[ℝ] E) (K : ℝ≥0) (hK : ∀ t, ‖A t‖ ≤ K)
    {f g : ℝ → E} {a b c d t₀ : ℝ} (hf : SolutionOn A f (Ioo a b))
    (hg : SolutionOn A g (Ioo c d)) (ht : t₀ ∈ Ioo a b ∩ Ioo c d)
    (heq : f t₀ = g t₀) :
    SolutionOn A (piecewise (Ioo a b) f g) (Ioo a b ∪ Ioo c d) := by
  intro t ht'
  by_cases htf : t ∈ Ioo a b
  · have he : piecewise (Ioo a b) f g =ᶠ[𝓝 t] f := by
      filter_upwards [Ioo_mem_nhds htf.1 htf.2] with s hs
      exact piecewise_eq_of_mem (Ioo a b) f g hs
    rw [he.self_of_nhds]
    exact (hf t htf).congr_of_eventuallyEq he
  · have htg : t ∈ Ioo c d := ht'.resolve_left htf
    have he : piecewise (Ioo a b) f g =ᶠ[𝓝 t] g := by
      filter_upwards [Ioo_mem_nhds htg.1 htg.2] with s hs
      exact patch_eq_right A K hK hf hg ht heq hs
    rw [he.self_of_nhds]
    exact (hg t htg).congr_of_eventuallyEq he

/-- Any prescribed finite symmetric interval is covered by a solution.
The uniform local time above prevents a finite continuation endpoint. -/
theorem bounded_interval_solution (A : ℝ → E →L[ℝ] E) (hA : Continuous A)
    (K : ℝ≥0) (hK : ∀ t, ‖A t‖ ≤ K) (x : E) (r : ℝ) :
    ∃ f : ℝ → E, f 0 = x ∧ SolutionOn A f (Ioo (-r) r) := by
  let S := {a : ℝ | ∃ f : ℝ → E, f 0 = x ∧ SolutionOn A f (Ioo (-a) a)}
  have hlocal : step K ∈ S := by
    simpa [S] using local_solution A hA K hK 0 x
  have he := step_pos K
  have hunbounded : ¬BddAbove S := by
    intro hbounded
    let R := sSup S
    have hR : step K ≤ R := le_csSup hbounded hlocal
    obtain ⟨a,⟨f,hf₀,hf⟩,ha⟩ := Real.add_neg_lt_sSup
      (⟨step K,hlocal⟩ : S.Nonempty) (ε := -(step K/2)) (by linarith)
    change R+ -(step K/2) < a at ha
    let t₁ := -(R-step K/2)
    let t₂ := R-step K/2
    obtain ⟨g,hg₀,hg⟩ := local_solution A hA K hK t₁ (f t₁)
    obtain ⟨j,hj₀,hj⟩ := local_solution A hA K hK t₂ (f t₂)
    let fleft := piecewise (Ioo (-a) a) f g
    have hfleft : SolutionOn A fleft (Ioo (-(R+step K/2)) a) := by
      refine (patch A K hK hf hg (t₀ := t₁) ?_ hg₀.symm).mono ?_
      · dsimp [t₁]; constructor <;> constructor <;> linarith
      · rw [union_comm]
        apply Ioo_subset_Ioo_union_Ioo <;> dsimp [t₁] <;> linarith
    let fext := piecewise (Ioo (-(R+step K/2)) a) fleft j
    have hfext : SolutionOn A fext (Ioo (-(R+step K/2)) (R+step K/2)) := by
      refine (patch A K hK hfleft hj (t₀ := t₂) ?_ ?_).mono ?_
      · dsimp [t₂]; constructor <;> constructor <;> linarith
      · change (piecewise (Ioo (-a) a) f g) t₂ = j t₂
        rw [piecewise, if_pos (show t₂ ∈ Ioo (-a) a by dsimp [t₂]; constructor <;> linarith),hj₀]
      · apply Ioo_subset_Ioo_union_Ioo <;> dsimp [t₂] <;> linarith
    have hzero : fext 0 = x := by
      dsimp [fext, fleft]
      rw [piecewise, if_pos (show (0:ℝ) ∈ Ioo (-(R+step K/2)) a by constructor <;> linarith),
        piecewise, if_pos (show (0:ℝ) ∈ Ioo (-a) a by constructor <;> linarith),hf₀]
    have hmem : R+step K/2 ∈ S := ⟨fext,hzero,hfext⟩
    have hle := le_csSup hbounded hmem
    change R+step K/2 ≤ R at hle
    linarith
  obtain ⟨a,⟨f,hf₀,hf⟩,ha⟩ := (not_bddAbove_iff.mp hunbounded) r
  exact ⟨f,hf₀,hf.mono (Ioo_subset_Ioo (neg_le_neg ha.le) ha.le)⟩

theorem coefficient_bound (A : ℝ → E →L[ℝ] E) (hA : Continuous A) (a b : ℝ) :
    ∃ K : ℝ≥0, ∀ t ∈ Icc a b, ‖A t‖ ≤ K := by
  obtain ⟨M,hM,hbound⟩ := (isCompact_Icc.image hA).isBounded.exists_pos_norm_le
  exact ⟨⟨M,hM.le⟩,fun t ht => hbound _ ⟨t,ht,rfl⟩⟩

theorem unique_continuous (A : ℝ → E →L[ℝ] E) (hA : Continuous A)
    {f g : ℝ → E} {a b t₀ : ℝ} (hf : SolutionOn A f (Ioo a b))
    (hg : SolutionOn A g (Ioo a b)) (ht : t₀ ∈ Ioo a b) (heq : f t₀ = g t₀) :
    EqOn f g (Ioo a b) := by
  obtain ⟨K,hK⟩ := coefficient_bound A hA a b
  exact ODE_solution_unique_of_mem_Ioo (s := fun _ => univ)
    (fun t ht => (ContinuousLinearMap.lipschitzWith_of_opNorm_le (hK t ⟨ht.1.le,ht.2.le⟩)).lipschitzOnWith)
    ht (fun t ht => ⟨hf t ht,mem_univ _⟩) (fun t ht => ⟨hg t ht,mem_univ _⟩) heq

/-- Continuity suffices; no global bound on A is imposed. A bounded
extension outside the requested interval lets the local result apply. -/
theorem interval_solution (A : ℝ → E →L[ℝ] E) (hA : Continuous A) (x : E) (r : ℝ) :
    ∃ f : ℝ → E, f 0 = x ∧ SolutionOn A f (Ioo (-r) r) := by
  by_cases hr : 0 < r
  · obtain ⟨K,hK⟩ := coefficient_bound A hA (-r) r
    let B := fun t : ℝ => A (max (-r) (min r t))
    have hB : Continuous B := hA.comp (continuous_const.max (continuous_const.min continuous_id))
    have hBK : ∀ t, ‖B t‖ ≤ K := by
      intro t
      exact hK _ ⟨le_max_left ..,max_le (by linarith) (min_le_left ..)⟩
    obtain ⟨f,hf₀,hf⟩ := bounded_interval_solution B hB K hBK x r
    refine ⟨f,hf₀,fun t ht => ?_⟩
    simpa only [B, min_eq_right ht.2.le, max_eq_right ht.1.le] using hf t ht
  · refine ⟨fun _ => x,rfl,fun t ht => False.elim ?_⟩
    have := lt_trans ht.1 ht.2
    linarith

/-- A global solution of every continuous homogeneous linear ODE in a real
Banach space, with arbitrary initial value. -/
theorem exists_solution (A : ℝ → E →L[ℝ] E) (hA : Continuous A) (x : E) :
    ∃ f : ℝ → E, f 0 = x ∧ ∀ t, HasDerivAt f (A t (f t)) t := by
  choose f hf₀ hf using interval_solution A hA x
  have agree {r s : ℝ} (hr : 0 < r) (hrs : r ≤ s) : EqOn (f r) (f s) (Ioo (-r) r) :=
    unique_continuous A hA (hf r) ((hf s).mono (Ioo_subset_Ioo (neg_le_neg hrs) hrs))
      ⟨by linarith,hr⟩ (by rw [hf₀,hf₀])
  let F := fun t : ℝ => f (|t|+1) t
  have hF {r : ℝ} : EqOn F (f r) (Ioo (-r) r) := by
    intro t ht
    by_cases hrt : |t|+1 ≤ r
    · exact agree (by positivity) hrt (abs_lt.mp (by linarith : |t| < |t|+1))
    · exact (agree (by linarith [ht.1,ht.2]) (le_of_lt (lt_of_not_ge hrt)) ht).symm
  refine ⟨F,hf₀ (|0|+1),fun t => ?_⟩
  have ht : t ∈ Ioo (-(|t|+1)) (|t|+1) := abs_lt.mp (by linarith)
  have heq : F =ᶠ[𝓝 t] f (|t|+1) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    exact hF hs
  rw [heq.self_of_nhds]
  exact (hf (|t|+1) t ht).congr_of_eventuallyEq heq

end GNC.LinearODE
