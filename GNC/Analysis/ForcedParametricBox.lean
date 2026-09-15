import GNC.Analysis.ParametricBox
import GNC.Analysis.TimeDependentODE
import GNC.Analysis.SwitchedPrimitive

/-! Full polynomial-field first-exit certificate with a bounded time-varying
additive input. The input is bounded only inside the proposed state region;
the theorem establishes that region. It does not replace the input history
by a constant uncertain parameter or assume piecewise-constant inputs.
The step's defect budget includes both the full candidate residual and input.
Continuous input histories also admit a constructed solution. Clipping is
used only in the existence proof and is proved inactive on the certified arc.
-/
noncomputable section
namespace GNC.ParametricBox
open PolynomialODE
variable {C : Type} {n : ℕ} (A : Model C)

/-- Every continuously differentiable physical trajectory with the regional
input envelope satisfies the checked polynomial tube. Existence for the
chosen nonautonomous physical/controller model is a separate obligation. -/
theorem forced_step_sound (s : Step C n) (f : Fin n → Expr n) (hs : s.Valid A f)
    (θ : ℝ) (hθ : |θ| ≤ (s.angle : ℝ)) (x : ℝ → Fin n → ℝ) (hx : Continuous x)
    (w : ℝ → Fin n → ℝ) (input : Fin n → ℚ)
    (hbudget : ∀ i, A.bound (residual A f s.coefficients i) s.duration s.angle + input i ≤ s.defect i)
    (hw : ∀ t ∈ Set.Icc (0 : ℝ) s.duration, (∀ i, |x t i| ≤ (s.region i : ℝ)) →
      ∀ i, |w t i| ≤ (input i : ℝ))
    (hd : ∀ t ∈ Set.Icc (0 : ℝ) s.duration, (∀ i, |x t i| ≤ (s.region i : ℝ)) →
      HasDerivAt x (fun i => (f i).value (x t) + w t i) t)
    (hi : ∀ i, |x 0 i - curve A s.coefficients θ 0 i| ≤ (s.initialError i : ℝ)) :
    ∀ t ∈ Set.Icc (0 : ℝ) s.duration, ∀ i,
      |x t i - curve A s.coefficients θ t i| < (s.error i : ℝ) := by
  let p := curve A s.coefficients θ
  let v := curve A (fun i => A.derivative (s.coefficients i)) θ
  have hB (i) : (0 : ℝ) < s.error i := by exact_mod_cast (hs.2.2 i).2.2.1
  have hM (i) : 0 ≤ s.region i := (hs.2.2 i).1
  have hBn (i) : 0 ≤ s.error i := (hs.2.2 i).2.2.1.le
  have hC (i) : (0 : ℝ) ≤ (f i).differenceMajorant s.region s.error + s.defect i := by
    exact_mod_cast add_nonneg ((f i).differenceMajorant_nonneg hM hBn) (hs.2.2 i).2.2.2.1
  have hclose (i) : (s.initialError i : ℝ) + (s.duration : ℝ) *
      ((f i).differenceMajorant s.region s.error + s.defect i) < s.error i := by
    exact_mod_cast (hs.2.2 i).2.2.2.2.1
  have hp : Continuous p := continuous_iff_continuousAt.mpr
    (fun t => (curve_derivative A s.coefficients θ t).continuousAt)
  have hpoly (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) s.duration) (i : Fin n) :
      |p t i| + (s.error i : ℝ) ≤ s.region i := by
    have hb := A.bound_sound (s.coefficients i)
      (show |t| ≤ (s.duration : ℝ) by rw [abs_of_nonneg ht.1]; exact ht.2) hθ
    have hr : (A.bound (s.coefficients i) s.duration s.angle : ℝ) + s.error i ≤ s.region i := by
      exact_mod_cast (hs.2.2 i).2.2.2.2.2.1
    change |p t i| ≤ _ at hb
    linarith
  have hregion (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) s.duration)
      (herr : ∀ i, |x t i - p t i| ≤ (s.error i : ℝ)) (i : Fin n) :
      |x t i| ≤ (s.region i : ℝ) := by
    have ha := abs_add_le (x t i - p t i) (p t i)
    rw [sub_add_cancel] at ha
    linarith [herr i, hpoly t ht i]
  apply BoxCertificate.response (fun t => x t - p t)
    (fun t i => (f i).value (x t) + w t i - v t i) (fun i => (s.error i : ℝ))
    (fun i => (f i).differenceMajorant s.region s.error + s.defect i)
    (fun i => (s.initialError i : ℝ)) (by exact_mod_cast hs.1) hB hC hclose (hx.sub hp) hi
  · intro t ht herr
    exact (hd t ht (hregion t ht herr)).sub (curve_derivative A s.coefficients θ t)
  · intro t ht herr i
    have hlip := (f i).box_difference_bound hM hBn (x t) (p t)
      (hregion t ht herr) (fun j => by linarith [hpoly t ht j, hB j]) herr
    have hr := A.bound_sound (residual A f s.coefficients i)
      (show |t| ≤ (s.duration : ℝ) by rw [abs_of_nonneg ht.1]; exact ht.2) hθ
    rw [residual_value] at hr
    have hδ : (A.bound (residual A f s.coefficients i) s.duration s.angle : ℝ) + input i ≤ s.defect i := by
      exact_mod_cast hbudget i
    have hforce := hw t ht (hregion t ht herr) i
    have ha := abs_add_le ((f i).value (x t) - (f i).value (p t))
      ((f i).value (p t) - v t i)
    rw [sub_add_sub_cancel] at ha
    have hf := abs_add_le ((f i).value (x t) - v t i) (w t i)
    rw [show (f i).value (x t) - v t i + w t i =
      (f i).value (x t) + w t i - v t i by ring] at hf
    change |(f i).value (p t) - v t i| ≤ _ at hr
    linarith

/-- Every continuous input history within the componentwise contract admits
a solution of the original field on the whole certified step. The finite
clipped-field bounds are used for existence only; they do not enlarge the
computed tube. This also applies to each arc of a switched burn/coast input. -/
theorem exists_forced_step (s : Step C n) (f : Fin n → Expr n) (hs : s.Valid A f)
    {θ : ℝ} (hθ : |θ| ≤ (s.angle : ℝ)) (x₀ : Fin n → ℝ)
    (hi : ∀ i, |x₀ i-curve A s.coefficients θ 0 i| ≤ (s.initialError i : ℝ))
    (w : ℝ → Fin n → ℝ) (hwc : Continuous w) (input : Fin n → ℚ)
    (hbudget : ∀ i, A.bound (residual A f s.coefficients i) s.duration s.angle+input i ≤ s.defect i)
    (hw : ∀ t ∈ Set.Icc (0 : ℝ) s.duration, ∀ i, |w t i| ≤ (input i : ℝ))
    {R : ℚ} (hR : 0 ≤ R) (hr : ∀ i, s.region i ≤ R) :
    ∃ x : ℝ → Fin n → ℝ, Continuous x ∧ x 0 = x₀ ∧
      (∀ t ∈ Set.Icc (0 : ℝ) s.duration,
        HasDerivAt x (fun i => (f i).value (x t)+w t i) t) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) s.duration, ∀ i,
        |x t i-curve A s.coefficients θ t i| < (s.error i : ℝ)) := by
  let k : Fin n → NNReal := fun i => ⟨(f i).slope R, by exact_mod_cast (f i).slope_nonneg hR⟩
  let l : Fin n → NNReal := fun i => ⟨(f i).majorant R, by exact_mod_cast (f i).majorant_nonneg hR⟩
  have hK (i : Fin n) : ((f i).slope R : ℝ) ≤ (∑ j, k j : NNReal) := by
    exact_mod_cast (Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => (k j).coe_nonneg)
      (Finset.mem_univ i) : (k i : ℝ) ≤ ∑ j, (k j : ℝ))
  have hL (i : Fin n) : ((f i).majorant R : ℝ) ≤ (∑ j, l j : NNReal) := by
    exact_mod_cast (Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => (l j).coe_nonneg)
      (Finset.mem_univ i) : (l i : ℝ) ≤ ∑ j, (l j : ℝ))
  have hclip := clippedField_lipschitz f hR (∑ i, k i) hK
  obtain ⟨x, hx, hx₀, hd⟩ := BoundedODE.exists_with_primitive
    (fun _ => clippedField f R) (∑ i, k i) (∑ i, l i)
    (fun _ => hclip) (hclip.continuous.comp continuous_snd)
    (fun _ y => clippedField_bound f hR (∑ i, l i) hL y)
    (SwitchedPrimitive.antiderivative w) (SwitchedPrimitive.antiderivative_continuous hwc)
    x₀ (show (0 : ℝ) ≤ s.duration by exact_mod_cast hs.1)
  have hd' (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) s.duration) :
      HasDerivAt x (clippedField f R (x t)+w t) t := by
    simpa only [Pi.add_def, sub_add_cancel] using
      (hd t ht).add (SwitchedPrimitive.antiderivative_derivative hwc t)
  have hcast (i : Fin n) : (s.region i : ℝ) ≤ R := by exact_mod_cast hr i
  have hlocal (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) s.duration)
      (hb : ∀ i, |x t i| ≤ (s.region i : ℝ)) :
      HasDerivAt x (fun i => (f i).value (x t)+w t i) t := by
    simpa only [clippedField_eq f (fun i => (hb i).trans (hcast i))] using hd' t ht
  have he := forced_step_sound A s f hs θ hθ x hx w input hbudget
    (fun t ht _ => hw t ht) hlocal (by simpa only [hx₀] using hi)
  refine ⟨x, hx, hx₀, ?_, he⟩
  intro t ht
  exact hlocal t ht (region_of_enclosure A s f hs hθ ht (x t) (fun i => (he t ht i).le))

/-- Construct a complete switched motion for every supplied family of
continuous input arcs. The same uncertain parameter is retained at all
handoffs; inputs may jump at the joins, while the state is continuous there. -/
theorem exists_forced_segments (S : ℕ → Step C n) (f : ℕ → Fin n → Expr n) (N : ℕ)
    (hvalid : ∀ j < N, (S j).Valid A (f j))
    (hjoin : ∀ j, j+1 < N → (S j).Compatible A (S (j+1)))
    (θ : ℝ) (hθ : ∀ j < N, |θ| ≤ ((S j).angle : ℝ))
    (x₀ : Fin n → ℝ)
    (hi : ∀ i, |x₀ i-curve A (S 0).coefficients θ 0 i| ≤ ((S 0).initialError i : ℝ))
    (w : ℕ → ℝ → Fin n → ℝ) (hwc : ∀ j < N, Continuous (w j)) (input : ℕ → Fin n → ℚ)
    (hbudget : ∀ j < N, ∀ i, A.bound (residual A (f j) (S j).coefficients i)
      (S j).duration (S j).angle+input j i ≤ (S j).defect i)
    (hw : ∀ j < N, ∀ t ∈ Set.Icc (0 : ℝ) (S j).duration, ∀ i, |w j t i| ≤ (input j i : ℝ))
    {R : ℚ} (hR : 0 ≤ R) (hr : ∀ j < N, ∀ i, (S j).region i ≤ R) :
    ∃ x : ℕ → ℝ → Fin n → ℝ,
      (∀ j < N, Continuous (x j)) ∧ x 0 0 = x₀ ∧
      (∀ j < N, ∀ t ∈ Set.Icc (0 : ℝ) (S j).duration,
        HasDerivAt (x j) (fun i => (f j i).value (x j t)+w j t i) t) ∧
      (∀ j < N, ∀ t ∈ Set.Icc (0 : ℝ) (S j).duration, ∀ i,
        |x j t i-curve A (S j).coefficients θ t i| < ((S j).error i : ℝ)) ∧
      (∀ j, j+1 < N → x (j+1) 0 = x j (S j).duration) := by
  induction N generalizing S f x₀ w input with
  | zero => exact ⟨fun _ _ => x₀, by simp⟩
  | succ N ih =>
    obtain ⟨y, hy, hy0, hyd, hye⟩ := exists_forced_step A (S 0) (f 0)
      (hvalid 0 (by omega)) (hθ 0 (by omega)) x₀ hi (w 0) (hwc 0 (by omega))
      (input 0) (hbudget 0 (by omega)) (hw 0 (by omega)) hR (hr 0 (by omega))
    by_cases hN : N = 0
    · subst N
      refine ⟨fun _ => y, ?_, hy0, ?_, ?_, ?_⟩
      · exact fun _ _ => hy
      · intro j hj
        have : j = 0 := by omega
        subst j
        exact hyd
      · intro j hj
        have : j = 0 := by omega
        subst j
        exact hye
      · omega
    have ht : (0 : ℝ) ≤ (S 0).duration := by exact_mod_cast (hvalid 0 (by omega)).1
    have hi' := handoff A (S 0) (S 1) (hjoin 0 (by omega)) (hθ 0 (by omega))
      (y (S 0).duration) (fun i => (hye (S 0).duration ⟨ht,le_rfl⟩ i).le)
    obtain ⟨tail, hc, h0, hd, he, hj⟩ := ih (fun j => S (j+1)) (fun j => f (j+1))
      (fun j hj => hvalid (j+1) (by omega)) (fun j hj => hjoin (j+1) (by omega))
      (fun j hj => hθ (j+1) (by omega)) (y (S 0).duration) hi'
      (fun j => w (j+1)) (fun j hj => hwc (j+1) (by omega)) (fun j => input (j+1))
      (fun j hj => hbudget (j+1) (by omega)) (fun j hj => hw (j+1) (by omega))
      (fun j hj => hr (j+1) (by omega))
    let x : ℕ → ℝ → Fin n → ℝ := fun j => Nat.casesOn j y tail
    refine ⟨x, ?_, hy0, ?_, ?_, ?_⟩
    · intro j hj
      cases j with
      | zero => exact hy
      | succ j => exact hc j (by omega)
    · intro j hj
      cases j with
      | zero => exact hyd
      | succ j => exact hd j (by omega)
    · intro j hj
      cases j with
      | zero => exact hye
      | succ j => exact he j (by omega)
    · intro j hj'
      cases j with
      | zero => exact h0
      | succ j => exact hj j (by omega)

end GNC.ParametricBox
