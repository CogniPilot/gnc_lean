import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-! A continuous primitive for a finite sequence of continuous input arcs.
The right derivative selects the current arc even at a switching time.
Inside an open arc the ordinary derivative is also established.
-/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology
namespace GNC.SwitchedPrimitive
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def antiderivative (u : ℝ → E) (t : ℝ) : E := ∫ s in (0:ℝ)..t, u s

theorem antiderivative_derivative {u : ℝ → E} (hu : Continuous u) (t : ℝ) :
    HasDerivAt (antiderivative u) (u t) t :=
  intervalIntegral.integral_hasDerivAt_right (hu.intervalIntegrable _ _)
    hu.aestronglyMeasurable.stronglyMeasurableAtFilter hu.continuousAt

theorem antiderivative_continuous {u : ℝ → E} (hu : Continuous u) :
    Continuous (antiderivative u) :=
  continuous_iff_continuousAt.mpr (fun t => (antiderivative_derivative hu t).continuousAt)

theorem min_derivative_right {u : ℝ → E} (hu : Continuous u) (d t : ℝ) :
    HasDerivWithinAt (fun s => antiderivative u (min d s))
      (if t < d then u t else 0) (Ici t) t := by
  by_cases ht : t < d
  · rw [if_pos ht]
    have he : (fun s => antiderivative u (min d s)) =ᶠ[𝓝 t] antiderivative u := by
      filter_upwards [Iio_mem_nhds ht] with s hs
      rw [min_eq_right hs.le]
    exact ((antiderivative_derivative hu t).congr_of_eventuallyEq he).hasDerivWithinAt
  · rw [if_neg ht]
    have he : (fun s => antiderivative u (min d s)) =ᶠ[𝓝[Ici t] t]
        (fun _ => antiderivative u d) := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      rw [min_eq_left ((le_of_not_gt ht).trans hs)]
    exact (hasDerivWithinAt_const t (Ici t) (antiderivative u d)).congr_of_eventuallyEq_of_mem
      he (by simp)

def arc (u : ℝ → E) (a b t : ℝ) : E :=
  antiderivative u (min b t)-antiderivative u (min a t)

theorem arc_continuous {u : ℝ → E} (hu : Continuous u) (a b : ℝ) :
    Continuous (arc u a b) :=
  ((antiderivative_continuous hu).comp (continuous_const.min continuous_id)).sub
    ((antiderivative_continuous hu).comp (continuous_const.min continuous_id))

theorem arc_derivative_right {u : ℝ → E} (hu : Continuous u) {a b : ℝ}
    (hab : a ≤ b) (t : ℝ) :
    HasDerivWithinAt (arc u a b) (if a ≤ t ∧ t < b then u t else 0) (Ici t) t := by
  have h := (min_derivative_right hu b t).sub (min_derivative_right hu a t)
  by_cases ha : t < a
  · simpa [arc,ha,ha.trans_le hab,not_le.mpr ha] using h
  · by_cases hb : t < b
    · simpa [arc,ha,hb,le_of_not_gt ha] using h
    · simpa [arc,ha,hb] using h

theorem min_derivative {u : ℝ → E} (hu : Continuous u) (d t : ℝ) (hne : t ≠ d) :
    HasDerivAt (fun s => antiderivative u (min d s)) (if t < d then u t else 0) t := by
  by_cases ht : t < d
  · rw [if_pos ht]
    apply (antiderivative_derivative hu t).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds ht] with s hs
    rw [min_eq_right hs.le]
  · rw [if_neg ht]
    apply (hasDerivAt_const t (antiderivative u d)).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds (lt_of_le_of_ne (le_of_not_gt ht) hne.symm)] with s hs
    rw [min_eq_left hs.le]

theorem arc_derivative {u : ℝ → E} (hu : Continuous u) {a b t : ℝ}
    (hab : a ≤ b) (ha : t ≠ a) (hb : t ≠ b) :
    HasDerivAt (arc u a b) (if a ≤ t ∧ t < b then u t else 0) t := by
  have h := (min_derivative hu b t hb).sub (min_derivative hu a t ha)
  by_cases hta : t < a
  · simpa [arc,hta,hta.trans_le hab,not_le.mpr hta] using h
  · by_cases htb : t < b
    · simpa [arc,hta,htb,le_of_not_gt hta] using h
    · simpa [arc,hta,htb] using h

def primitive (u : ℕ → ℝ → E) (nodes : ℕ → ℝ) (N : ℕ) (t : ℝ) : E :=
  ∑ k ∈ Finset.range N, arc (u k) (nodes k) (nodes (k+1)) t

def rate (u : ℕ → ℝ → E) (nodes : ℕ → ℝ) (N : ℕ) (t : ℝ) : E :=
  ∑ k ∈ Finset.range N, if nodes k ≤ t ∧ t < nodes (k+1) then u k t else 0

theorem primitive_continuous (u : ℕ → ℝ → E) (nodes : ℕ → ℝ) (N : ℕ)
    (hu : ∀ k < N, Continuous (u k)) : Continuous (primitive u nodes N) := by
  apply continuous_finset_sum
  intro k hk
  exact arc_continuous (hu k (Finset.mem_range.mp hk)) _ _

theorem primitive_derivative_right (u : ℕ → ℝ → E) (nodes : ℕ → ℝ) (N : ℕ)
    (hu : ∀ k < N, Continuous (u k)) (hn : Monotone nodes) (t : ℝ) :
    HasDerivWithinAt (primitive u nodes N) (rate u nodes N t) (Ici t) t := by
  apply HasDerivWithinAt.fun_sum
  intro k hk
  exact arc_derivative_right (hu k (Finset.mem_range.mp hk)) (hn (Nat.le_succ k)) t

theorem primitive_zero (u : ℕ → ℝ → E) (nodes : ℕ → ℝ) (N : ℕ)
    (hn : Monotone nodes) (hzero : nodes 0 = 0) : primitive u nodes N 0 = 0 := by
  apply Finset.sum_eq_zero
  intro k hk
  have ha : 0 ≤ nodes k := by rw [← hzero]; exact hn (Nat.zero_le k)
  have hb : 0 ≤ nodes (k+1) := by rw [← hzero]; exact hn (Nat.zero_le (k+1))
  simp [arc,min_eq_right ha,min_eq_right hb]

theorem rate_eq (u : ℕ → ℝ → E) (nodes : ℕ → ℝ) {N k : ℕ} {t : ℝ}
    (hn : Monotone nodes) (hk : k < N) (ht : t ∈ Ico (nodes k) (nodes (k+1))) :
    rate u nodes N t = u k t := by
  unfold rate
  rw [Finset.sum_eq_single k]
  · simp [ht.1,ht.2]
  · intro j hj hjk
    have hj : j < N := Finset.mem_range.mp hj
    by_cases hjl : j < k
    · have hbj : nodes (j+1) ≤ t := (hn (by omega)).trans ht.1
      simp [not_lt.mpr hbj]
    · have haj : t < nodes j := ht.2.trans_le (hn (by omega))
      simp [not_le.mpr haj]
  · intro h
    exact False.elim (h (Finset.mem_range.mpr hk))

theorem locate (nodes : ℕ → ℝ) {N : ℕ} {t : ℝ}
    (ht : t ∈ Ico (nodes 0) (nodes N)) : ∃ k < N, t ∈ Ico (nodes k) (nodes (k+1)) := by
  induction N with
  | zero => exact False.elim (not_lt_of_ge ht.1 ht.2)
  | succ N ih =>
    by_cases h : t < nodes N
    · obtain ⟨k,hk,htk⟩ := ih ⟨ht.1,h⟩
      exact ⟨k,by omega,htk⟩
    · exact ⟨N,by omega,le_of_not_gt h,ht.2⟩

theorem rate_bound (u : ℕ → ℝ → E) (nodes : ℕ → ℝ) {N : ℕ} {B t : ℝ}
    (hn : Monotone nodes) (ht : t ∈ Ico (nodes 0) (nodes N))
    (hu : ∀ k < N, t ∈ Ico (nodes k) (nodes (k+1)) → ‖u k t‖ ≤ B) :
    ‖rate u nodes N t‖ ≤ B := by
  obtain ⟨k,hk,htk⟩ := locate nodes ht
  rw [rate_eq u nodes hn hk htk]
  exact hu k hk htk

theorem primitive_derivative (u : ℕ → ℝ → E) (nodes : ℕ → ℝ) {N k : ℕ} {t : ℝ}
    (hu : ∀ j < N, Continuous (u j)) (hn : Monotone nodes)
    (hk : k < N) (ht : t ∈ Ioo (nodes k) (nodes (k+1))) :
    HasDerivAt (primitive u nodes N) (u k t) t := by
  have hne (j : ℕ) : t ≠ nodes j := by
    by_cases hj : j ≤ k
    · exact ne_of_gt ((hn hj).trans_lt ht.1)
    · exact ne_of_lt (ht.2.trans_le (hn (by omega)))
  rw [← rate_eq u nodes hn hk ⟨ht.1.le,ht.2⟩]
  apply HasDerivAt.fun_sum
  intro j hj
  exact arc_derivative (hu j (Finset.mem_range.mp hj)) (hn (Nat.le_succ j)) (hne j) (hne (j+1))

end GNC.SwitchedPrimitive
