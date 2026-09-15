import GNC.Planning.SmoothStep

/-! A finite sequence of constant attitude coordinates joined during coasts.
All joins are differentiable twice. The hold-value theorem telescopes the
completed increments and applies to arbitrary ordered coast schedules. -/
noncomputable section
set_option autoImplicit false
namespace GNC.Planning.CoastInterpolation
open Finset

def value (keys starts durations : ℕ → ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  keys 0+∑ i ∈ range N, SmoothStep.blend (starts i) (durations i) 0 (keys (i+1)-keys i) t
def velocity (keys starts durations : ℕ → ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  ∑ i ∈ range N, SmoothStep.blendVelocity (starts i) (durations i) 0 (keys (i+1)-keys i) t
def acceleration (keys starts durations : ℕ → ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  ∑ i ∈ range N, SmoothStep.blendAcceleration (starts i) (durations i) 0 (keys (i+1)-keys i) t

theorem value_derivative (keys starts durations : ℕ → ℝ) (N : ℕ) (t : ℝ) :
    HasDerivAt (value keys starts durations N) (velocity keys starts durations N t) t := by
  exact (HasDerivAt.fun_sum (fun i _ => SmoothStep.blend_derivative
    (starts i) (durations i) 0 (keys (i+1)-keys i) t)).const_add (keys 0)

theorem velocity_derivative (keys starts durations : ℕ → ℝ) (N : ℕ) (t : ℝ) :
    HasDerivAt (velocity keys starts durations N) (acceleration keys starts durations N t) t :=
  HasDerivAt.fun_sum (fun i _ => SmoothStep.blendVelocity_derivative
    (starts i) (durations i) 0 (keys (i+1)-keys i) t)

theorem value_continuous (keys starts durations : ℕ → ℝ) (N : ℕ) :
    Continuous (value keys starts durations N) :=
  continuous_iff_continuousAt.mpr (fun t => (value_derivative keys starts durations N t).continuousAt)

theorem velocity_continuous (keys starts durations : ℕ → ℝ) (N : ℕ) :
    Continuous (velocity keys starts durations N) :=
  continuous_iff_continuousAt.mpr (fun t => (velocity_derivative keys starts durations N t).continuousAt)

theorem acceleration_continuous (keys starts durations : ℕ → ℝ) (N : ℕ) :
    Continuous (acceleration keys starts durations N) := by
  apply continuous_finset_sum
  intro i hi
  exact (continuous_const.mul (SmoothStep.acceleration_continuous.comp
    ((continuous_id.sub continuous_const).div_const (durations i)))).div_const _

theorem value_twice_contDiff (keys starts durations : ℕ → ℝ) (N : ℕ) :
    ContDiff ℝ 2 (value keys starts durations N) := by
  have hv : deriv (value keys starts durations N) = velocity keys starts durations N :=
    funext (fun t => (value_derivative keys starts durations N t).deriv)
  have ha : deriv (velocity keys starts durations N) = acceleration keys starts durations N :=
    funext (fun t => (velocity_derivative keys starts durations N t).deriv)
  rw [show (2 : WithTop ℕ∞) = 1+1 by norm_num, contDiff_succ_iff_deriv]
  refine ⟨fun t => (value_derivative keys starts durations N t).differentiableAt,
    (by norm_num), ?_⟩
  rw [hv, contDiff_one_iff_deriv, ha]
  exact ⟨fun t => (velocity_derivative keys starts durations N t).differentiableAt,
    acceleration_continuous keys starts durations N⟩

theorem at_hold (keys starts durations : ℕ → ℝ) {N j : ℕ} {t : ℝ} (hj : j ≤ N)
    (hd : ∀ i < N, 0 < durations i)
    (hpast : ∀ i < j, starts i+durations i ≤ t)
    (hfuture : ∀ i ∈ range N, j ≤ i → t ≤ starts i) :
    value keys starts durations N t = keys j := by
  have he : ∑ i ∈ range N, SmoothStep.blend (starts i) (durations i) 0 (keys (i+1)-keys i) t =
      ∑ i ∈ range N, if i < j then keys (i+1)-keys i else 0 := by
    apply sum_congr rfl
    intro i hi
    by_cases hij : i < j
    · rw [if_pos hij]
      exact SmoothStep.blend_after (hd i (mem_range.mp hi)) (hpast i hij)
    · rw [if_neg hij]
      exact SmoothStep.blend_before (hd i (mem_range.mp hi)) (hfuture i hi (by omega))
  have hs : (range N).filter (fun i => i < j) = range j := by
    ext i
    simp only [mem_filter, mem_range]
    omega
  unfold value
  rw [he, ← sum_filter, hs, sum_range_sub]
  ring

theorem velocity_bound (keys starts durations : ℕ → ℝ) (N : ℕ) (t : ℝ)
    (hd : ∀ i < N, 0 < durations i) :
    |velocity keys starts durations N t| ≤
      ∑ i ∈ range N, |keys (i+1)-keys i| * (15/8)/durations i := by
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum (fun i hi => ?_))
  simpa only [sub_zero] using SmoothStep.blendVelocity_bound
    (a := starts i) (start := 0) (finish := keys (i+1)-keys i) (t := t) (hd i (mem_range.mp hi))

theorem acceleration_bound (keys starts durations : ℕ → ℝ) (N : ℕ) (t : ℝ)
    (hd : ∀ i < N, 0 < durations i) :
    |acceleration keys starts durations N t| ≤
      ∑ i ∈ range N, |keys (i+1)-keys i| * 15/(durations i)^2 := by
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum (fun i hi => ?_))
  simpa only [sub_zero] using SmoothStep.blendAcceleration_bound
    (a := starts i) (start := 0) (finish := keys (i+1)-keys i) (t := t) (hd i (mem_range.mp hi))

end GNC.Planning.CoastInterpolation
