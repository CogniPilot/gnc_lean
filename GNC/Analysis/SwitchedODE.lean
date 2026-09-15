import GNC.Analysis.TimeDependentODE
import GNC.Analysis.SwitchedPrimitive
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Existence and whole-horizon growth bounds with additive switched inputs.
Every input arc is continuous, but the input may jump between arcs. A single
continuous primitive absorbs all switches before applying Picard--Lindelof.
-/
noncomputable section
set_option autoImplicit false
open Set
open scoped NNReal
namespace GNC.SwitchedODE
open SwitchedPrimitive
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem exists_solution (f : ℝ → E → E) (K L : ℝ≥0)
    (hK : ∀ t, LipschitzWith K (f t))
    (hc : Continuous (fun z : ℝ × E => f z.1 z.2))
    (hL : ∀ t x, ‖f t x‖ ≤ L)
    (u : ℕ → ℝ → E) (nodes : ℕ → ℝ) (N : ℕ)
    (hu : ∀ k < N, Continuous (u k)) (hn : Monotone nodes) (hzero : nodes 0 = 0)
    (x₀ : E) :
    ∃ x : ℝ → E, Continuous x ∧ x 0 = x₀ ∧
      (∀ t ∈ Ico (0:ℝ) (nodes N), HasDerivWithinAt x
        (f t (x t)+rate u nodes N t) (Ici t) t) ∧
      ∀ k < N, ∀ t ∈ Ioo (nodes k) (nodes (k+1)),
        HasDerivAt x (f t (x t)+u k t) t := by
  have hT : 0 ≤ nodes N := by rw [← hzero]; exact hn (Nat.zero_le N)
  obtain ⟨x,hx,hx₀,hdx⟩ := BoundedODE.exists_with_primitive f K L hK hc hL
    (primitive u nodes N) (primitive_continuous u nodes N hu) x₀ hT
  refine ⟨x,hx,hx₀,?_,?_⟩
  · intro t ht
    have h := ((hdx t (Ico_subset_Icc_self ht)).hasDerivWithinAt).fun_add
      (primitive_derivative_right u nodes N hu hn t)
    simpa only [Pi.add_apply, sub_add_cancel] using h
  · intro k hk t ht
    have hdom : t ∈ Icc (0:ℝ) (nodes N) := by
      constructor
      · rw [← hzero]
        exact (hn (Nat.zero_le k)).trans ht.1.le
      · exact ht.2.le.trans (hn (by omega))
    have h := (hdx t hdom).fun_add (primitive_derivative u nodes hu hn hk ht)
    simpa only [Pi.add_apply, sub_add_cancel] using h

/-- A Grönwall bound includes every switch through right derivatives.
The two forcing budgets separately charge the continuous drift and input. -/
theorem norm_bound (f : ℝ → E → E) (u : ℕ → ℝ → E) (nodes : ℕ → ℝ)
    (N : ℕ) (K : ℝ≥0) (x : ℝ → E) {δ D₀ D₁ : ℝ}
    (hn : Monotone nodes) (hzero : nodes 0 = 0)
    (hx : Continuous x)
    (hd : ∀ t ∈ Ico (0:ℝ) (nodes N), HasDerivWithinAt x
      (f t (x t)+rate u nodes N t) (Ici t) t)
    (hK : ∀ t ∈ Ico (0:ℝ) (nodes N), LipschitzWith K (f t))
    (h₀ : ∀ t ∈ Ico (0:ℝ) (nodes N), ‖f t 0‖ ≤ D₀)
    (hu : ∀ k < N, ∀ t ∈ Ico (nodes k) (nodes (k+1)), ‖u k t‖ ≤ D₁)
    (hi : ‖x 0‖ ≤ δ) :
    ∀ t ∈ Icc (0:ℝ) (nodes N), ‖x t‖ ≤ gronwallBound δ K (D₀+D₁) t := by
  have h := norm_le_gronwallBound_of_norm_deriv_right_le
    (K := (K : ℝ)) (ε := D₀+D₁) hx.continuousOn hd hi (by
    intro t ht
    have hdiff := (hK t ht).dist_le_mul (x t) 0
    rw [dist_eq_norm,dist_zero_right] at hdiff
    have hf : ‖f t (x t)‖ ≤ (K:ℝ)*‖x t‖+D₀ := by
      have hnrm := norm_le_norm_sub_add (f t (x t)) (f t 0)
      linarith [h₀ t ht]
    have hur := rate_bound u nodes hn (by simpa only [hzero] using ht)
      (fun k hk htk => hu k hk t htk)
    exact (norm_add_le _ _).trans (by linarith))
  simpa only [sub_zero] using h

/-- A deliberately coarse rational envelope for the scaled solar error
construction. The exponential bound comes from released mathlib. -/
theorem coarse_solar_bound {t : ℝ} (ht : t ∈ Icc (0:ℝ) (3/5)) :
    gronwallBound (1/10000) 4 (1/200) t ≤ (22/625:ℝ) := by
  have he : Real.exp (4*t) ≤ 27 := by
    calc
      Real.exp (4*t) ≤ Real.exp (3:ℝ) := Real.exp_le_exp.mpr (by linarith [ht.2])
      _ = (Real.exp 1)^3 := by simpa using Real.exp_nat_mul (1:ℝ) 3
      _ ≤ 27 := by
        calc
          (Real.exp 1)^3 ≤ (3:ℝ)^3 := by
            gcongr
            exact Real.exp_one_lt_three.le
          _ = 27 := by norm_num
  norm_num [gronwallBound] at *
  linarith

end GNC.SwitchedODE
