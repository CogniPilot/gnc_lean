import GNC.Control.Propellant
import GNC.Analysis.SwitchedPrimitive
import GNC.Analysis.SwitchedInputBound

/-! Exact mass and thrust schedules for finitely switched commanded
acceleration. Knots are in normalized time; the physical time scale is
included in both the accumulated impulse and the derivative. The model
allows ideal throttle switches and does not assert a slew-rate limit.
-/
noncomputable section
set_option autoImplicit false
namespace GNC.PulsePropellant
open Set ArcGronwall

def impulse (nodes amplitude : ℕ → ℝ) (N : ℕ) (timeScale s : ℝ) : ℝ :=
  timeScale*prefixBudget nodes amplitude N (s/timeScale)

def mass (nodes amplitude : ℕ → ℝ) (N : ℕ) (timeScale m₀ exhaust s : ℝ) : ℝ :=
  Propellant.remainingMass m₀ exhaust (impulse nodes amplitude N timeScale s)

def force (nodes amplitude : ℕ → ℝ) (N : ℕ) (timeScale m₀ exhaust : ℝ)
    (k : ℕ) (s : ℝ) : ℝ := mass nodes amplitude N timeScale m₀ exhaust s*amplitude k

theorem budget_primitive (nodes amplitude : ℕ → ℝ) (N : ℕ) (t : ℝ) :
    prefixBudget nodes amplitude N t =
      SwitchedPrimitive.primitive (fun k _ => amplitude k) nodes N t := by
  simp only [prefixBudget,budget,SwitchedPrimitive.primitive,SwitchedPrimitive.arc,
    SwitchedPrimitive.antiderivative,intervalIntegral.integral_const,sub_zero,
    smul_eq_mul,← sub_mul]

theorem impulse_continuous (nodes amplitude : ℕ → ℝ) (N : ℕ) (timeScale : ℝ) :
    Continuous (impulse nodes amplitude N timeScale) := by
  have h := SwitchedPrimitive.primitive_continuous (fun k _ => amplitude k) nodes N
    (fun _ _ => continuous_const)
  rw [show SwitchedPrimitive.primitive (fun k _ => amplitude k) nodes N =
    prefixBudget nodes amplitude N from funext (fun t => (budget_primitive nodes amplitude N t).symm)] at h
  exact continuous_const.mul (h.comp (continuous_id.div_const timeScale))

theorem mass_continuous (nodes amplitude : ℕ → ℝ) (N : ℕ) (timeScale m₀ exhaust : ℝ) :
    Continuous (mass nodes amplitude N timeScale m₀ exhaust) :=
  continuous_const.mul (Real.continuous_exp.comp
    ((impulse_continuous nodes amplitude N timeScale).neg.div_const exhaust))

theorem impulse_nonneg (nodes amplitude : ℕ → ℝ) (N : ℕ) (timeScale s : ℝ)
    (hn : Monotone nodes) (ha : ∀ k < N, 0 ≤ amplitude k) (hT : 0 ≤ timeScale) :
    0 ≤ impulse nodes amplitude N timeScale s :=
  mul_nonneg hT (prefixBudget_nonneg nodes amplitude N _ hn ha)

theorem mass_bounds (nodes amplitude : ℕ → ℝ) (N : ℕ) (timeScale m₀ exhaust s : ℝ)
    (hn : Monotone nodes) (ha : ∀ k < N, 0 ≤ amplitude k) (hT : 0 ≤ timeScale)
    (hm : 0 < m₀) (he : 0 < exhaust) :
    0 < mass nodes amplitude N timeScale m₀ exhaust s ∧
      mass nodes amplitude N timeScale m₀ exhaust s ≤ m₀ := by
  refine ⟨Propellant.mass_positive hm,?_⟩
  have h := Propellant.consumed_nonneg hm.le he (impulse_nonneg nodes amplitude N timeScale s hn ha hT)
  change 0 ≤ m₀-mass nodes amplitude N timeScale m₀ exhaust s at h
  linarith

theorem initial_mass (nodes amplitude : ℕ → ℝ) (N : ℕ) (timeScale m₀ exhaust : ℝ)
    (hn : Monotone nodes) (hzero : nodes 0 = 0) :
    mass nodes amplitude N timeScale m₀ exhaust 0 = m₀ := by
  have hz := SwitchedPrimitive.primitive_zero (fun k _ => amplitude k) nodes N hn hzero
  rw [← budget_primitive] at hz
  simp [mass,impulse,hz,Propellant.remainingMass]

theorem impulse_derivative (nodes amplitude : ℕ → ℝ) {N k : ℕ} {timeScale s : ℝ}
    (hn : Monotone nodes) (hk : k < N) (hT : 0 < timeScale)
    (hs : s/timeScale ∈ Ioo (nodes k) (nodes (k+1))) :
    HasDerivAt (impulse nodes amplitude N timeScale) (amplitude k) s := by
  have hd := SwitchedPrimitive.primitive_derivative (fun j _ => amplitude j) nodes
    (fun _ _ => continuous_const) hn hk hs
  rw [show SwitchedPrimitive.primitive (fun j _ => amplitude j) nodes N =
    prefixBudget nodes amplitude N from funext (fun t => (budget_primitive nodes amplitude N t).symm)] at hd
  have h := (hd.comp s ((hasDerivAt_id s).div_const timeScale)).const_mul timeScale
  convert h using 1; dsimp [impulse]
  field_simp [hT.ne']

theorem mass_flow (nodes amplitude : ℕ → ℝ) {N k : ℕ} {timeScale m₀ exhaust s : ℝ}
    (hn : Monotone nodes) (hk : k < N) (hT : 0 < timeScale)
    (hs : s/timeScale ∈ Ioo (nodes k) (nodes (k+1))) :
    HasDerivAt (mass nodes amplitude N timeScale m₀ exhaust)
      (-force nodes amplitude N timeScale m₀ exhaust k s/exhaust) s := by
  have h := Propellant.mass_derivative (m₀ := m₀) (exhaust := exhaust)
    (impulse_derivative nodes amplitude hn hk hT hs)
  convert h using 1; dsimp [mass,force]
  ring

theorem force_bounds (nodes amplitude : ℕ → ℝ) (N k : ℕ) (timeScale m₀ exhaust s limit : ℝ)
    (hn : Monotone nodes) (ha : ∀ j < N, 0 ≤ amplitude j) (hk : k < N)
    (hT : 0 ≤ timeScale) (hm : 0 < m₀) (he : 0 < exhaust)
    (hl : m₀*amplitude k ≤ limit) :
    0 ≤ force nodes amplitude N timeScale m₀ exhaust k s ∧
      force nodes amplitude N timeScale m₀ exhaust k s ≤ limit := by
  have hb := mass_bounds nodes amplitude N timeScale m₀ exhaust s hn ha hT hm he
  exact ⟨mul_nonneg hb.1.le (ha k hk),
    (mul_le_mul_of_nonneg_right hb.2 (ha k hk)).trans hl⟩

theorem delivered_acceleration (nodes amplitude : ℕ → ℝ) (N k : ℕ)
    (timeScale m₀ exhaust s : ℝ) (hm : 0 < m₀) :
    force nodes amplitude N timeScale m₀ exhaust k s /
      mass nodes amplitude N timeScale m₀ exhaust s = amplitude k := by
  unfold force
  exact mul_div_cancel_left₀ _ (Propellant.mass_positive hm).ne'

theorem final_impulse (nodes amplitude : ℕ → ℝ) (N : ℕ) {timeScale : ℝ}
    (hn : Monotone nodes) (hT : 0 < timeScale) :
    impulse nodes amplitude N timeScale (timeScale*nodes N) =
      timeScale*budget nodes amplitude N := by
  unfold impulse prefixBudget budget
  rw [mul_div_cancel_left₀ _ hT.ne']
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  dsimp only
  rw [min_eq_left (hn (by have := Finset.mem_range.mp hk; omega)),
    min_eq_left (hn (by have := Finset.mem_range.mp hk; omega))]

end GNC.PulsePropellant
