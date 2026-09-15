import GNC.Applications.ApproachGate.Specification

/-! Composition, existence and physical interpretation of the fixed
12-segment approach maneuver. Positive inverse radius is proved from the
certificate region; constraints of the polynomial lift are preserved.
-/
noncomputable section
namespace GNC.ApproachGate
open ParametricBox PolynomialODE Set

def Constraints (z : Fin 11 → ℝ) (θ phase : ℝ) : Prop :=
  inverseDefect z = 0 ∧ phaseDefect phase z = 0 ∧
    z 7 = Real.sin θ ∧ z 8 = 1-Real.cos θ

theorem initial_constraints (θ : ℝ) :
    Constraints (lift θ 0 (fun i => (initialState i : ℝ))) θ 0 := by
  refine ⟨initial_numbers θ, ?_, ?_, ?_⟩
  · change (Real.cos 0-Real.cos 0)^2+(Real.sin 0-Real.sin 0)^2 = 0
    ring
  · rfl
  · rfl

theorem constraints_preserved {z : ℝ → Fin 11 → ℝ} {T θ start : ℝ}
    {mode : Law} {u : Fin 2 → ℝ}
    (hz : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt z (rate mode u (z t)) t)
    (hU : ∀ t ∈ Icc (0 : ℝ) T, 0 < z t 6+1)
    (hi : Constraints (z 0) θ start) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    Constraints (z t) θ (start+t) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (constant_on_interval
      (fun s hs => inverse_defect_derivative (hz s hs) (ne_of_gt (hU s hs))) ht).trans hi.1
  · have h := constant_on_interval (fun s hs => phase_defect_derivative (start := start) (hz s hs)) ht
    simpa only [add_zero, hi.2.1] using h
  · exact (pointing_constraint hz ht).1.trans hi.2.2.1
  · exact (pointing_constraint hz ht).2.trans hi.2.2.2

structure Motion (mode : Law) (command : ℕ → Fin 2 → ℚ) (θ : ℝ) where
  state : ℕ → ℝ → Fin 11 → ℝ
  continuous : ∀ j < 12, Continuous (state j)
  initial : state 0 0 = lift θ 0 (fun i => (initialState i : ℝ))
  derivative : ∀ j < 12, ∀ t ∈ Icc (0 : ℝ) (stepDuration : ℝ),
    HasDerivAt (state j) (rate mode (fun i => (command j i : ℝ)) (state j t)) t
  join : ∀ j, j+1 < 12 → state (j+1) 0 = state j stepDuration

theorem Motion.constraints {mode : Law} {command : ℕ → Fin 2 → ℚ} {θ : ℝ}
    (x : Motion mode command θ)
    (hU : ∀ j < 12, ∀ t ∈ Icc (0 : ℝ) (stepDuration : ℝ), 0 < x.state j t 6+1) :
    ∀ j < 12, ∀ t ∈ Icc (0 : ℝ) (stepDuration : ℝ),
      Constraints (x.state j t) θ ((j : ℝ)*stepDuration+t) := by
  intro j
  induction j with
  | zero =>
    intro hj t ht
    have hi : Constraints (x.state 0 0) θ 0 := by rw [x.initial]; exact initial_constraints θ
    simpa using constraints_preserved (x.derivative 0 hj) (hU 0 hj) hi ht
  | succ j ih =>
    intro hj t ht
    have hj' : j < 12 := by omega
    have hi := ih hj' stepDuration (by norm_num [stepDuration])
    rw [← x.join j hj] at hi
    have hh : (j : ℝ)*stepDuration+stepDuration = ((j+1 : ℕ) : ℝ)*stepDuration := by
      push_cast
      ring
    rw [hh] at hi
    exact constraints_preserved (x.derivative (j+1) hj) (hU (j+1) hj) hi ht

/-- A certified lifted motion is a genuine spatial inverse-square trajectory.
The phase is the target's known time-dependent RTN rotation. -/
theorem Motion.physical {mode : Law} {command : ℕ → Fin 2 → ℚ} {θ : ℝ}
    (x : Motion mode command θ)
    (hU : ∀ j < 12, ∀ t ∈ Icc (0 : ℝ) (stepDuration : ℝ), 0 < x.state j t 6+1) :
    ∀ j < 12, ∀ t ∈ Icc (0 : ℝ) (stepDuration : ℝ),
      0 < CircularRendezvous3D.radius (project (x.state j t)) ∧
      HasDerivAt (fun s => project (x.state j s))
        (CircularRendezvous3D.physicalRate
          (source mode θ ((j : ℝ)*stepDuration+t) (fun i => (command j i : ℝ)))
          (project (x.state j t))) t := by
  intro j hj t ht
  have hi := x.constraints hU j hj 0 (by norm_num [stepDuration])
  simp only [add_zero] at hi
  have hr := inverse_constraint (x.derivative j hj) (hU j hj) hi.1 ht
  have hp := phase_constraint (x.derivative j hj) hi.2.1 ht
  have hs := x.constraints hU j hj t ht
  exact ⟨hr.1, project_derivative (x.derivative j hj t ht) hr.2
    hs.2.2.1 hs.2.2.2 hp.1 hp.2⟩

theorem exists_motion {C : Type} (A : Model C) (S : ℕ → Step C 11)
    (mode : Law) (command : ℕ → Fin 2 → ℚ)
    (hv : ∀ j < 12, (S j).Valid A (field mode (command j)))
    (hj : ∀ j, j+1 < 12 → (S j).Compatible A (S (j+1)))
    (hT : ∀ j < 12, (S j).duration = stepDuration)
    (hA : ∀ j < 12, (S j).angle = angle)
    (hR : ∀ j < 12, ∀ i, (S j).region i ≤ 2)
    (θ : ℝ) (hθ : |θ| ≤ (angle : ℝ))
    (hi : ∀ i, |lift θ 0 (fun i => (initialState i : ℝ)) i-
      ParametricBox.curve A (S 0).coefficients θ 0 i| ≤ ((S 0).initialError i : ℝ)) :
    ∃ x : Motion mode command θ, ∀ j < 12, ∀ t ∈ Icc (0 : ℝ) (stepDuration : ℝ), ∀ i,
      |x.state j t i-ParametricBox.curve A (S j).coefficients θ t i| < ((S j).error i : ℝ) := by
  obtain ⟨x, hc, h0, hd, he, hxj⟩ := exists_segments A S (fun j => field mode (command j)) 12 hv hj θ
    (fun j hj => by rw [hA j hj]; exact hθ) (lift θ 0 (fun i => (initialState i : ℝ))) hi
    (by norm_num : (0 : ℚ) ≤ 2) hR
  let m : Motion mode command θ := {
    state := x
    continuous := hc
    initial := h0
    derivative := by
      intro j hj t ht
      have h := hd j hj t (by simpa only [hT j hj] using ht)
      simpa only [field_value] using h
    join := by
      intro j hj
      simpa only [hT j (by omega)] using hxj j hj }
  refine ⟨m, ?_⟩
  intro j hj t ht
  exact he j hj t (by simpa only [hT j hj] using ht)

theorem motion_enclosed {C : Type} (A : Model C) (S : ℕ → Step C 11)
    (mode : Law) (command : ℕ → Fin 2 → ℚ)
    (hv : ∀ j < 12, (S j).Valid A (field mode (command j)))
    (hj : ∀ j, j+1 < 12 → (S j).Compatible A (S (j+1)))
    (hT : ∀ j < 12, (S j).duration = stepDuration)
    (hA : ∀ j < 12, (S j).angle = angle)
    (θ : ℝ) (hθ : |θ| ≤ (angle : ℝ))
    (hi : ∀ i, |lift θ 0 (fun i => (initialState i : ℝ)) i-
      ParametricBox.curve A (S 0).coefficients θ 0 i| ≤ ((S 0).initialError i : ℝ))
    (x : Motion mode command θ) :
    ∀ j < 12, ∀ t ∈ Icc (0 : ℝ) (stepDuration : ℝ), ∀ i,
      |x.state j t i-ParametricBox.curve A (S j).coefficients θ t i| < ((S j).error i : ℝ) := by
  have he := segments_sound A S (fun j => field mode (command j)) 12 hv hj θ
    (fun j hj => by rw [hA j hj]; exact hθ) x.state x.continuous
    (by
      intro j hj t ht
      have h := x.derivative j hj t (by simpa only [hT j hj] using ht)
      simpa only [field_value] using h)
    (by
      intro j hj
      simpa only [hT j (by omega)] using x.join j hj)
    (by simpa only [x.initial] using hi)
  intro j hj t ht
  exact he j hj t (by simpa only [hT j hj] using ht)

theorem positive_inverse_radius {C : Type} (A : Model C) (S : ℕ → Step C 11)
    (mode : Law) (command : ℕ → Fin 2 → ℚ)
    (hv : ∀ j < 12, (S j).Valid A (field mode (command j)))
    (hT : ∀ j < 12, (S j).duration = stepDuration)
    (hA : ∀ j < 12, (S j).angle = angle)
    (hU : ∀ j < 12, (S j).region 6 < 1)
    {θ : ℝ} (hθ : |θ| ≤ (angle : ℝ)) (x : Motion mode command θ)
    (he : ∀ j < 12, ∀ t ∈ Icc (0 : ℝ) (stepDuration : ℝ), ∀ i,
      |x.state j t i-ParametricBox.curve A (S j).coefficients θ t i| < ((S j).error i : ℝ)) :
    ∀ j < 12, ∀ t ∈ Icc (0 : ℝ) (stepDuration : ℝ), 0 < x.state j t 6+1 := by
  intro j hj t ht
  have hr := region_of_enclosure A (S j) (field mode (command j)) (hv j hj)
    (by rw [hA j hj]; exact hθ) (by simpa only [hT j hj] using ht)
    (x.state j t) (fun i => (he j hj t ht i).le) 6
  have hu : ((S j).region 6 : ℝ) < 1 := by exact_mod_cast hU j hj
  linarith [neg_abs_le (x.state j t 6)]

end GNC.ApproachGate
