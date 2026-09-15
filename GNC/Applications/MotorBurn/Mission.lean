import GNC.Applications.MotorBurn.Specification

/-! Compose the force-commanded burn/coast certificate and reconstruct its
physical gravity and mass equations. Each local input is continuous; it may
jump at an arc boundary. State and mass pass unchanged to the next arc.
-/
noncomputable section
namespace GNC.MotorBurn
open Set ParametricBox PolynomialODE

def Constraints (z : Fin 13 → ℝ) (θ phase : ℝ) : Prop :=
  inverseDefect z = 0 ∧ phaseDefect phase z = 0 ∧
    z 7 = Real.sin θ ∧ z 8 = 1-Real.cos θ ∧ z 12 = beta

theorem constraints_initial (θ : ℝ) : Constraints (initialState θ) θ 0 :=
  ⟨(initial_constraints θ).1, (initial_constraints θ).2.1, rfl, rfl, rfl⟩

theorem constraints_preserved {z : ℝ → Fin 13 → ℝ} {T θ start on : ℝ}
    {mode : Law} {u : Fin 2 → ℝ} {w : ℝ → Vec3}
    (hz : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt z (rate mode u on (z t) (w t)) t)
    (hU : ∀ t ∈ Icc (0 : ℝ) T, 0 < z t 6+1)
    (hi : Constraints (z 0) θ start) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    Constraints (z t) θ (start+t) := by
  have hc := constant_parameters hz ht
  refine ⟨?_, ?_, hc.1.trans hi.2.2.1, hc.2.1.trans hi.2.2.2.1,
    hc.2.2.trans hi.2.2.2.2⟩
  · exact (ApproachGate.constant_on_interval
      (fun s hs => inverse_defect_derivative (hz s hs) (hU s hs).ne') ht).trans hi.1
  · have h := ApproachGate.constant_on_interval
      (fun s hs => phase_defect_derivative (start := start) (hz s hs)) ht
    simpa only [add_zero, hi.2.1] using h

theorem inverse_of_constraint (z : Fin 13 → ℝ) (hi : inverseDefect z = 0)
    (hu : 0 < z 6+1) :
    0 < CircularRendezvous3D.radius (project z) ∧
      z 6+1 = (CircularRendezvous3D.radius (project z))⁻¹ := by
  have he : ((z 6+1)⁻¹)^2 = (1+z 0)^2+z 1^2+z 2^2 := sub_eq_zero.mp hi
  have hr : CircularRendezvous3D.radius (project z) = (z 6+1)⁻¹ := by
    change Real.sqrt ((1+z 0)^2+z 1^2+z 2^2) = _
    rw [← he, Real.sqrt_sq (inv_pos.mpr hu).le]
  rw [hr, inv_inv]
  exact ⟨inv_pos.mpr hu, rfl⟩

theorem phase_of_constraint {z : Fin 13 → ℝ} {phase : ℝ} (hi : phaseDefect phase z = 0) :
    z 9 = Real.cos phase ∧ z 10 = Real.sin phase := by
  change (z 9-Real.cos phase)^2+(z 10-Real.sin phase)^2 = 0 at hi
  constructor <;> nlinarith [sq_nonneg (z 9-Real.cos phase), sq_nonneg (z 10-Real.sin phase)]

structure Motion (mode : Law) (command : ℕ → Fin 2 → ℚ) (on : ℕ → ℚ)
    (w : ℕ → ℝ → Vec3) (θ : ℝ) where
  state : ℕ → ℝ → Fin 13 → ℝ
  continuous : ∀ j < 12, Continuous (state j)
  initial : state 0 0 = initialState θ
  derivative : ∀ j < 12, ∀ t ∈ Icc (0 : ℝ) (stepDuration : ℝ),
    HasDerivAt (state j) (rate mode (fun i => (command j i : ℝ)) (on j) (state j t) (w j t)) t
  join : ∀ j, j+1 < 12 → state (j+1) 0 = state j stepDuration

theorem Motion.constraints {mode : Law} {command : ℕ → Fin 2 → ℚ} {on : ℕ → ℚ}
    {w : ℕ → ℝ → Vec3} {θ : ℝ} (x : Motion mode command on w θ)
    (hU : ∀ j < 12, ∀ t ∈ Icc (0 : ℝ) (stepDuration : ℝ), 0 < x.state j t 6+1) :
    ∀ j < 12, ∀ t ∈ Icc (0 : ℝ) (stepDuration : ℝ),
      Constraints (x.state j t) θ ((j : ℝ)*stepDuration+t) := by
  intro j
  induction j with
  | zero =>
    intro hj t ht
    have hi : Constraints (x.state 0 0) θ 0 := by rw [x.initial]; exact constraints_initial θ
    simpa using constraints_preserved (x.derivative 0 hj) (hU 0 hj) hi ht
  | succ j ih =>
    intro hj t ht
    have hi := ih (by omega) stepDuration (by norm_num [stepDuration])
    rw [← x.join j hj] at hi
    have he : (j : ℝ)*stepDuration+stepDuration = ((j+1 : ℕ) : ℝ)*stepDuration := by
      push_cast
      ring
    rw [he] at hi
    exact constraints_preserved (x.derivative (j+1) hj) (hU (j+1) hj) hi ht

def Motion.Physical {mode : Law} {command : ℕ → Fin 2 → ℚ} {on : ℕ → ℚ}
    {w : ℕ → ℝ → Vec3} {θ : ℝ} (x : Motion mode command on w θ) : Prop :=
    ∀ j < 12, ∀ t ∈ Icc (0 : ℝ) (stepDuration : ℝ),
      0 < CircularRendezvous3D.radius (project (x.state j t)) ∧
      0 < mass Orion.Propulsion.initialMass (x.state j t) ∧
      HasDerivAt (fun s => project (x.state j s))
        (CircularRendezvous3D.physicalRate
          ((1+x.state j t 11) • ApproachGate.source mode θ ((j : ℝ)*stepDuration+t)
            (fun i => (command j i : ℝ))+w j t) (project (x.state j t))) t ∧
      HasDerivAt (fun s => mass Orion.Propulsion.initialMass (x.state j s))
        (-Orion.Propulsion.initialMass*(on j : ℝ)*beta) t

/-- Actual inverse-square motion and force-driven mass depletion throughout
all arcs. The original force coefficient beta is preserved at every handoff. -/
theorem Motion.physical {mode : Law} {command : ℕ → Fin 2 → ℚ} {on : ℕ → ℚ}
    {w : ℕ → ℝ → Vec3} {θ : ℝ} (x : Motion mode command on w θ)
    (hU : ∀ j < 12, ∀ t ∈ Icc (0 : ℝ) (stepDuration : ℝ), 0 < x.state j t 6+1)
    (hM : ∀ j < 12, ∀ t ∈ Icc (0 : ℝ) (stepDuration : ℝ), 0 < 1+x.state j t 11) :
    x.Physical := by
  intro j hj t ht
  have hc := x.constraints hU j hj t ht
  have hr := inverse_of_constraint (x.state j t) hc.1 (hU j hj t ht)
  have hp := phase_of_constraint hc.2.1
  refine ⟨hr.1, mass_positive (by norm_num [Orion.Propulsion.initialMass]) _ (hM j hj t ht),
    project_derivative (x.derivative j hj t ht) hr.2 hc.2.2.1 hc.2.2.2.1 hp.1 hp.2, ?_⟩
  simpa only [hc.2.2.2.2] using mass_derivative (initialMass := Orion.Propulsion.initialMass)
    (x.derivative j hj t ht) (hM j hj t ht).ne'

theorem exists_motion {C : Type} (A : Model C) (S : ℕ → Step C 13)
    (mode : Law) (command : ℕ → Fin 2 → ℚ) (on : ℕ → ℚ) (input : ℕ → Fin 13 → ℚ)
    (hv : ∀ j < 12, (S j).Valid A (field mode (command j) (on j)))
    (hj : ∀ j, j+1 < 12 → (S j).Compatible A (S (j+1)))
    (hT : ∀ j < 12, (S j).duration = stepDuration)
    (hA : ∀ j < 12, (S j).angle = angle)
    (hR : ∀ j < 12, ∀ i, (S j).region i ≤ 2)
    (hbudget : ∀ j < 12, ∀ i, A.bound (residual A (field mode (command j) (on j))
      (S j).coefficients i) (S j).duration (S j).angle+input j i ≤ (S j).defect i)
    (θ : ℝ) (hθ : |θ| ≤ (angle : ℝ))
    (hi : ∀ i, |initialState θ i-curve A (S 0).coefficients θ 0 i| ≤ ((S 0).initialError i : ℝ))
    (w : ℕ → ℝ → Vec3) (hwc : ∀ j < 12, Continuous (w j))
    (hw : ∀ j < 12, ∀ t ∈ Icc (0 : ℝ) (stepDuration : ℝ), ∀ i,
      |inputLift (w j t) i| ≤ (input j i : ℝ)) :
    ∃ x : Motion mode command on w θ, ∀ j < 12,
      ∀ t ∈ Icc (0 : ℝ) (stepDuration : ℝ), ∀ i,
        |x.state j t i-curve A (S j).coefficients θ t i| < ((S j).error i : ℝ) := by
  have hc (j : ℕ) (hj : j < 12) : Continuous (fun t => inputLift (w j t)) := by
    apply continuous_pi
    intro i
    fin_cases i
    all_goals first
      | exact continuous_const
      | exact (continuous_apply 0).comp (hwc j hj)
      | exact (continuous_apply 1).comp (hwc j hj)
      | exact (continuous_apply 2).comp (hwc j hj)
  obtain ⟨x, hx, h0, hd, he, hjoin⟩ := exists_forced_segments A S
    (fun j => field mode (command j) (on j)) 12 hv hj θ
    (fun j hj => by rw [hA j hj]; exact hθ) (initialState θ) hi
    (fun j t => inputLift (w j t)) hc input hbudget
    (fun j hj t ht => hw j hj t (by simpa only [hT j hj] using ht))
    (by norm_num : (0 : ℚ) ≤ 2) hR
  let m : Motion mode command on w θ := {
    state := x
    continuous := hx
    initial := h0
    derivative := by
      intro j hj t ht
      have h := hd j hj t (by simpa only [hT j hj] using ht)
      simpa only [field_value, ← Pi.add_def, ← rate_input] using h
    join := by
      intro j hj
      simpa only [hT j (by omega)] using hjoin j hj }
  refine ⟨m, ?_⟩
  intro j hj t ht
  exact he j hj t (by simpa only [hT j hj] using ht)

end GNC.MotorBurn
