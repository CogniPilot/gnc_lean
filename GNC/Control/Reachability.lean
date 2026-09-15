import GNC.Control.LocalLogBackstepping

/-! Reachable-set enclosures for exact nonlinear dynamics.
Reachability quantifies over all admissible trajectories from the initial set.
The energy certificate does not replace the dynamics by a local linearization.
Existence and model/chart validity are distinct obligations.
-/
noncomputable section
open Set Real
namespace GNC.Reachability
variable {E : Type*}

def reachable (valid : (ℝ → E) → Prop) (initial : Set E) (a t : ℝ) : Set E :=
  {y | ∃ x : ℝ → E, valid x ∧ x a ∈ initial ∧ x t = y}

def sublevel (V : E → ℝ) (ρ : ℝ) : Set E := {x | V x ≤ ρ}

/-- Lift a trajectory estimate to a universal enclosure of the reachable set.
The initial set may contain arbitrarily many states and valid trajectories. -/
theorem sublevel_enclosure (valid : (ℝ → E) → Prop) (V : E → ℝ)
    {ρ decay budget a t : ℝ} (hdecay : 0 ≤ decay)
    (h : ∀ x, valid x → V (x t) ≤ V (x a)*decay+budget) :
    reachable valid (sublevel V ρ) a t ⊆ sublevel V (ρ*decay+budget) := by
  rintro y ⟨x,hx,hinit,rfl⟩
  have hm := mul_le_mul_of_nonneg_right hinit hdecay
  change V (x t) ≤ ρ*decay+budget
  linarith [h x hx]

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def disturbedTrajectories (f : ℝ → E → E) (δ a b : ℝ) (x : ℝ → E) : Prop :=
  ∃ d : ℝ → E, (∀ s ∈ Icc a b, ‖d s‖ ≤ δ) ∧
    (∀ s ∈ Icc a b, HasDerivAt x (f s (x s)+d s) s)

/-- A robust finite-time enclosure for a nonlinear dissipative vector field.
Both disturbances and initial states vary over sets. No Jacobian of f,
Taylor approximation, or linearized trajectory appears in the hypotheses. -/
theorem disturbed_reachable_subset (f : ℝ → E → E)
    {k δ ρ a b t : ℝ} (hk : 0 < k) (hδ : 0 ≤ δ)
    (hf : ∀ s ∈ Icc a b, ∀ y, inner ℝ y (f s y) ≤ -k*‖y‖^2)
    (ht : t ∈ Icc a b) :
    reachable (disturbedTrajectories f δ a b) (sublevel (fun y => ‖y‖^2/2) ρ) a t ⊆
      sublevel (fun y => ‖y‖^2/2)
        (ρ*exp (-k*(t-a))+(δ^2/(2*k^2))*(1-exp (-k*(t-a)))) := by
  apply sublevel_enclosure _ _ (exp_pos _).le
  intro x hx
  obtain ⟨d,hd,hx⟩ := hx
  have hder : ∀ s ∈ Icc a b, HasDerivAt (fun u => ‖x u‖^2/2)
      (inner ℝ (x s) (f s (x s)+d s)) s := by
    intro s hs
    convert (hx s hs).norm_sq.div_const 2 using 1
    ring
  have h := Lyapunov.disturbed_bound_on (c := k) (ε := δ^2/(2*k))
    hk.ne' hder (by
      intro s hs
      have hs' : s ∈ Icc a b := ⟨hs.1,hs.2.le⟩
      have hp := Lyapunov.disturbance_dissipation (x s) (f s (x s)) (d s) hk (hf s hs' (x s))
      have hsq : ‖d s‖^2 ≤ δ^2 := by nlinarith [hd s hs', norm_nonneg (d s)]
      have hdiv := div_le_div_of_nonneg_right hsq (by positivity : 0 ≤ 2*k)
      nlinarith)
  convert h t ht using 1
  congr 1
  congr 1
  field_simp

end GNC.Reachability

namespace GNC.Reachability

def attitudeEnergy (x : Vec3 × Vec3) : ℝ := (enorm x.1^2+enorm x.2^2)/2

def logRateTrajectories (kq kz a b : ℝ) (x : ℝ → Vec3 × Vec3) : Prop :=
  (∀ s ∈ Icc a b, HasDerivAt (fun u => (x u).1)
    (-kq • (x s).1+Jacobian.inverseAt (-(x s).1) (x s).2) s) ∧
  (∀ s ∈ Icc a b, HasDerivAt (fun u => (x u).2)
    (-kz • (x s).2-(x s).1) s)

/-- The exact nonlinear log-attitude/rate dynamics admit a contracting
reachable energy set. The physical torque theorem supplies these dynamics
for chart-valid rigid-body trajectories; no local linearization is used. -/
theorem logRate_reachable_subset {kq kz k ρ a b t : ℝ}
    (hkq : k ≤ kq) (hkz : k ≤ kz) (ht : t ∈ Icc a b) :
    reachable (logRateTrajectories kq kz a b) (sublevel attitudeEnergy ρ) a t ⊆
      sublevel attitudeEnergy (ρ*exp (-2*k*(t-a))) := by
  have h := sublevel_enclosure (logRateTrajectories kq kz a b) attitudeEnergy
    (ρ := ρ) (decay := exp (-2*k*(t-a))) (budget := 0) (a := a) (t := t)
    (exp_pos _).le (by
      intro x hx
      simpa only [attitudeEnergy, add_zero] using
        LogBackstepping.rotation_rate_energy_bound_on hkq hkz hx.1 hx.2 t ht)
  simpa only [add_zero] using h

/-- Projection of a joint attitude/rate energy enclosure to attitude length. -/
theorem attitude_projection {q z : Vec3} {ρ : ℝ}
    (h : (q,z) ∈ sublevel attitudeEnergy ρ) : enorm q^2 ≤ 2*ρ := by
  change (enorm q^2+enorm z^2)/2 ≤ ρ at h
  nlinarith [sq_nonneg (enorm z)]

end GNC.Reachability
