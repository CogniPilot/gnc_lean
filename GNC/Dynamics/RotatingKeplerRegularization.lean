import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-! An exact planar Levi-Civita reduction of the rotating Kepler/constant-force
Hamiltonian. No gravity expansion is used. The regularized Hamiltonian is
polynomial, but its rotating term obstructs the usual additive Stark
separation. That obstruction is not a general nonintegrability theorem.
-/
noncomputable section
set_option autoImplicit false
namespace GNC.RotatingKeplerRegularization

def radius (u v : ℝ) : ℝ := u^2+v^2
def positionX (u v : ℝ) : ℝ := u^2-v^2
def positionY (u v : ℝ) : ℝ := 2*u*v
def momentumX (u v pu pv : ℝ) : ℝ := (u*pu-v*pv)/(2*radius u v)
def momentumY (u v pu pv : ℝ) : ℝ := (v*pu+u*pv)/(2*radius u v)

theorem physical_radius (u v : ℝ) :
    Real.sqrt (positionX u v^2+positionY u v^2) = radius u v := by
  have h : positionX u v^2+positionY u v^2 = radius u v^2 := by
    unfold positionX positionY radius; ring
  rw [h, Real.sqrt_sq (by unfold radius; positivity)]

/-- Pullback of P dot dq equals p dot du away from collision. -/
theorem canonical_one_form (u v pu pv du dv : ℝ) (hr : radius u v ≠ 0) :
    momentumX u v pu pv*(2*u*du-2*v*dv) +
      momentumY u v pu pv*(2*v*du+2*u*dv) = pu*du+pv*dv := by
  unfold momentumX momentumY
  field_simp
  unfold radius
  ring

theorem angular_momentum (u v pu pv : ℝ) (hr : radius u v ≠ 0) :
    positionX u v*momentumY u v pu pv-positionY u v*momentumX u v pu pv =
      (u*pv-v*pu)/2 := by
  unfold momentumX momentumY
  field_simp
  unfold radius positionX positionY
  ring

def hamiltonian (μ w ax ay u v pu pv : ℝ) : ℝ :=
  (momentumX u v pu pv^2+momentumY u v pu pv^2)/2 - μ/radius u v -
    w*(positionX u v*momentumY u v pu pv-positionY u v*momentumX u v pu pv) -
    ax*positionX u v-ay*positionY u v

def regularized (μ energy w ax ay u v pu pv : ℝ) : ℝ :=
  (pu^2+pv^2)/8-μ-energy*(u^2+v^2) -
    w/2*(u^2+v^2)*(u*pv-v*pu)-ax*(u^4-v^4)-2*ay*u*v*(u^2+v^2)

/-- Exact energy-shell rescaling K = r (H-E), corresponding to dt/dτ = r.
This identity alone does not construct the regularized Hamiltonian flow or
invert its physical time map. -/
theorem regularized_identity (μ energy w ax ay u v pu pv : ℝ)
    (hr : radius u v ≠ 0) :
    radius u v*(hamiltonian μ w ax ay u v pu pv-energy) =
      regularized μ energy w ax ay u v pu pv := by
  unfold hamiltonian momentumX momentumY regularized
  field_simp
  unfold radius positionX positionY
  ring

/-- With a fixed inertial force aligned with the first coordinate, the
regularized Hamiltonian separates into two quartic one-dimensional terms. -/
theorem stark_separation (μ energy ax u v pu pv : ℝ) :
    regularized μ energy 0 ax 0 u v pu pv =
      (pu^2/8-energy*u^2-ax*u^4) + (pv^2/8-energy*v^2+ax*v^4)-μ := by
  unfold regularized
  ring

/-- A mixed-coordinate finite difference, at four noncollision positions,
detects the coupling caused by a rotating reference frame. -/
theorem separation_defect (μ energy w ax ay : ℝ) :
    regularized μ energy w ax ay 2 1 0 1 -
      regularized μ energy w ax ay 2 1 0 0 -
      regularized μ energy w ax ay 1 1 0 1 +
      regularized μ energy w ax ay 1 1 0 0 = -4*w := by
  unfold regularized
  ring

/-- Only the usual additive separation in these coordinates is ruled out.
Other coordinate systems, additional integrals, and special functions have
not been ruled out by this theorem. -/
theorem no_additive_stark_separation (μ energy w ax ay : ℝ) (hw : w ≠ 0) :
    ¬ ∃ F G : ℝ → ℝ → ℝ, ∀ u v pu pv,
      regularized μ energy w ax ay u v pu pv = F u pu+G v pv := by
  rintro ⟨F, G, h⟩
  have hd := separation_defect μ energy w ax ay
  rw [h, h, h, h] at hd
  apply hw
  linarith

end GNC.RotatingKeplerRegularization
