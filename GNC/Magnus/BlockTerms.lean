import GNC.Magnus.NilpotentInteraction
import GNC.Magnus.GaussLegendre
import GNC.Magnus.FixedAxis
import GNC.Dynamics.OrbitalNilpotence

/-! Explicit Magnus integrands for the orbital block decomposition.
The convention is left evolution, Phi' = A Phi. Finite term identities
below do not assume convergence of an infinite Magnus expansion. Exact
termination of the transported coupling follows separately from the actual
flow and exponential theorems in NilpotentInteraction.
-/
noncomputable section
open Matrix MeasureTheory
open scoped Matrix.Norms.Operator
namespace GNC.BlockMagnus
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

def triangular (T : Matrix m m ℝ) (K : Matrix m n ℝ) (H : Matrix n n ℝ) :=
  fromBlocks T K 0 H

/-- Before diagonal transport, attitude/thrust terms still couple to the
translation and attitude generators in the SECOND Magnus integrand. -/
theorem triangular_commutator (T₁ T₂ : Matrix m m ℝ) (K₁ K₂ : Matrix m n ℝ)
    (H₁ H₂ : Matrix n n ℝ) :
    Magnus.comm (triangular T₁ K₁ H₁) (triangular T₂ K₂ H₂) =
      fromBlocks (Magnus.comm T₁ T₂)
        (T₁*K₂+K₁*H₂-T₂*K₁-K₂*H₁) 0 (Magnus.comm H₁ H₂) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [triangular, Magnus.comm, fromBlocks_multiply] <;> ring

section Terms
variable {k : Type*} [Fintype k] [DecidableEq k]

def first (A : ℝ → Matrix k k ℝ) (h : ℝ) := ∫ t in (0 : ℝ)..h, A t

def second (A : ℝ → Matrix k k ℝ) (h : ℝ) :=
  (1/2 : ℝ) • ∫ t₁ in (0 : ℝ)..h, ∫ t₂ in (0 : ℝ)..t₁, Magnus.comm (A t₁) (A t₂)

def third (A : ℝ → Matrix k k ℝ) (h : ℝ) :=
  (1/6 : ℝ) • ∫ t₁ in (0 : ℝ)..h, ∫ t₂ in (0 : ℝ)..t₁, ∫ t₃ in (0 : ℝ)..t₂,
    (Magnus.comm (A t₁) (Magnus.comm (A t₂) (A t₃)) +
      Magnus.comm (A t₃) (Magnus.comm (A t₂) (A t₁)))

theorem second_zero_of_commuting (A : ℝ → Matrix k k ℝ)
    (hcomm : ∀ s t, Magnus.comm (A s) (A t) = 0) (h : ℝ) : second A h = 0 := by
  simp [second, hcomm]

theorem third_zero_of_commuting (A : ℝ → Matrix k k ℝ)
    (hcomm : ∀ s t, Magnus.comm (A s) (A t) = 0) (h : ℝ) : third A h = 0 := by
  simp only [third, hcomm]
  simp [Magnus.comm]

end Terms

theorem coupling_first (L : ℝ → Matrix m n ℝ) (hL : Continuous L) (h : ℝ) :
    first (fun t => NilpotentInteraction.lift (L t)) h =
      NilpotentInteraction.lift (NilpotentInteraction.primitive L h) :=
  NilpotentInteraction.first_magnus L hL h

theorem coupling_second (L : ℝ → Matrix m n ℝ) (h : ℝ) :
    second (fun t => NilpotentInteraction.lift (L t)) h = 0 :=
  second_zero_of_commuting _ (fun s t => NilpotentInteraction.cross_commutator (L s) (L t)) h

theorem coupling_third (L : ℝ → Matrix m n ℝ) (h : ℝ) :
    third (fun t => NilpotentInteraction.lift (L t)) h = 0 :=
  third_zero_of_commuting _ (fun s t => NilpotentInteraction.cross_commutator (L s) (L t)) h

/-- Removing all higher terms is justified by the actual exponential/ODE
proof, independently of a formal-series convergence argument. -/
theorem coupling_exponential (L : ℝ → Matrix m n ℝ) (hL : Continuous L) (h : ℝ) :
    NormedSpace.exp (first (fun t => NilpotentInteraction.lift (L t)) h) =
      fromBlocks 1 (NilpotentInteraction.primitive L h) 0 1 := by
  rw [coupling_first L hL h, NilpotentInteraction.exponential]

theorem fixed_axis_second (Z : Matrix n n ℝ) (speed : ℝ → ℝ) (h : ℝ) :
    second (fun t => speed t • Z) h = 0 :=
  second_zero_of_commuting _ (fun s t => FixedAxisMagnus.cross_commutator Z (speed s) (speed t)) h

theorem fixed_axis_third (Z : Matrix n n ℝ) (speed : ℝ → ℝ) (h : ℝ) :
    third (fun t => speed t • Z) h = 0 :=
  third_zero_of_commuting _ (fun s t => FixedAxisMagnus.cross_commutator Z (speed s) (speed t)) h

/-- Even in inertial coordinates, a changing gravity gradient leaves a
nonzero second Magnus integrand. -/
theorem gravity_commutator (G₁ G₂ : Matrix n n ℝ) :
    Magnus.comm (OrbitalNilpotence.translation G₁) (OrbitalNilpotence.translation G₂) =
      fromBlocks (G₂-G₁) 0 0 (G₁-G₂) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Magnus.comm, OrbitalNilpotence.translation, fromBlocks_multiply]

/-- For G(t)=G0+t G1 the cubic left-Magnus jet is -[T0,T1]/12.
The sign is tied to Phi'=A Phi; swapping the evolution convention changes it. -/
theorem gravity_linear_cubic_jet (G₀ G₁ : Matrix n n ℝ) :
    (Magnus.leftExponent4 (OrbitalNilpotence.translation G₀)
      (OrbitalNilpotence.gravity G₁) 0 0).coeff 3 =
      (-1/12 : ℝ) • fromBlocks G₁ 0 0 (-G₁) := by
  have hc : Magnus.comm (OrbitalNilpotence.translation G₀) (OrbitalNilpotence.gravity G₁) =
      fromBlocks G₁ 0 0 (-G₁) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [Magnus.comm, OrbitalNilpotence.translation, OrbitalNilpotence.gravity,
        fromBlocks_multiply]
  norm_num [Magnus.leftExponent4, Polynomial.coeff_monomial, hc, neg_div, neg_smul]

end GNC.BlockMagnus
