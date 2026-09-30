import GNC.Magnus.ResidualBound
import GNC.Magnus.FOHIncrement
import Mathlib.Analysis.CStarAlgebra.Matrix

/-! Structured bound on the degree-five Magnus residual of the first-order hold.

For the generators `N₀ = ξ(0, a, ω; 1)` and `N₁ = ξ(0, l, d; 0)` (with `l`, `d`
the input slopes `Δa/T`, `Δω/T`), the residual
`Ξ₅ = -(1/240)[N₁,[N₀,N₁]] - (1/720)[N₀,[N₀,[N₀,N₁]]]` has zero time component.
Its position, velocity and rotation coordinates are explicit cross-product
polynomials, bounded in the Euclidean norm by

  `ρ_R = W D²/240 + W³ D/720`,
  `ρ_V = (2 W D L + D² A)/240 + (W³ L + 3 W² D A)/720`,
  `ρ_P = (D L + W² L + W D A)/240`,

with `W = |ω|`, `A = |a|`, `D = |d|`, `L = |l|`. An element `ξ(x_P, x_V, x_R; 0)`
maps `(y, s₁, s₂) ∈ ℝ⁵` to `(x_R × y + s₁ x_V + s₂ x_P, 0, 0)`, so its spectral
norm is at most `√(|x_P|² + |x_V|² + |x_R|²)`, which gives
`‖T⁵ Ξ₅‖₂ ≤ T⁵ √(ρ_R² + ρ_V² + ρ_P²)`. -/
noncomputable section
namespace GNC.Magnus
open Matrix
open scoped Matrix

section Brackets

/-- Bracket with the constant generator:
`[N₀, ξ(x_P, x_V, x_R; 0)] = ξ(ω × x_P - x_V, ω × x_V + a × x_R, ω × x_R; 0)`.
Since `a × x_R = -(x_R × a)`, this is the coordinate map of the bracket
identity with the time corner contributing `-x_V`. -/
theorem comm_N0 (a ω xP xV xR : Vec3) :
    comm (extended ![0, a, ω] 1) (extended ![xP, xV, xR] 0) =
      extended ![ω ⨯₃ xP - xV, ω ⨯₃ xV + a ⨯₃ xR, ω ⨯₃ xR] 0 := by
  unfold comm
  rw [extended_commutator]
  congr 1
  ext i j; fin_cases i <;> fin_cases j <;> simp [extendedBracket, ad] <;> ring

/-- Bracket with the slope generator:
`[N₁, ξ(x_P, x_V, x_R; 0)] = ξ(d × x_P, d × x_V + l × x_R, d × x_R; 0)`. -/
theorem comm_N1 (l d xP xV xR : Vec3) :
    comm (extended ![0, l, d] 0) (extended ![xP, xV, xR] 0) =
      extended ![d ⨯₃ xP, d ⨯₃ xV + l ⨯₃ xR, d ⨯₃ xR] 0 := by
  unfold comm
  rw [extended_commutator]
  congr 1
  ext i j; fin_cases i <;> fin_cases j <;> simp [extendedBracket, ad]

end Brackets

section Coordinates

/-- Velocity coordinate of `[N₀, N₁]`. -/
def c1V (a ω l d : Vec3) : Vec3 := ω ⨯₃ l + a ⨯₃ d
/-- Rotation coordinate of `[N₀, N₁]`. -/
def c1R (ω d : Vec3) : Vec3 := ω ⨯₃ d
/-- Position coordinate of `[N₀,[N₀, N₁]]`. -/
def c2P (a ω l d : Vec3) : Vec3 := -(ω ⨯₃ l) - c1V a ω l d
/-- Velocity coordinate of `[N₀,[N₀, N₁]]`. -/
def c2V (a ω l d : Vec3) : Vec3 := ω ⨯₃ c1V a ω l d + a ⨯₃ c1R ω d
/-- Rotation coordinate of `[N₀,[N₀, N₁]]`. -/
def c2R (ω d : Vec3) : Vec3 := ω ⨯₃ c1R ω d

/-- Position coordinate of the residual `Ξ₅`. -/
def resP (a ω l d : Vec3) : Vec3 :=
  -(1/240:ℝ) • (d ⨯₃ (-l)) - (1/720:ℝ) • (ω ⨯₃ c2P a ω l d - c2V a ω l d)
/-- Velocity coordinate of the residual `Ξ₅`. -/
def resV (a ω l d : Vec3) : Vec3 :=
  -(1/240:ℝ) • (d ⨯₃ c1V a ω l d + l ⨯₃ c1R ω d) -
    (1/720:ℝ) • (ω ⨯₃ c2V a ω l d + a ⨯₃ c2R ω d)
/-- Rotation coordinate of the residual `Ξ₅`. -/
def resR (ω d : Vec3) : Vec3 :=
  -(1/240:ℝ) • (d ⨯₃ c1R ω d) - (1/720:ℝ) • (ω ⨯₃ c2R ω d)

/-- The residual as a plain matrix expression. -/
theorem residual5_mat (N₀ N₁ : Mat5) :
    -(1/240:ℝ) • (N₁ * (N₀ * N₁ - N₁ * N₀) - (N₀ * N₁ - N₁ * N₀) * N₁) -
      (1/720:ℝ) • (N₀ * (N₀ * (N₀ * N₁ - N₁ * N₀) - (N₀ * N₁ - N₁ * N₀) * N₀) -
        (N₀ * (N₀ * N₁ - N₁ * N₀) - (N₀ * N₁ - N₁ * N₀) * N₀) * N₀) =
    -(1/240:ℝ) • comm N₁ (comm N₀ N₁) - (1/720:ℝ) • comm N₀ (comm N₀ (comm N₀ N₁)) :=
  rfl

/-- The structured residual: `-(1/240)[N₁,[N₀,N₁]] - (1/720)[N₀,[N₀,[N₀,N₁]]]`
equals `ξ(resP, resV, resR; 0)`, so its time component is zero. -/
theorem structured_coords_comm (a ω l d : Vec3) :
    -(1/240:ℝ) • comm (extended ![0, l, d] 0)
        (comm (extended ![0, a, ω] 1) (extended ![0, l, d] 0)) -
      (1/720:ℝ) • comm (extended ![0, a, ω] 1) (comm (extended ![0, a, ω] 1)
        (comm (extended ![0, a, ω] 1) (extended ![0, l, d] 0))) =
      extended ![resP a ω l d, resV a ω l d, resR ω d] 0 := by
  have h1 : comm (extended ![0, a, ω] 1) (extended ![0, l, d] 0) =
      extended ![-l, c1V a ω l d, c1R ω d] 0 := by
    rw [comm_N0]; congr 1; ext i j; fin_cases i <;> fin_cases j <;> simp [c1V, c1R]
  rw [h1, comm_N1, comm_N0, comm_N0]
  rw [show ω ⨯₃ (-l) - c1V a ω l d = c2P a ω l d by simp [c2P, cross_neg_right]]
  rw [show ω ⨯₃ c1V a ω l d + a ⨯₃ c1R ω d = c2V a ω l d from rfl,
    show ω ⨯₃ c1R ω d = c2R ω d from rfl]
  rw [← extended_smul, ← extended_smul, sub_eq_add_neg, ← neg_one_smul ℝ
    (extended _ (1/720 * 0)), ← extended_smul, ← extended_add]
  congr 1
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [resP, resV, resR, sub_eq_add_neg]
  · ring

end Coordinates

end GNC.Magnus
