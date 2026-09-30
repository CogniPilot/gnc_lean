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
  rw [show ω ⨯₃ (-l) - c1V a ω l d = c2P a ω l d by simp [c2P]]
  rw [show ω ⨯₃ c1V a ω l d + a ⨯₃ c1R ω d = c2V a ω l d from rfl,
    show ω ⨯₃ c1R ω d = c2R ω d from rfl]
  rw [← extended_smul, ← extended_smul, sub_eq_add_neg, ← neg_one_smul ℝ
    (extended _ (1/720 * 0)), ← extended_smul, ← extended_add]
  congr 1
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [resP, resV, resR, sub_eq_add_neg] <;> ring
  · ring

end Coordinates

section Bounds

/-- Rotation bound `ρ_R = W D²/240 + W³ D/720`. -/
def rhoR (W D : ℝ) : ℝ := W * D^2 / 240 + W^3 * D / 720
/-- Velocity bound `ρ_V = (2 W D L + D² A)/240 + (W³ L + 3 W² D A)/720`. -/
def rhoV (W A D L : ℝ) : ℝ :=
  (2 * W * D * L + D^2 * A) / 240 + (W^3 * L + 3 * W^2 * D * A) / 720
/-- Position bound `ρ_P = (D L + W² L + W D A)/240`. -/
def rhoP (W A D L : ℝ) : ℝ := (D * L + W^2 * L + W * D * A) / 240

theorem cross_le_of_le {x y : Vec3} {X Y : ℝ} (hx : enorm x ≤ X) (hy : enorm y ≤ Y) :
    enorm (x ⨯₃ y) ≤ X * Y :=
  (enorm_cross_le x y).trans
    (mul_le_mul hx hy (enorm_nonneg y) ((enorm_nonneg x).trans hx))

theorem enorm_sub_le' (u v : Vec3) : enorm (u - v) ≤ enorm u + enorm v := by
  rw [sub_eq_add_neg]
  exact (enorm_add_le u (-v)).trans (by rw [enorm_neg])

theorem residual_combo_le (u v : Vec3) :
    enorm (-(1/240:ℝ) • u - (1/720:ℝ) • v) ≤ enorm u / 240 + enorm v / 720 := by
  refine (enorm_sub_le' _ _).trans (le_of_eq ?_)
  rw [enorm_smul, enorm_smul]
  norm_num
  ring

/-- Coordinate bounds of the structured residual under norm bounds
`|ω| ≤ W`, `|a| ≤ A`, `|d| ≤ D`, `|l| ≤ L`. -/
theorem structured_coord_bounds_of_le (a ω l d : Vec3) (W A D L : ℝ)
    (hω : enorm ω ≤ W) (ha : enorm a ≤ A) (hd : enorm d ≤ D) (hl : enorm l ≤ L) :
    enorm (resR ω d) ≤ rhoR W D ∧ enorm (resV a ω l d) ≤ rhoV W A D L ∧
      enorm (resP a ω l d) ≤ rhoP W A D L := by
  have e1V : enorm (c1V a ω l d) ≤ W * L + A * D :=
    (enorm_add_le _ _).trans (add_le_add (cross_le_of_le hω hl) (cross_le_of_le ha hd))
  have e1R : enorm (c1R ω d) ≤ W * D := cross_le_of_le hω hd
  have e2P : enorm (c2P a ω l d) ≤ W * L + (W * L + A * D) := by
    unfold c2P
    refine (enorm_sub_le' _ _).trans (add_le_add ?_ e1V)
    rw [enorm_neg]; exact cross_le_of_le hω hl
  have e2V : enorm (c2V a ω l d) ≤ W * (W * L + A * D) + A * (W * D) :=
    (enorm_add_le _ _).trans (add_le_add (cross_le_of_le hω e1V) (cross_le_of_le ha e1R))
  have e2R : enorm (c2R ω d) ≤ W * (W * D) := cross_le_of_le hω e1R
  refine ⟨?_, ?_, ?_⟩
  · refine (residual_combo_le _ _).trans ?_
    have h1 := cross_le_of_le hd e1R
    have h2 := cross_le_of_le hω e2R
    unfold rhoR
    linarith
  · refine (residual_combo_le _ _).trans ?_
    have h1 : enorm (d ⨯₃ c1V a ω l d + l ⨯₃ c1R ω d) ≤ D * (W * L + A * D) + L * (W * D) :=
      (enorm_add_le _ _).trans (add_le_add (cross_le_of_le hd e1V) (cross_le_of_le hl e1R))
    have h2 : enorm (ω ⨯₃ c2V a ω l d + a ⨯₃ c2R ω d) ≤
        W * (W * (W * L + A * D) + A * (W * D)) + A * (W * (W * D)) :=
      (enorm_add_le _ _).trans (add_le_add (cross_le_of_le hω e2V) (cross_le_of_le ha e2R))
    unfold rhoV
    linarith
  · refine (residual_combo_le _ _).trans ?_
    have h1 : enorm (d ⨯₃ (-l)) ≤ D * L := cross_le_of_le hd (by rw [enorm_neg]; exact hl)
    have h2 : enorm (ω ⨯₃ c2P a ω l d - c2V a ω l d) ≤
        W * (W * L + (W * L + A * D)) + (W * (W * L + A * D) + A * (W * D)) :=
      (enorm_sub_le' _ _).trans (add_le_add (cross_le_of_le hω e2P) e2V)
    unfold rhoP
    linarith

/-- Equation (rho) of the FOH paper, with `W = |ω|`, `A = |a|`, `D = |d|`,
`L = |l|`. -/
theorem structured_coord_bounds (a ω l d : Vec3) :
    enorm (resR ω d) ≤ rhoR (enorm ω) (enorm d) ∧
      enorm (resV a ω l d) ≤ rhoV (enorm ω) (enorm a) (enorm d) (enorm l) ∧
      enorm (resP a ω l d) ≤ rhoP (enorm ω) (enorm a) (enorm d) (enorm l) :=
  structured_coord_bounds_of_le a ω l d _ _ _ _ le_rfl le_rfl le_rfl le_rfl

end Bounds

section Spectral

open scoped Matrix.Norms.L2Operator

/-- `residual5 N₀ N₁ = ξ(resP, resV, resR; 0)` with the spectral-norm algebra
structure on `Mat5`. -/
theorem structured_coords (a ω l d : Vec3) :
    residual5 (extended ![0, a, ω] 1) (extended ![0, l, d] 0) =
      extended ![resP a ω l d, resV a ω l d, resR ω d] 0 :=
  structured_coords_comm a ω l d

/-- The action of `ξ(x_P, x_V, x_R; 0)` on `(y, s₁, s₂)` is
`(x_R × y + s₁ x_V + s₂ x_P, 0, 0)`; its squared Euclidean norm is the squared
length of the first block. -/
theorem extended_mulVec_sq (xP xV xR : Vec3) (v : Fin 5 → ℝ) :
    ∑ i, (extended ![xP, xV, xR] 0 *ᵥ v) i ^ 2 =
      lengthSq (xR ⨯₃ ![v 0, v 1, v 2] + v 3 • xV + v 4 • xP) := by
  simp [extended, hat, kinematicC, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
    lengthSq, cross_apply, Matrix.vecHead, Matrix.vecTail, Pi.smul_apply, smul_eq_mul]
  ring

/-- Cauchy-Schwarz for three scalar pairs. -/
theorem cs_three (p q r α β γ : ℝ) :
    (p * α + q * β + r * γ)^2 ≤ (p^2 + q^2 + r^2) * (α^2 + β^2 + γ^2) := by
  nlinarith [sq_nonneg (p * β - q * α), sq_nonneg (p * γ - r * α),
    sq_nonneg (q * γ - r * β)]

/-- Vector form of the norm bound: for `M = ξ(x_P, x_V, x_R; 0)` and every
`v ∈ ℝ⁵`, `|M v|² ≤ (|x_P|² + |x_V|² + |x_R|²) |v|²` in the Euclidean norm. -/
theorem extended_mulVec_sq_le (xP xV xR : Vec3) (v : Fin 5 → ℝ) :
    ∑ i, (extended ![xP, xV, xR] 0 *ᵥ v) i ^ 2 ≤
      (enorm xP^2 + enorm xV^2 + enorm xR^2) * ∑ i, v i ^ 2 := by
  rw [extended_mulVec_sq, ← enorm_sq]
  set y : Vec3 := ![v 0, v 1, v 2]
  have hu : enorm (xR ⨯₃ y + v 3 • xV + v 4 • xP) ≤
      enorm xR * enorm y + enorm xV * |v 3| + enorm xP * |v 4| := by
    refine (enorm_add_le _ _).trans ?_
    refine (add_le_add (enorm_add_le _ _) le_rfl).trans ?_
    rw [enorm_smul, enorm_smul]
    have := enorm_cross_le xR y
    linarith
  have hy : enorm y ^ 2 = v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by
    rw [enorm_sq]; simp [y, lengthSq]
  have hcs := cs_three (enorm xR) (enorm xV) (enorm xP) (enorm y) |v 3| |v 4|
  have hsq := pow_le_pow_left₀ (enorm_nonneg _) hu 2
  rw [hy, sq_abs, sq_abs] at hcs
  rw [Fin.sum_univ_five]
  nlinarith [hcs, hsq]

/-- Spectral-norm bound for elements with zero time component:
`‖ξ(x_P, x_V, x_R; 0)‖₂ ≤ √(|x_P|² + |x_V|² + |x_R|²)`. -/
theorem structured_norm_bound (xP xV xR : Vec3) :
    ‖(extended ![xP, xV, xR] 0 : Mat5)‖ ≤
      Real.sqrt (enorm xP^2 + enorm xV^2 + enorm xR^2) := by
  rw [Matrix.cstar_norm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun v => ?_
  have h := extended_mulVec_sq_le xP xV xR (WithLp.ofLp v)
  have hl : ‖Matrix.toEuclideanCLM (n := Fin 5) (𝕜 := ℝ) (extended ![xP, xV, xR] 0) v‖ ^ 2 =
      ∑ i, (extended ![xP, xV, xR] 0 *ᵥ WithLp.ofLp v) i ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp
  have hr : ‖v‖ ^ 2 = ∑ i, (WithLp.ofLp v) i ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]; simp
  have hS : 0 ≤ enorm xP^2 + enorm xV^2 + enorm xR^2 := by positivity
  rw [← Real.sqrt_sq (norm_nonneg v), ← Real.sqrt_mul hS]
  refine le_trans (le_abs_self _) (Real.abs_le_sqrt ?_)
  rw [hl, hr]
  exact h

/-- Equation (rho-norm) of the FOH paper in the spectral norm:
`‖T⁵ Ξ₅‖₂ ≤ T⁵ √(ρ_R² + ρ_V² + ρ_P²)` for `T ≥ 0`. -/
theorem structured_residual_spectral_le (a ω l d : Vec3) (T : ℝ) (hT : 0 ≤ T) :
    ‖T^5 • residual5 (extended ![0, a, ω] 1) (extended ![0, l, d] 0)‖ ≤
      T^5 * Real.sqrt (rhoR (enorm ω) (enorm d) ^ 2 +
        rhoV (enorm ω) (enorm a) (enorm d) (enorm l) ^ 2 +
        rhoP (enorm ω) (enorm a) (enorm d) (enorm l) ^ 2) := by
  obtain ⟨hR, hV, hP⟩ := structured_coord_bounds a ω l d
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hT 5), structured_coords]
  refine mul_le_mul_of_nonneg_left ((structured_norm_bound _ _ _).trans ?_) (pow_nonneg hT 5)
  apply Real.sqrt_le_sqrt
  have h1 := pow_le_pow_left₀ (enorm_nonneg _) hR 2
  have h2 := pow_le_pow_left₀ (enorm_nonneg _) hV 2
  have h3 := pow_le_pow_left₀ (enorm_nonneg _) hP 2
  linarith

end Spectral

end GNC.Magnus
