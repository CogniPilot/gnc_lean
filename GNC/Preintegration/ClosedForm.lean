import GNC.Analysis.MixedFlow
import GNC.Lie.Jacobian
import GNC.Algebra.NilpotentSummation
import Mathlib.Data.Matrix.Block

/-! Closed-form preintegration, Theorem 1 of Lin et al. (2025).
We use the dimensionally consistent P in equation (28), and its coefficient
list, rather than the inconsistent duplicate formulas in the theorem display.
The proof identifies the formula with mathlib's actual matrix exponential by
differentiation and uniqueness; it does not postulate the exponential series.
-/
noncomputable section
open Matrix Real
open scoped Matrix Matrix.Norms.Operator
namespace GNC.Preintegration

def f₁ (w t : ℝ) : ℝ := (1-cos (w*t))/w^2
def f₂ (w t : ℝ) : ℝ := (w*t-sin (w*t))/w^3
def f₃ (w t : ℝ) : ℝ := ((w*t)^2/2+cos (w*t)-1)/w^4

theorem derivative_f₂ (w t : ℝ) (hw : w ≠ 0) : HasDerivAt (f₂ w) (f₁ w t) t := by
  have hd := (hasDerivAt_id t).const_mul w
  convert (hd.sub ((hasDerivAt_sin (w*t)).comp t hd)).div_const (w^3) using 1
  dsimp [f₁]; field_simp

theorem derivative_f₃ (w t : ℝ) (hw : w ≠ 0) : HasDerivAt (f₃ w) (f₂ w t) t := by
  have hd := (hasDerivAt_id t).const_mul w
  convert ((((hd.pow 2).div_const 2).add
    ((hasDerivAt_cos (w*t)).comp t hd)).sub_const 1).div_const (w^4) using 1
  dsimp [f₂]; field_simp; ring

theorem f₁_relation (w t : ℝ) (hw : w ≠ 0) :
    f₁ w t = t^2/2 - w^2 * f₃ w t := by
  unfold f₁ f₃; field_simp; ring

section BanachAlgebra
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

def polynomial (W : A) (w t : ℝ) : A :=
  1 + t • W + (t^2/2) • W^2 + f₂ w t • W^3 + f₃ w t • W^4

omit [CompleteSpace A] in
theorem polynomial_derivative (W : A) (w t : ℝ) (hw : w ≠ 0)
    (hW : W^5 = -(w^2) • W^3) :
    HasDerivAt (polynomial W w) (W * polynomial W w t) t := by
  have hd := ((((hasDerivAt_id t).smul_const W).const_add 1).add
    (((hasDerivAt_id t).pow 2).div_const 2 |>.smul_const (W^2))).add
    ((derivative_f₂ w t hw).smul_const (W^3)) |>.add
    ((derivative_f₃ w t hw).smul_const (W^4))
  convert hd using 1
  simp only [polynomial, mul_add, mul_one, mul_smul_comm, ← pow_succ', hW,
    smul_smul, f₁_relation w t hw, Nat.reduceAdd, ← pow_two]
  norm_num
  module

/-- Exact exponential under the minimal-polynomial identity satisfied by
the paper's block matrix W. -/
theorem exp_polynomial (W : A) (w t : ℝ) (hw : w ≠ 0)
    (hW : W^5 = -(w^2) • W^3) :
    NormedSpace.exp (t • W) = polynomial W w t := by
  have he := MixedInvariant.flow_unique W 0 1 (polynomial W w)
    (fun s => by simpa using polynomial_derivative W w s hw hW)
    (by simp [polynomial, f₂, f₃])
  simpa [MixedInvariant.flow] using (congrFun he t).symm

end BanachAlgebra

section Blocks
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

theorem block_power (Ω : Matrix m m ℝ) (A : Matrix m n ℝ)
    (B : Matrix n n ℝ) (hB : B^2 = 0) (j : ℕ) :
    block Ω A B ^ (j+2) = fromBlocks (Ω^(j+2)) (Ω^(j+1)*A + Ω^j*A*B) 0 0 := by
  induction j with
  | zero =>
    simp only [pow_zero, pow_one, block, pow_two, fromBlocks_multiply,
      Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero, Matrix.one_mul]
    rw [← pow_two B, hB]
  | succ j ih =>
    rw [show j+1+2 = (j+2)+1 by omega, pow_succ, ih]
    simp only [block, fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero]
    congr 1
    rw [Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← pow_two B, hB,
      Matrix.mul_zero, add_zero]

theorem block_relation (Ω : Matrix m m ℝ) (A : Matrix m n ℝ) (B : Matrix n n ℝ)
    (w : ℝ) (hΩ : Ω^3 = -(w^2) • Ω) (hB : B^2 = 0) :
    block Ω A B ^ 5 = -(w^2) • block Ω A B ^ 3 := by
  exact block_minimal_relation Ω A B 1 w hΩ hB

/-- Translation block in equation (28), including the omitted A factor. -/
def translation (Ω : Matrix m m ℝ) (A : Matrix m n ℝ)
    (B : Matrix n n ℝ) (w t : ℝ) : Matrix m n ℝ :=
  t • A + (t^2/2) • (A*B) + f₁ w t • (Ω*A) +
    f₂ w t • (Ω^2*A + Ω*A*B) + f₃ w t • (Ω^2*A*B)

def rodrigues (Ω : Matrix m m ℝ) (w t : ℝ) : Matrix m m ℝ :=
  1 + (sin (w*t)/w) • Ω + f₁ w t • Ω^2

theorem sin_relation (w t : ℝ) (hw : w ≠ 0) : sin (w*t)/w = t - w^2*f₂ w t := by
  unfold f₂; field_simp; ring

theorem fourth_power (Ω : Matrix m m ℝ) (w : ℝ)
    (hΩ : Ω^3 = -(w^2) • Ω) : Ω^4 = -(w^2) • Ω^2 := by
  calc Ω^4 = Ω^3*Ω := by noncomm_ring
       _ = _ := by rw [hΩ, smul_mul_assoc]; congr 1; noncomm_ring

theorem fifth_power (Ω : Matrix m m ℝ) (w : ℝ)
    (hΩ : Ω^3 = -(w^2) • Ω) : Ω^5 = -(w^2) • Ω^3 := by
  calc Ω^5 = Ω^3*Ω^2 := by noncomm_ring
       _ = (-(w^2) • Ω)*Ω^2 := by rw [hΩ]
       _ = _ := by rw [smul_mul_assoc]; congr 1; noncomm_ring

theorem exp_rodrigues (Ω : Matrix m m ℝ) (w t : ℝ) (hw : w ≠ 0)
    (hΩ : Ω^3 = -(w^2) • Ω) : NormedSpace.exp (t • Ω) = rodrigues Ω w t := by
  rw [exp_polynomial Ω w t hw (fifth_power Ω w hΩ)]
  unfold polynomial rodrigues
  rw [fourth_power Ω w hΩ, hΩ, sin_relation w t hw, f₁_relation w t hw]
  module

/-- Equation (29), proved as equality to mathlib's exponential. -/
theorem exp_block (Ω : Matrix m m ℝ) (A : Matrix m n ℝ) (B : Matrix n n ℝ)
    (w t : ℝ) (hw : w ≠ 0) (hΩ : Ω^3 = -(w^2) • Ω) (hB : B^2 = 0) :
    NormedSpace.exp (t • block Ω A B) =
      fromBlocks (NormedSpace.exp (t • Ω)) (translation Ω A B w t) 0 (1+t • B) := by
  rw [exp_polynomial _ w t hw (block_relation Ω A B w hΩ hB), exp_rodrigues Ω w t hw hΩ]
  unfold polynomial
  rw [show block Ω A B ^ 2 = _ from block_power Ω A B hB 0,
    show block Ω A B ^ 3 = _ from block_power Ω A B hB 1,
    show block Ω A B ^ 4 = _ from block_power Ω A B hB 2]
  rw [show (1 : Matrix (m ⊕ n) (m ⊕ n) ℝ) = fromBlocks 1 0 0 1 from fromBlocks_one.symm]
  simp only [block, fromBlocks_smul, fromBlocks_add, smul_zero, zero_add, add_zero,
    Nat.reduceAdd, pow_zero, pow_one, Matrix.one_mul]
  congr 1
  · unfold rodrigues
    rw [fourth_power Ω w hΩ, hΩ, sin_relation w t hw, f₁_relation w t hw]
    module
  · unfold translation
    rw [hΩ, Matrix.smul_mul, f₁_relation w t hw]
    module

/-- Zero angular rate: the finite polynomial replaces all removable quotients. -/
theorem exp_block_zero (A : Matrix m n ℝ) (B : Matrix n n ℝ) (t : ℝ) (hB : B^2 = 0) :
    NormedSpace.exp (t • block 0 A B) =
      fromBlocks 1 (t • A + (t^2/2) • (A*B)) 0 (1+t • B) := by
  have he := exp_block (0 : Matrix m m ℝ) A B 1 t (by norm_num) (by simp) hB
  simpa [translation, Matrix.zero_mul] using he

omit [DecidableEq m] in
/-- The block product in equation (15), for any number of translation columns. -/
theorem flow_blocks (RM RN R₀ : Matrix m m ℝ) (PM PN P₀ : Matrix m n ℝ)
    (B : Matrix n n ℝ) (t : ℝ) (hB : B^2 = 0) :
    fromBlocks RM PM 0 (1-t • B) * fromBlocks R₀ P₀ 0 1 *
      fromBlocks RN PN 0 (1+t • B) =
    fromBlocks (RM*R₀*RN) (RM*R₀*PN + (RM*P₀+PM)*(1+t • B)) 0 1 := by
  have hc : (1-t • B)*(1+t • B) = 1 := by
    rw [sub_mul, one_mul, mul_add, mul_one, smul_mul_smul_comm, ← pow_two B, hB, smul_zero]
    abel
  simp only [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
    Matrix.mul_one, zero_add, add_zero, hc]

/-- The nonzero-angular-rate case of Theorem 1, with the corrected equation (28).
Together with flow_derivative and flow_unique this is the unique IVP solution. -/
theorem closed_form (ΩM ΩN R₀ : Matrix m m ℝ) (AM AN P₀ : Matrix m n ℝ)
    (B : Matrix n n ℝ) (wM wN t : ℝ) (hwM : wM ≠ 0) (hwN : wN ≠ 0)
    (hM : ΩM^3 = -(wM^2) • ΩM) (hN : ΩN^3 = -(wN^2) • ΩN) (hB : B^2 = 0) :
    MixedInvariant.flow (block ΩM AM (-B)) (block ΩN AN B) (fromBlocks R₀ P₀ 0 1) t =
      fromBlocks (NormedSpace.exp (t • ΩM)*R₀*NormedSpace.exp (t • ΩN))
        (NormedSpace.exp (t • ΩM)*R₀*translation ΩN AN B wN t +
         (NormedSpace.exp (t • ΩM)*P₀+translation ΩM AM (-B) wM t)*(1+t • B)) 0 1 := by
  unfold MixedInvariant.flow
  rw [exp_block ΩM AM (-B) wM t hwM hM (by simpa using hB),
    exp_block ΩN AN B wN t hwN hN hB]
  simpa only [smul_neg, ← sub_eq_add_neg] using
    flow_blocks (NormedSpace.exp (t • ΩM)) (NormedSpace.exp (t • ΩN)) R₀
      (translation ΩM AM (-B) wM t) (translation ΩN AN B wN t) P₀ B t hB

/-- Total translation formula with its removable zero-rate case filled in. -/
def translationAll (Ω : Matrix m m ℝ) (A : Matrix m n ℝ)
    (B : Matrix n n ℝ) (w t : ℝ) : Matrix m n ℝ :=
  if w = 0 then t • A + (t^2/2) • (A*B) else translation Ω A B w t

theorem exp_block_all (Ω : Matrix m m ℝ) (A : Matrix m n ℝ) (B : Matrix n n ℝ)
    (w t : ℝ) (hΩ : Ω^3 = -(w^2) • Ω) (hz : w = 0 → Ω = 0) (hB : B^2 = 0) :
    NormedSpace.exp (t • block Ω A B) =
      fromBlocks (NormedSpace.exp (t • Ω)) (translationAll Ω A B w t) 0 (1+t • B) := by
  by_cases hw : w = 0
  · rw [hz hw]
    simpa [translationAll, hw] using exp_block_zero A B t hB
  · simpa [translationAll, hw] using exp_block Ω A B w t hw hΩ hB

end Blocks

section Spatial
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Theorem 1 specialized to the actual SO(3) skew matrices, without an
assumed polynomial identity or an excluded zero-angular-rate case. -/
theorem closed_form_spatial (ωM ωN : Vec3) (R₀ : Matrix (Fin 3) (Fin 3) ℝ)
    (AM AN P₀ : Matrix (Fin 3) n ℝ) (B : Matrix n n ℝ) (t : ℝ) (hB : B^2 = 0) :
    MixedInvariant.flow (block (skew ωM) AM (-B)) (block (skew ωN) AN B)
      (fromBlocks R₀ P₀ 0 1) t =
    fromBlocks (NormedSpace.exp (t • skew ωM)*R₀*NormedSpace.exp (t • skew ωN))
      (NormedSpace.exp (t • skew ωM)*R₀*translationAll (skew ωN) AN B (enorm ωN) t +
       (NormedSpace.exp (t • skew ωM)*P₀+
        translationAll (skew ωM) AM (-B) (enorm ωM) t)*(1+t • B)) 0 1 := by
  have hz (v : Vec3) (h : enorm v = 0) : skew v = 0 := by
    rw [(enorm_eq_zero_iff v).mp h, skew_zero]
  unfold MixedInvariant.flow
  rw [exp_block_all (skew ωM) AM (-B) (enorm ωM) t (skew_cube ωM) (hz ωM)
      (by simpa using hB),
    exp_block_all (skew ωN) AN B (enorm ωN) t (skew_cube ωN) (hz ωN) hB]
  simpa only [smul_neg, ← sub_eq_add_neg] using
    flow_blocks (NormedSpace.exp (t • skew ωM)) (NormedSpace.exp (t • skew ωN)) R₀
      (translationAll (skew ωM) AM (-B) (enorm ωM) t)
      (translationAll (skew ωN) AN B (enorm ωN) t) P₀ B t hB

end Spatial
end GNC.Preintegration
