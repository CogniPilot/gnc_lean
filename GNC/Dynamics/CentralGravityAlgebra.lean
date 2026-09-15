import GNC.Analysis.BiquadraticExponential
import GNC.Dynamics.RotatingThrustEnergy
import Mathlib.Algebra.Lie.Sl2

/-! The small matrix algebra behind full central gravity along a trajectory.

For canonical position/momentum the gravity coefficient is the *actual*
mu / norm(q)^3. No gravity gradient is substituted. The homogeneous blocks
close on three scalar generators and commute with a common spatial rotation.
Their matrix exponential reduces to two scalar modes. These identities do
not determine the unknown radius history or prove Magnus convergence.
-/
noncomputable section
set_option autoImplicit false
namespace GNC.CentralGravityAlgebra
open Matrix
open scoped Matrix.Norms.Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

def block (a b c : ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ :=
  fromBlocks (a • (1 : Matrix n n ℝ)) (b • 1) (c • 1) ((-a) • 1)

theorem block_linear_combination (a b c : ℝ) :
    block (n := n) a b c =
      a • block 1 0 0+b • block 0 1 0+c • block 0 0 1 := by
  simp [block, fromBlocks_smul, fromBlocks_add]

theorem block_square (a b c : ℝ) :
    (block (n := n) a b c)^2 = (a^2+b*c) • (1 : Matrix (n ⊕ n) (n ⊕ n) ℝ) := by
  simp only [block, pow_two, fromBlocks_multiply, smul_mul_smul, one_mul]
  rw [← fromBlocks_one, fromBlocks_smul]
  congr 1 <;> module

/-- All nested commutators remain in the same three-coefficient family. -/
theorem block_commutator (a b c d e f : ℝ) :
    block (n := n) a b c*block d e f-block d e f*block a b c =
      block (b*f-e*c) (2*(a*e-d*b)) (2*(c*d-f*a)) := by
  simp only [block, fromBlocks_multiply, smul_mul_smul, one_mul]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [fromBlocks, Matrix.sub_apply, smul_eq_mul] <;> ring

theorem central_commutator (k l : ℝ) :
    block (n := n) 0 1 (-k)*block 0 1 (-l)-block 0 1 (-l)*block 0 1 (-k) =
      block (k-l) 0 0 := by
  rw [block_commutator]
  congr 1 <;> ring

/-- Cayley--Hamilton style reduction sums the exponential; higher powers
need not vanish. This applies to any specified Magnus coefficients. -/
theorem block_exp (a b c t : ℝ) :
    NormedSpace.exp (t • block (n := n) a b c) =
      QuadraticModes.C (a^2+b*c) t • (1 : Matrix (n ⊕ n) (n ⊕ n) ℝ) +
      QuadraticModes.S (a^2+b*c) t • block a b c :=
  QuadraticModes.exp_quadratic _ _ _ (block_square a b c)

/-- Spatial rotation acts identically on position and canonical momentum. -/
theorem rotation_commutes (W : Matrix n n ℝ) (a b c : ℝ) :
    Commute (fromBlocks (-W) 0 0 (-W)) (block a b c) := by
  show _ * _ = _ * _
  simp [block, fromBlocks_multiply]

/-- The standard non-solvable three-generator algebra is identified using
mathlib's existing `IsSl2Triple` interface. Separate nilpotence is not a
termination argument for its commutators. -/
theorem sl2_triple [Nonempty n] :
    IsSl2Triple (block (n := n) 1 0 0) (block 0 1 0) (block 0 0 1) where
  h_ne_zero := by
    intro h
    let i : n := Classical.choice inferInstance
    have hi := congrArg (fun M => M (Sum.inl i) (Sum.inl i)) h
    simp [block] at hi
  lie_e_f := by simp [Ring.lie_def, block_commutator]
  lie_h_e_nsmul := by
    rw [Ring.lie_def, block_commutator]
    norm_num [block, two_smul, fromBlocks_add]
  lie_h_f_nsmul := by
    rw [Ring.lie_def, block_commutator]
    norm_num [block, two_smul, fromBlocks_add]
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp

/-- A repeated adjoint has a finite recurrence, even when it never vanishes. -/
theorem adjoint_cube {A : Type*} [Ring A] [Algebra ℝ A]
    (X Y : A) (q : ℝ) (hX : X^2 = q • (1 : A)) :
    X*(X*(X*Y-Y*X)-(X*Y-Y*X)*X) -
      (X*(X*Y-Y*X)-(X*Y-Y*X)*X)*X = (4*q) • (X*Y-Y*X) := by
  have hXX : X*X = q • (1 : A) := by simpa only [pow_two] using hX
  calc
    _ = (X*X)*(X*Y)-3 • ((X*X)*(Y*X))+3 • ((X*Y)*(X*X))-(Y*X)*(X*X) := by
      noncomm_ring
    _ = _ := by simp only [hXX, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]; module

section FullField
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Exact canonical equation under the change p = velocity + W position.
The coefficient remains state dependent. This is not a group-affine claim. -/
theorem canonical_derivative (W : E →L[ℝ] E) {q v : ℝ → E}
    {mu t : ℝ} {thrust : E}
    (hq : HasDerivAt q (v t) t)
    (hv : HasDerivAt v (RotatingThrust.field mu W thrust (q t) (v t)) t) :
    HasDerivAt (fun s => v s+W (q s))
      ((-(mu/‖q t‖^3)) • q t-W (v t+W (q t))+thrust) t := by
  convert hv.add (W.hasFDerivAt.comp_hasDerivAt t hq) using 1
  simp only [RotatingThrust.field, Gravity.field, neg_div, neg_smul, map_add]
  module

theorem canonical_position (W : E →L[ℝ] E) (q v : E) :
    v = (v+W q)-W q := by abel

/-- Differentiating the state-dependent gravity coefficient contributes a
term absent from the frozen-coefficient matrix bracket. Thus the matrix
closure above must not be mistaken for closure of nonlinear vector fields
or for the error STM's gravity gradient. -/
theorem frozen_gradient_defect (mu : ℝ) (q p : E) :
    Gravity.gradient mu q p - (-(mu/‖q‖^3)) • p =
      (3*mu*inner (𝕜 := ℝ) q p/‖q‖^5) • q := by
  simp only [Gravity.gradient, neg_smul]
  module

theorem radial_gradient_defect (mu : ℝ) (q : E) (hq : q ≠ 0) :
    Gravity.gradient mu q q - (-(mu/‖q‖^3)) • q = (3*mu/‖q‖^3) • q := by
  rw [frozen_gradient_defect, real_inner_self_eq_norm_sq]
  congr 1
  have hn := norm_ne_zero_iff.mpr hq
  field_simp


end FullField
end GNC.CentralGravityAlgebra
