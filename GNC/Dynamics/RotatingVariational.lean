import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic

/-! The exact algebraic connection between body-frame inertial-velocity error
and the rotating-coordinate position derivative used by HCW and TH/YA.
W is the frame angular-velocity matrix; Wdot must not be omitted on an ellipse.
This identity holds for any reference gradient, independently of Kepler motion. -/
noncomputable section
open Matrix
namespace GNC.RotatingVariational
variable {n : Type*} [Fintype n] [DecidableEq n]
abbrev Block := Matrix (n ⊕ n) (n ⊕ n) ℝ

def logGenerator (G W : Matrix n n ℝ) : Block (n := n) := fromBlocks (-W) 1 G (-W)
def classicalGenerator (G W Wdot : Matrix n n ℝ) : Block (n := n) :=
  fromBlocks 0 1 (G - W*W - Wdot) (-(2:ℝ) • W)
def coordinateChange (W : Matrix n n ℝ) : Block (n := n) := fromBlocks 1 0 (-W) 1
def coordinateInverse (W : Matrix n n ℝ) : Block (n := n) := fromBlocks 1 0 W 1
def coordinateDerivative (Wdot : Matrix n n ℝ) : Block (n := n) := fromBlocks 0 0 (-Wdot) 0

theorem coordinate_derivative (W : ℝ → Matrix n n ℝ) {Wdot : Matrix n n ℝ}
    {t : ℝ} (hW : HasDerivAt W Wdot t) :
    HasDerivAt (fun s => coordinateChange (W s)) (coordinateDerivative Wdot) t := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  rcases i with i | i <;> rcases j with j | j
  · exact hasDerivAt_const t ((1 : Matrix n n ℝ) i j)
  · exact hasDerivAt_const t 0
  · exact (hasDerivAt_pi.mp (hasDerivAt_pi.mp hW i) j).neg
  · exact hasDerivAt_const t ((1 : Matrix n n ℝ) i j)

@[simp] theorem cancel (W : Matrix n n ℝ) :
    coordinateChange W * coordinateInverse W = 1 := by
  simp [coordinateChange, coordinateInverse, fromBlocks_multiply, fromBlocks_one]

@[simp] theorem cancel' (W : Matrix n n ℝ) :
    coordinateInverse W * coordinateChange W = 1 := by
  simp [coordinateChange, coordinateInverse, fromBlocks_multiply, fromBlocks_one]

/-- Time-varying generator intertwining, including the frame acceleration. -/
theorem connection (G W Wdot : Matrix n n ℝ) :
    coordinateDerivative Wdot + coordinateChange W * logGenerator G W =
      classicalGenerator G W Wdot * coordinateChange W := by
  simp only [coordinateDerivative, coordinateChange, logGenerator, classicalGenerator,
    fromBlocks_multiply, Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero,
    add_zero, zero_add, fromBlocks_add]
  congr 1 <;> simp [two_smul, add_mul, mul_neg, neg_mul] <;> abel

end GNC.RotatingVariational
