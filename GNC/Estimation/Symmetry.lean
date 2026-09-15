import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Tactic
import GNC.Lie.Euclidean

/-! Separating input equivariance, invariance and group-affine dynamics.

The counterexample uses a smooth transitive translation action on the real
Lie group, with a finite-dimensional linear action on polynomial inputs.
Thus equivariance is not dismissed through a trivial/nontransitive action.
-/
noncomputable section
namespace GNC.Estimation

def quadraticField (u : Fin 3 → ℝ) (x : ℝ) : ℝ := u 0+u 1*x+u 2*x^2

def translateInput (s : ℝ) (u : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![u 0-u 1*s+u 2*s^2, u 1-2*u 2*s, u 2]

theorem translation_transitive (x y : ℝ) : ∃ s, x+s=y :=
  ⟨y-x,by ring⟩

theorem input_action_zero (u : Fin 3 → ℝ) : translateInput 0 u = u := by
  ext i
  fin_cases i <;> simp [translateInput]

theorem input_action_add (s t : ℝ) (u : Fin 3 → ℝ) :
    translateInput t (translateInput s u) = translateInput (s+t) u := by
  ext i
  fin_cases i <;> simp [translateInput] <;> ring

theorem input_action_linear (s a b : ℝ) (u v : Fin 3 → ℝ) :
    translateInput s (a • u+b • v) = a • translateInput s u+b • translateInput s v := by
  ext i
  fin_cases i <;> simp [translateInput] <;> ring

/-- The derivative of translation is the identity, so this is precisely
the vector-field/input equivariance identity. -/
theorem quadratic_equivariant (s x : ℝ) (u : Fin 3 → ℝ) :
    quadraticField (translateInput s u) (x+s) = quadraticField u x := by
  simp [quadraticField, translateInput]
  ring

theorem translation_derivative (s x : ℝ) :
    HasDerivAt (fun y : ℝ => y+s) 1 x := (hasDerivAt_id x).add_const s

theorem quadratic_derivative (u : Fin 3 → ℝ) (x : ℝ) :
    HasDerivAt (quadraticField u) (u 1+2*u 2*x) x := by
  convert ((hasDerivAt_const x (u 0)).add ((hasDerivAt_id x).const_mul (u 1))).add
    (((hasDerivAt_id x).pow 2).const_mul (u 2)) using 1 <;> simp [quadraticField] <;> ring

/-- The group-affine identity on the additive real group. -/
def AdditiveGroupAffine (f : ℝ → ℝ) : Prop :=
  ∀ x y, f (x+y)=f x+f y-f 0

theorem equivariant_not_group_affine :
    ¬ AdditiveGroupAffine (quadraticField ![0,0,1]) := by
  intro h
  have hc := h 1 1
  norm_num [quadraticField, Matrix.cons_val_two] at hc

/-- Holding the input fixed gives no translation invariance in this
example, although the input-equivariance identity above holds. -/
theorem equivariant_not_invariant :
    quadraticField ![0,0,1] (0+1) ≠ quadraticField ![0,0,1] 0 := by
  norm_num [quadraticField, Matrix.cons_val_two]

/-- Actual error ODE: the equivariant quadratic family retains a quadratic
error term. It is not an exact linear error model on the Lie algebra. -/
theorem quadratic_error_derivative {x estimate : ℝ → ℝ} {t : ℝ}
    (hx : HasDerivAt x ((x t)^2) t)
    (hh : HasDerivAt estimate ((estimate t)^2) t) :
    HasDerivAt (fun s => x s-estimate s)
      (2*estimate t*(x t-estimate t)+(x t-estimate t)^2) t := by
  convert hx.sub hh using 1
  ring

theorem affine_has_linear_error (a b x estimate : ℝ) :
    (a+b*x)-(a+b*estimate) = b*(x-estimate) := by ring

/-- Group-affine need not mean invariant under a specified action with no
input transformation. A compatible input extension must be stated. -/
theorem affine_not_fixed_input_invariant :
    AdditiveGroupAffine (fun x : ℝ => x) ∧ (1 : ℝ) ≠ 0 := by
  constructor
  · intro x y; ring
  · norm_num

end GNC.Estimation
