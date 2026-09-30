import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.List.GetD
import Mathlib.Tactic

/-! Straight-line rational arithmetic graphs with checked polynomial semantics.
References address previous nodes. The arithmetic count charges additions and
multiplications once per emitted node; negations, constants and loads are
reported separately. This is an exact-real operation model, not a CPU or
floating-point theorem. A graph proposer and its optimizer need not be trusted. -/
namespace GNC.ArithmeticProgram

inductive Instruction (n : ℕ) where
  | constant : ℚ → Instruction n
  | input : Fin n → Instruction n
  | add : ℕ → ℕ → Instruction n
  | multiply : ℕ → ℕ → Instruction n
  | negate : ℕ → Instruction n
  deriving DecidableEq

namespace Instruction
variable {n : ℕ}

def eval {K : Type*} [CommRing K] (coeff : ℚ →+* K) (input : Fin n → K)
    (values : List K) : Instruction n → K
  | .constant c => coeff c
  | .input i => input i
  | .add i j => values.getD i 0+values.getD j 0
  | .multiply i j => values.getD i 0*values.getD j 0
  | .negate i => -values.getD i 0

def valid (size : ℕ) : Instruction n → Prop
  | .constant _ | .input _ => True
  | .add i j | .multiply i j => i<size ∧ j<size
  | .negate i => i<size

instance (size : ℕ) (op : Instruction n) : Decidable (op.valid size) := by
  cases op <;> unfold valid <;> infer_instance

def arithmetic : Instruction n → ℕ
  | .add _ _ | .multiply _ _ => 1
  | _ => 0

def negations : Instruction n → ℕ
  | .negate _ => 1
  | _ => 0

theorem eval_map {K L : Type*} [CommRing K] [CommRing L] (f : K →+* L)
    (coeff : ℚ →+* K) (input : Fin n → K) (values : List K) (op : Instruction n) :
    eval (f.comp coeff) (f ∘ input) (values.map f) op=f (eval coeff input values op) := by
  have hget (i : ℕ) : (values.map f).getD i 0=f (values.getD i 0) := by
    simpa only [map_zero] using List.getD_map (l := values) (d := (0:K)) (n := i) f
  cases op <;> simp only [eval, hget, map_add, map_mul, map_neg, RingHom.comp_apply, Function.comp_apply]

end Instruction
variable {n : ℕ}

def runFrom {K : Type*} [CommRing K] (coeff : ℚ →+* K) (input : Fin n → K)
    (values : List K) : List (Instruction n) → List K
  | [] => values
  | op::code => runFrom coeff input (values++[op.eval coeff input values]) code

def validFrom (size : ℕ) : List (Instruction n) → Prop
  | [] => True
  | op::code => op.valid size ∧ validFrom (size+1) code

instance (size : ℕ) (code : List (Instruction n)) : Decidable (validFrom size code) := by
  induction code generalizing size with
  | nil => exact isTrue trivial
  | cons op code ih => exact @instDecidableAnd _ _ inferInstance (ih (size+1))

def arithmetic (code : List (Instruction n)) : ℕ := (code.map Instruction.arithmetic).sum
def negations (code : List (Instruction n)) : ℕ := (code.map Instruction.negations).sum

theorem runFrom_map {K L : Type*} [CommRing K] [CommRing L] (f : K →+* L)
    (coeff : ℚ →+* K) (input : Fin n → K) (values : List K) (code : List (Instruction n)) :
    runFrom (f.comp coeff) (f ∘ input) (values.map f) code=(runFrom coeff input values code).map f := by
  induction code generalizing values with
  | nil => rfl
  | cons op code ih =>
    simp only [runFrom, Instruction.eval_map]
    simpa only [List.map_append, List.map_cons, List.map_nil] using
      ih (values++[op.eval coeff input values])

noncomputable def polynomials (code : List (Instruction n)) : List (MvPolynomial (Fin n) ℚ) :=
  runFrom MvPolynomial.C MvPolynomial.X [] code

noncomputable def values (code : List (Instruction n)) (input : Fin n → ℝ) : List ℝ :=
  runFrom (Rat.castHom ℝ) input [] code

theorem values_polynomial (code : List (Instruction n)) (input : Fin n → ℝ) :
    values code input=(polynomials code).map (MvPolynomial.eval₂Hom (Rat.castHom ℝ) input) := by
  have h := runFrom_map (MvPolynomial.eval₂Hom (Rat.castHom ℝ) input)
    MvPolynomial.C MvPolynomial.X [] code
  have hc : (MvPolynomial.eval₂Hom (Rat.castHom ℝ) input).comp MvPolynomial.C=Rat.castHom ℝ := by
    ext c
    simp
  have hi : (MvPolynomial.eval₂Hom (Rat.castHom ℝ) input) ∘ MvPolynomial.X=input := by
    funext i
    simp
  simpa only [List.map_nil, hc, hi] using h

/-- A kernel-checked polynomial identity certifies the emitted graph for
all real inputs, including values never sampled by the proposer. -/
theorem output_correct (code : List (Instruction n)) (index : ℕ)
    (expected : MvPolynomial (Fin n) ℚ)
    (h : (polynomials code).getD index 0=expected) (input : Fin n → ℝ) :
    (values code input).getD index 0=MvPolynomial.eval₂ (Rat.castHom ℝ) input expected := by
  rw [values_polynomial]
  have hm := List.getD_map (l := polynomials code) (d := (0:MvPolynomial (Fin n) ℚ))
    (n := index) (MvPolynomial.eval₂Hom (Rat.castHom ℝ) input)
  simpa only [map_zero, h] using hm

end GNC.ArithmeticProgram
