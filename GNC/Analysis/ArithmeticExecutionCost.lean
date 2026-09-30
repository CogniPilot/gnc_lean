import GNC.Analysis.ArithmeticDyadic

/-! An explicit primitive-operation model for the rational evaluator.
Binary rational arithmetic, dyadic quantization, and negation are counted
separately. These counts exclude allocation, indexing, integer bit complexity,
compiler behavior, and proof checking; they are not CPU costs.
-/
namespace GNC.ArithmeticProgram.Rounding

structure Work where
  binary : ℕ := 0
  quantize : ℕ := 0
  negate : ℕ := 0
  deriving DecidableEq, Repr

def Work.plus (a b : Work) : Work :=
  ⟨a.binary+b.binary,a.quantize+b.quantize,a.negate+b.negate⟩

def Work.repeat (a : Work) (n : ℕ) : Work :=
  ⟨n*a.binary,n*a.quantize,n*a.negate⟩

def instructionWork {n : ℕ} : Instruction n → Work
  | .constant _ => ⟨0,1,0⟩
  | .input _ => ⟨0,0,0⟩
  | .add _ _ | .multiply _ _ => ⟨1,1,0⟩
  | .negate _ => ⟨0,0,1⟩

def work {n : ℕ} : List (Instruction n) → Work
  | [] => ⟨0,0,0⟩
  | op::code => (instructionWork op).plus (work code)

/-- Instrument the same evaluator without replacing its rounding semantics. -/
def meteredFrom {n : ℕ} (N : ℕ) (input : Fin n → ℚ) (previous : List ℚ) :
    List (Instruction n) → List ℚ × Work
  | [] => (previous,⟨0,0,0⟩)
  | op::code =>
    let rest := meteredFrom N input (previous++[stepRat N input previous op]) code
    (rest.1,(instructionWork op).plus rest.2)

theorem metered_correct {n : ℕ} (N : ℕ) (input : Fin n → ℚ)
    (previous : List ℚ) (code : List (Instruction n)) :
    meteredFrom N input previous code=(roundedRatFrom N input previous code,work code) := by
  induction code generalizing previous with
  | nil => rfl
  | cons op code ih => simp only [meteredFrom, ih, roundedRatFrom, work]

theorem work_binary {n : ℕ} (code : List (Instruction n)) :
    (work code).binary=arithmetic code := by
  induction code with
  | nil => rfl
  | cons op code ih => cases op <;>
      simp_all [work, instructionWork, Work.plus, arithmetic, Instruction.arithmetic]

end GNC.ArithmeticProgram.Rounding
