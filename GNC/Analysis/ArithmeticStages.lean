import GNC.Analysis.ArithmeticProgram

/-! Reuse a phase-only prefix for many independent uncertainty queries.
The reuse theorem is about exact ring evaluation. It does not validate
storage, parallel execution or floating arithmetic. -/
namespace GNC.ArithmeticProgram
variable {n : ℕ}

def Instruction.usesOnly (allowed : Fin n → Bool) : Instruction n → Bool
  | .input i => allowed i
  | _ => true

def usesOnly (allowed : Fin n → Bool) (code : List (Instruction n)) : Bool :=
  code.all (Instruction.usesOnly allowed)

theorem Instruction.eval_input_eq {K : Type*} [CommRing K] (coeff : ℚ →+* K)
    (allowed : Fin n → Bool) (a b : Fin n → K) (previous : List K) (op : Instruction n)
    (hop : op.usesOnly allowed=true) (h : ∀ i, allowed i=true → a i=b i) :
    op.eval coeff a previous=op.eval coeff b previous := by
  cases op with
  | input i => exact h i hop
  | _ => rfl

theorem runFrom_input_eq {K : Type*} [CommRing K] (coeff : ℚ →+* K)
    (allowed : Fin n → Bool) (a b : Fin n → K) (code : List (Instruction n))
    (hcode : usesOnly allowed code=true) (h : ∀ i, allowed i=true → a i=b i)
    (previous : List K) : runFrom coeff a previous code=runFrom coeff b previous code := by
  induction code generalizing previous with
  | nil => rfl
  | cons op code ih =>
    have hc : op.usesOnly allowed=true ∧ usesOnly allowed code=true := by
      simpa [usesOnly] using hcode
    simp only [runFrom, Instruction.eval_input_eq coeff allowed a b previous op hc.1 h]
    exact ih hc.2 _

theorem runFrom_append {K : Type*} [CommRing K] (coeff : ℚ →+* K) (input : Fin n → K)
    (previous : List K) (prepare query : List (Instruction n)) :
    runFrom coeff input previous (prepare++query)=
      runFrom coeff input (runFrom coeff input previous prepare) query := by
  induction prepare generalizing previous with
  | nil => rfl
  | cons op prepare ih => simpa only [List.cons_append, runFrom] using ih _

noncomputable def stagedValues (prepare query : List (Instruction n))
    (cachedInput input : Fin n → ℝ) : List ℝ :=
  runFrom (Rat.castHom ℝ) input (values prepare cachedInput) query

/-- A prefix computed from any inputs agreeing on its dependencies can be
reused without changing the predictor at any other input. -/
theorem stagedValues_eq (allowed : Fin n → Bool) (prepare query : List (Instruction n))
    (cachedInput input : Fin n → ℝ) (hcode : usesOnly allowed prepare=true)
    (h : ∀ i, allowed i=true → cachedInput i=input i) :
    stagedValues prepare query cachedInput input=values (prepare++query) input := by
  have hp := runFrom_input_eq (Rat.castHom ℝ) allowed cachedInput input prepare hcode h []
  simp only [stagedValues, values, hp, runFrom_append]

/-- Arithmetic work for one preparation and m queries; data movement and
loads are outside this operation model. -/
def batchArithmetic (prepare query : List (Instruction n)) (m : ℕ) : ℕ :=
  arithmetic prepare+m*arithmetic query

end GNC.ArithmeticProgram
