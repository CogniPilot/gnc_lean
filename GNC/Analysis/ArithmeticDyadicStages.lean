import GNC.Analysis.ArithmeticDyadic
import GNC.Analysis.ArithmeticStages

/-! Dependency-certified reuse remains exact for the specified dyadic
rounding evaluator. Every query reads the same prepared values; its output
is not fed into the next query. Thus batch length does not enlarge the
individual graph's rounding budget. No mutable-memory or IEEE claim is made. -/
namespace GNC.ArithmeticProgram.Rounding
variable {n : ℕ}

theorem stepRat_input_eq (N : ℕ) (allowed : Fin n → Bool) (a b : Fin n → ℚ)
    (previous : List ℚ) (op : Instruction n) (hop : op.usesOnly allowed=true)
    (h : ∀ i, allowed i=true → a i=b i) :
    stepRat N a previous op=stepRat N b previous op := by
  cases op with
  | input i => exact h i hop
  | _ => rfl

theorem roundedRatFrom_input_eq (N : ℕ) (allowed : Fin n → Bool)
    (a b : Fin n → ℚ) (code : List (Instruction n)) (hcode : usesOnly allowed code=true)
    (h : ∀ i, allowed i=true → a i=b i) (previous : List ℚ) :
    roundedRatFrom N a previous code=roundedRatFrom N b previous code := by
  induction code generalizing previous with
  | nil => rfl
  | cons op code ih =>
    have hc : op.usesOnly allowed=true ∧ usesOnly allowed code=true := by
      simpa [usesOnly] using hcode
    simp only [roundedRatFrom, stepRat_input_eq N allowed a b previous op hc.1 h]
    exact ih hc.2 _

theorem roundedRatFrom_append (N : ℕ) (input : Fin n → ℚ) (previous : List ℚ)
    (prepare query : List (Instruction n)) :
    roundedRatFrom N input previous (prepare++query)=
      roundedRatFrom N input (roundedRatFrom N input previous prepare) query := by
  induction prepare generalizing previous with
  | nil => rfl
  | cons op prepare ih => simpa only [List.cons_append, roundedRatFrom] using ih _

def stagedRat (N : ℕ) (prepare query : List (Instruction n))
    (cachedInput input : Fin n → ℚ) : List ℚ :=
  roundedRatFrom N input (roundedRatFrom N cachedInput [] prepare) query

/-- Preparation once and independent queries exactly reproduce complete
rounded graph evaluations, not just their real-arithmetic limits. -/
theorem stagedRat_eq (N : ℕ) (allowed : Fin n → Bool)
    (prepare query : List (Instruction n)) (cachedInput input : Fin n → ℚ)
    (hcode : usesOnly allowed prepare=true)
    (h : ∀ i, allowed i=true → cachedInput i=input i) :
    stagedRat N prepare query cachedInput input=roundedRatFrom N input [] (prepare++query) := by
  have hp := roundedRatFrom_input_eq N allowed cachedInput input prepare hcode h []
  simp only [stagedRat, hp, roundedRatFrom_append]

end GNC.ArithmeticProgram.Rounding
