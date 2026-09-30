import GNC.Analysis.ArithmeticRounding

/-! Executable rational evaluation with rounding after each arithmetic node.
Rationals are used as a specification for an unbounded-integer dyadic backend;
there is no claim of IEEE semantics, bounded-integer overflow safety or CPU cost. -/
namespace GNC.ArithmeticProgram.Rounding
variable {n : ℕ}

def stepRat (N : ℕ) (input : Fin n → ℚ) (previous : List ℚ) : Instruction n → ℚ
  | .constant c => dyadicRat N c
  | .input i => input i
  | .add i j => dyadicRat N (previous.getD i 0+previous.getD j 0)
  | .multiply i j => dyadicRat N (previous.getD i 0*previous.getD j 0)
  | .negate i => -previous.getD i 0

def roundedRatFrom (N : ℕ) (input : Fin n → ℚ) (previous : List ℚ) :
    List (Instruction n) → List ℚ
  | [] => previous
  | op::code => roundedRatFrom N input (previous++[stepRat N input previous op]) code

theorem stepRat_cast (N : ℕ) (input : Fin n → ℚ) (previous : List ℚ) (op : Instruction n) :
    (stepRat N input previous op:ℝ)=
      stepValue (dyadic N) (fun i => (input i:ℝ)) (previous.map fun q : ℚ => (q:ℝ)) op := by
  have hg (i : ℕ) : (previous.map fun q : ℚ => (q:ℝ)).getD i 0=(previous.getD i 0:ℝ) := by
    simpa only [Rat.cast_zero] using List.getD_map (l := previous) (d := (0:ℚ)) (n := i)
      (fun q : ℚ => (q:ℝ))
  cases op <;> simp only [stepRat, stepValue, dyadic_cast, hg, Rat.cast_add, Rat.cast_mul, Rat.cast_neg]

theorem roundedRatFrom_cast (N : ℕ) (input : Fin n → ℚ) (previous : List ℚ)
    (code : List (Instruction n)) :
    (roundedRatFrom N input previous code).map (fun q : ℚ => (q:ℝ))=
      roundedFrom (dyadic N) (fun i => (input i:ℝ)) (previous.map fun q : ℚ => (q:ℝ)) code := by
  induction code generalizing previous with
  | nil => rfl
  | cons op code ih =>
    simp only [roundedRatFrom, roundedFrom]
    rw [ih]
    simp only [List.map_append, List.map_cons, List.map_nil, stepRat_cast]

/-- The executable evaluator satisfies the graph's propagated error budget. -/
theorem rational_output_error {N : ℕ} (hN : 0<N)
    (input : Fin n → Budget) (x : Fin n → ℝ) (y : Fin n → ℚ)
    (hi : ∀ i, Holds (input i) (x i) (y i:ℝ)) (code : List (Instruction n)) (index : ℕ) :
    |((roundedRatFrom N y [] code).getD index 0:ℝ)-(values code x).getD index 0|≤
      ((budgetsFrom (1/(2*N)) input [] code).getD index zero).error := by
  have h := output_error (1/(2*N)) (by positivity) (dyadic N)
    (by intro z; simpa only [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast,
        Rat.cast_one] using dyadic_error hN z) input x (fun i => (y i:ℝ)) hi code index
  have hc := roundedRatFrom_cast N y [] code
  have hg := List.getD_map (l := roundedRatFrom N y [] code) (d := (0:ℚ)) (n := index)
    (fun q : ℚ => (q:ℝ))
  rw [hc] at hg
  simp only [List.map_nil, Rat.cast_zero] at hg
  rw [hg] at h
  exact h

end GNC.ArithmeticProgram.Rounding
