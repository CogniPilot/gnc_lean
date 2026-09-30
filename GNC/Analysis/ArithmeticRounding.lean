import GNC.Analysis.ArithmeticProgram
import Mathlib.Data.Rat.Floor

/-! Absolute-error propagation for a straight-line arithmetic graph.
The rounder contract is explicit. A dyadic implementation below discharges
it globally; no assertion about Lean's `Float` or CPU instructions is made. -/
namespace GNC.ArithmeticProgram.Rounding

structure Budget where
  magnitude : ℚ
  error : ℚ
  deriving DecidableEq

def zero : Budget := ⟨0, 0⟩
def Holds (b : Budget) (x y : ℝ) : Prop :=
  0≤b.magnitude ∧ 0≤b.error ∧ |x|≤(b.magnitude:ℝ) ∧ |y-x|≤(b.error:ℝ)

theorem zero_holds : Holds zero 0 0 := by norm_num [Holds, zero]

theorem approximate_bound {b : Budget} {x y : ℝ} (h : Holds b x y) :
    |y|≤(b.magnitude:ℝ)+(b.error:ℝ) := by
  have ht := abs_add_le x (y-x)
  have he := h.2.2.2
  have hx := h.2.2.1
  rw [add_sub_cancel] at ht
  linarith

theorem product_error {a b : Budget} {x y u v : ℝ}
    (ha : Holds a x y) (hb : Holds b u v) :
    |y*v-x*u|≤(a.magnitude*b.error+b.magnitude*a.error+a.error*b.error:ℚ) := by
  have he : y*v-x*u=x*(v-u)+u*(y-x)+(y-x)*(v-u) := by ring
  rw [he]
  have h1 := mul_le_mul ha.2.2.1 hb.2.2.2 (abs_nonneg _) (by exact_mod_cast ha.1)
  have h2 := mul_le_mul hb.2.2.1 ha.2.2.2 (abs_nonneg _) (by exact_mod_cast hb.1)
  have h3 := mul_le_mul ha.2.2.2 hb.2.2.2 (abs_nonneg _) (by exact_mod_cast ha.2.1)
  simp only [Rat.cast_add, Rat.cast_mul]
  calc
    _ ≤ |x*(v-u)+u*(y-x)|+|(y-x)*(v-u)| := abs_add_le _ _
    _ ≤ (|x*(v-u)|+|u*(y-x)|)+|(y-x)*(v-u)| := add_le_add (abs_add_le _ _) (le_refl _)
    _ ≤ _ := by simpa only [abs_mul] using add_le_add (add_le_add h1 h2) h3

variable {n : ℕ}

def stepBudget (δ : ℚ) (input : Fin n → Budget) (previous : List Budget) : Instruction n → Budget
  | .constant c => ⟨|c|, δ⟩
  | .input i => input i
  | .add i j =>
    let a := previous.getD i zero; let b := previous.getD j zero
    ⟨a.magnitude+b.magnitude, a.error+b.error+δ⟩
  | .multiply i j =>
    let a := previous.getD i zero; let b := previous.getD j zero
    ⟨a.magnitude*b.magnitude, a.magnitude*b.error+b.magnitude*a.error+a.error*b.error+δ⟩
  | .negate i => previous.getD i zero

noncomputable def stepValue (round : ℝ → ℝ) (input : Fin n → ℝ)
    (previous : List ℝ) : Instruction n → ℝ
  | .constant c => round c
  | .input i => input i
  | .add i j => round (previous.getD i 0+previous.getD j 0)
  | .multiply i j => round (previous.getD i 0*previous.getD j 0)
  | .negate i => -previous.getD i 0

theorem step_sound (δ : ℚ) (hδ : 0≤δ) (round : ℝ → ℝ)
    (hr : ∀ z, |round z-z|≤(δ:ℝ))
    (input : Fin n → Budget) (x y : Fin n → ℝ)
    (hi : ∀ i, Holds (input i) (x i) (y i))
    (bs : List Budget) (xs ys : List ℝ)
    (hp : ∀ i, Holds (bs.getD i zero) (xs.getD i 0) (ys.getD i 0)) (op : Instruction n) :
    Holds (stepBudget δ input bs op) (op.eval (Rat.castHom ℝ) x xs)
      (stepValue round y ys op) := by
  cases op with
  | constant c =>
    simp only [stepBudget, Instruction.eval, stepValue, Holds]
    exact ⟨abs_nonneg _, hδ, by simp, hr _⟩
  | input i => exact hi i
  | add i j =>
    obtain ⟨ha, hea, hxa, hexa⟩ := hp i
    obtain ⟨hb, heb, hxb, hexb⟩ := hp j
    simp only [stepBudget, Instruction.eval, stepValue, Holds]
    refine ⟨add_nonneg ha hb, add_nonneg (add_nonneg hea heb) hδ, ?_, ?_⟩
    · simpa only [Rat.cast_add] using (abs_add_le _ _).trans (add_le_add hxa hxb)
    · have ht := abs_sub_le (round (ys.getD i 0+ys.getD j 0))
        (ys.getD i 0+ys.getD j 0) (xs.getD i 0+xs.getD j 0)
      have he : ys.getD i 0+ys.getD j 0-(xs.getD i 0+xs.getD j 0)=
          (ys.getD i 0-xs.getD i 0)+(ys.getD j 0-xs.getD j 0) := by ring
      rw [he] at ht
      have he' := (abs_add_le _ _).trans (add_le_add hexa hexb)
      have hr' := hr (ys.getD i 0+ys.getD j 0)
      simp only [Rat.cast_add]
      linarith
  | multiply i j =>
    have ha := hp i
    have hb := hp j
    simp only [stepBudget, Instruction.eval, stepValue, Holds]
    refine ⟨mul_nonneg ha.1 hb.1, add_nonneg (add_nonneg (add_nonneg (mul_nonneg ha.1 hb.2.1) (mul_nonneg hb.1 ha.2.1)) (mul_nonneg ha.2.1 hb.2.1)) hδ, ?_, ?_⟩
    · simpa only [Rat.cast_mul, abs_mul] using
        mul_le_mul ha.2.2.1 hb.2.2.1 (abs_nonneg _) (by exact_mod_cast ha.1)
    · have ht := abs_sub_le (round (ys.getD i 0*ys.getD j 0))
        (ys.getD i 0*ys.getD j 0) (xs.getD i 0*xs.getD j 0)
      have he := product_error ha hb
      have hr' := hr (ys.getD i 0*ys.getD j 0)
      simp only [Rat.cast_add] at he ⊢
      linarith
  | negate i =>
    simpa only [stepBudget, Instruction.eval, stepValue, Holds, neg_sub_neg, abs_neg,
      abs_sub_comm] using hp i

/-- Matching graph prefixes, including a safe zero default for unused indices. -/
def Consistent (bs : List Budget) (xs ys : List ℝ) : Prop :=
  xs.length=bs.length ∧ ys.length=bs.length ∧
    ∀ i, Holds (bs.getD i zero) (xs.getD i 0) (ys.getD i 0)

theorem getD_append_one {α : Type*} (xs : List α) (a d : α) (i : ℕ) :
    (xs++[a]).getD i d=if i<xs.length then xs.getD i d else if i=xs.length then a else d := by
  by_cases hi : i<xs.length
  · simp only [if_pos hi, List.getD_append xs [a] d i hi]
  · rw [List.getD_append_right xs [a] d i (Nat.le_of_not_gt hi)]
    by_cases he : i=xs.length
    · subst i; simp
    · have hd : [a].length ≤ i-xs.length := by simp only [List.length_singleton]; omega
      rw [List.getD_eq_default [a] d hd]
      simp [hi, he]

theorem consistent_append {bs : List Budget} {xs ys : List ℝ}
    (h : Consistent bs xs ys) {b : Budget} {x y : ℝ} (hb : Holds b x y) :
    Consistent (bs++[b]) (xs++[x]) (ys++[y]) := by
  refine ⟨by simp [h.1], by simp [h.2.1], ?_⟩
  intro i
  simp only [getD_append_one, h.1, h.2.1]
  split_ifs <;> first | exact h.2.2 i | exact hb | exact zero_holds

def budgetsFrom (δ : ℚ) (input : Fin n → Budget) (previous : List Budget) :
    List (Instruction n) → List Budget
  | [] => previous
  | op::code => budgetsFrom δ input (previous++[stepBudget δ input previous op]) code

noncomputable def roundedFrom (round : ℝ → ℝ) (input : Fin n → ℝ) (previous : List ℝ) :
    List (Instruction n) → List ℝ
  | [] => previous
  | op::code => roundedFrom round input (previous++[stepValue round input previous op]) code

theorem run_sound (δ : ℚ) (hδ : 0≤δ) (round : ℝ → ℝ)
    (hr : ∀ z, |round z-z|≤(δ:ℝ))
    (input : Fin n → Budget) (x y : Fin n → ℝ)
    (hi : ∀ i, Holds (input i) (x i) (y i))
    (code : List (Instruction n)) (bs : List Budget) (xs ys : List ℝ)
    (hp : Consistent bs xs ys) :
    Consistent (budgetsFrom δ input bs code) (runFrom (Rat.castHom ℝ) x xs code)
      (roundedFrom round y ys code) := by
  induction code generalizing bs xs ys with
  | nil => exact hp
  | cons op code ih =>
    exact ih _ _ _ (consistent_append hp (step_sound δ hδ round hr input x y hi bs xs ys hp.2.2 op))

/-- The rational budget pays for all graph-node rounding and input errors. -/
theorem output_error (δ : ℚ) (hδ : 0≤δ) (round : ℝ → ℝ)
    (hr : ∀ z, |round z-z|≤(δ:ℝ))
    (input : Fin n → Budget) (x y : Fin n → ℝ)
    (hi : ∀ i, Holds (input i) (x i) (y i)) (code : List (Instruction n)) (index : ℕ) :
    |(roundedFrom round y [] code).getD index 0-(values code x).getD index 0|≤
      ((budgetsFrom δ input [] code).getD index zero).error := by
  have h := run_sound δ hδ round hr input x y hi code [] [] []
    ⟨rfl, rfl, fun _ => zero_holds⟩
  exact (h.2.2 index).2.2.2

/-- Nearest dyadic rounding, ties toward positive infinity as in mathlib's
integer `round`. The grid spacing is exactly 1/N. -/
noncomputable def dyadic (N : ℕ) (x : ℝ) : ℝ := (round ((N:ℝ)*x):ℤ)/N

def dyadicRat (N : ℕ) (x : ℚ) : ℚ := (round ((N:ℚ)*x):ℤ)/N

theorem dyadic_cast (N : ℕ) (x : ℚ) : (dyadicRat N x:ℝ)=dyadic N x := by
  simp only [dyadicRat, dyadic, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast]
  congr 1
  rw [←Rat.round_cast (α := ℝ)]
  simp

theorem dyadic_error {N : ℕ} (hN : 0<N) (x : ℝ) :
    |dyadic N x-x|≤(1:ℝ)/(2*N) := by
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have h := abs_sub_round ((N:ℝ)*x)
  rw [abs_sub_comm] at h
  have he : dyadic N x-x=((round ((N:ℝ)*x):ℤ)-(N:ℝ)*x)/N := by
    dsimp [dyadic]; field_simp
  rw [he, abs_div, abs_of_pos hn]
  calc
    _ ≤ (1/2)/(N:ℝ) := div_le_div_of_nonneg_right h hn.le
    _ = _ := by ring

end GNC.ArithmeticProgram.Rounding
