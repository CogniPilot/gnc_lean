import GNC.Analysis.PolynomialBox

/-! Checked differentiation and quadratic remainder bounds for the polynomial
ODE expression language. The remainder is computed from the expression and
the certified componentwise region/error boxes, not supplied as a tolerance.
These operations support residual validation of a computed adjoint.
-/
namespace GNC.PolynomialODE.Expr
variable {n : ℕ}

def addReduced (a b : Expr n) : Expr n :=
  match a, b with
  | .constant c, .constant d => .constant (c+d)
  | .constant c, b => if c = 0 then b else .add (.constant c) b
  | a, .constant d => if d = 0 then a else .add a (.constant d)
  | a, b => .add a b

def multiplyReduced (a b : Expr n) : Expr n :=
  match a, b with
  | .constant c, .constant d => .constant (c*d)
  | .constant c, b => if c = 0 then .constant 0 else if c = 1 then b else .multiply (.constant c) b
  | a, .constant d => if d = 0 then .constant 0 else if d = 1 then a else .multiply a (.constant d)
  | a, b => .multiply a b

theorem addReduced_value (a b : Expr n) (q : Fin n → ℝ) :
    (addReduced a b).value q = a.value q+b.value q := by
  cases a <;> cases b <;> simp [addReduced, value]
  all_goals split_ifs <;> simp_all [value]

theorem multiplyReduced_value (a b : Expr n) (q : Fin n → ℝ) :
    (multiplyReduced a b).value q = a.value q*b.value q := by
  cases a <;> cases b <;> simp [multiplyReduced, value]
  all_goals split_ifs <;> simp_all [value]

def partialDerivative (e : Expr n) (i : Fin n) : Expr n :=
  match e with
  | .constant _ => .constant 0
  | .var j => .constant (if i = j then 1 else 0)
  | .add a b => addReduced (a.partialDerivative i) (b.partialDerivative i)
  | .multiply a b => addReduced (multiplyReduced a (b.partialDerivative i))
      (multiplyReduced b (a.partialDerivative i))
  | .negate a => .negate (a.partialDerivative i)

noncomputable def linearization (e : Expr n) (q v : Fin n → ℝ) : ℝ :=
  match e with
  | .constant _ => 0
  | .var i => v i
  | .add a b => a.linearization q v + b.linearization q v
  | .multiply a b => a.value q * b.linearization q v + b.value q * a.linearization q v
  | .negate a => -a.linearization q v

theorem linearization_eq_sum (e : Expr n) (q v : Fin n → ℝ) :
    e.linearization q v = ∑ i, (e.partialDerivative i).value q * v i := by
  induction e with
  | constant c => simp [linearization, partialDerivative, value]
  | var j =>
    simp only [linearization]
    rw [Finset.sum_eq_single j]
    · simp [partialDerivative, value]
    · intro i _ hij
      simp [partialDerivative, value, hij]
    · simp
  | add a b ha hb => simp [linearization, partialDerivative, addReduced_value, ha, hb, add_mul, Finset.sum_add_distrib]
  | multiply a b ha hb =>
    simp [linearization, partialDerivative, addReduced_value, multiplyReduced_value, ha, hb, add_mul, Finset.sum_add_distrib,
      Finset.mul_sum, mul_assoc]
  | negate a ha => simp [linearization, partialDerivative, value, ha]

/-- The symbolic operation is the actual derivative along every differentiable
state curve. Mathlib supplies the sum/product/negation differentiation rules. -/
theorem hasDerivAt_value (e : Expr n) {x : ℝ → Fin n → ℝ} {v : Fin n → ℝ} {t : ℝ}
    (hx : HasDerivAt x v t) :
    HasDerivAt (fun s => e.value (x s)) (e.linearization (x t) v) t := by
  induction e with
  | constant c => exact hasDerivAt_const t _
  | var i => exact hasDerivAt_pi.mp hx i
  | add a b ha hb => exact ha.add hb
  | multiply a b ha hb =>
    convert ha.mul hb using 1
    simp only [linearization]
    ring
  | negate a ha => exact ha.neg

noncomputable def remainder (e : Expr n) (x q : Fin n → ℝ) : ℝ :=
  e.value x - e.value q - e.linearization q (x-q)

/-- The exact product remainder exposes two quadratic differences. -/
theorem remainder_multiply (a b : Expr n) (x q : Fin n → ℝ) :
    (a.multiply b).remainder x q = a.value q * b.remainder x q +
      b.value q * a.remainder x q + (a.value x-a.value q)*(b.value x-b.value q) := by
  simp only [remainder, value, linearization]
  ring

def remainderMajorant (e : Expr n) (M E : Fin n → ℚ) : ℚ :=
  match e with
  | .constant _ => 0
  | .var _ => 0
  | .add a b => a.remainderMajorant M E + b.remainderMajorant M E
  | .multiply a b => a.boxMajorant M * b.remainderMajorant M E +
      b.boxMajorant M * a.remainderMajorant M E +
      a.differenceMajorant M E * b.differenceMajorant M E
  | .negate a => a.remainderMajorant M E

theorem remainderMajorant_nonneg (e : Expr n) {M E : Fin n → ℚ}
    (hM : ∀ i, 0 ≤ M i) (hE : ∀ i, 0 ≤ E i) : 0 ≤ e.remainderMajorant M E := by
  induction e with
  | constant _ => exact le_rfl
  | var _ => exact le_rfl
  | add a b ha hb => exact add_nonneg ha hb
  | multiply a b ha hb =>
    exact add_nonneg (add_nonneg (mul_nonneg (a.boxMajorant_nonneg hM) hb)
      (mul_nonneg (b.boxMajorant_nonneg hM) ha))
      (mul_nonneg (a.differenceMajorant_nonneg hM hE) (b.differenceMajorant_nonneg hM hE))
  | negate a ha => exact ha

theorem differenceMajorant_scale (e : Expr n) (M E : Fin n → ℚ) (c : ℚ) :
    e.differenceMajorant M (fun i => c*E i) = c*e.differenceMajorant M E := by
  induction e <;> simp_all only [differenceMajorant] <;> ring

/-- With a fixed regional box, shrinking the error box by c shrinks this
nonlinear remainder allowance by c squared. It is not a first-order allowance. -/
theorem remainderMajorant_scale (e : Expr n) (M E : Fin n → ℚ) (c : ℚ) :
    e.remainderMajorant M (fun i => c*E i) = c^2*e.remainderMajorant M E := by
  induction e <;> simp_all only [remainderMajorant, differenceMajorant_scale] <;> ring

/-- Sound for the full polynomial, including terms of every degree, whenever
both states and their difference lie in the supplied checked boxes. -/
theorem remainder_bound (e : Expr n) {M E : Fin n → ℚ}
    (hM : ∀ i, 0 ≤ M i) (hE : ∀ i, 0 ≤ E i) (x q : Fin n → ℝ)
    (hx : ∀ i, |x i| ≤ (M i : ℝ)) (hq : ∀ i, |q i| ≤ (M i : ℝ))
    (he : ∀ i, |x i-q i| ≤ (E i : ℝ)) :
    |e.remainder x q| ≤ (e.remainderMajorant M E : ℝ) := by
  induction e with
  | constant c => simp [remainder, value, linearization, remainderMajorant]
  | var i => simp [remainder, value, linearization, remainderMajorant]
  | add a b ha hb =>
    have hid : (a.add b).remainder x q = a.remainder x q+b.remainder x q := by
      simp only [remainder, value, linearization]; ring
    rw [hid]
    exact (abs_add_le _ _).trans (by simpa [remainderMajorant] using add_le_add ha hb)
  | multiply a b ha hb =>
    have hma : (0 : ℝ) ≤ a.boxMajorant M := by exact_mod_cast a.boxMajorant_nonneg hM
    have hmb : (0 : ℝ) ≤ b.boxMajorant M := by exact_mod_cast b.boxMajorant_nonneg hM
    have hda : (0 : ℝ) ≤ a.differenceMajorant M E := by
      exact_mod_cast a.differenceMajorant_nonneg hM hE
    have h₁ := mul_le_mul (a.box_value_bound hM q hq) hb (abs_nonneg _) hma
    have h₂ := mul_le_mul (b.box_value_bound hM q hq) ha (abs_nonneg _) hmb
    have h₃ := mul_le_mul (a.box_difference_bound hM hE x q hx hq he)
      (b.box_difference_bound hM hE x q hx hq he) (abs_nonneg _) hda
    rw [remainder_multiply]
    calc
      _ ≤ |a.value q*b.remainder x q|+|b.value q*a.remainder x q|+
          |(a.value x-a.value q)*(b.value x-b.value q)| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ _ := by simpa [abs_mul, remainderMajorant] using add_le_add (add_le_add h₁ h₂) h₃
  | negate a ha =>
    have hid : a.negate.remainder x q = -a.remainder x q := by
      simp only [remainder, value, linearization]; ring
    simpa [hid, remainderMajorant] using ha

end GNC.PolynomialODE.Expr
