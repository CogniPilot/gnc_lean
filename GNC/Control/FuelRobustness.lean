import GNC.Control.FuelCertificate
import GNC.Control.Propellant

/-! Fuel comparisons that survive certified errors in propagation coefficients.
The matrices may come from any integrator. Bounds on their errors are inputs,
not inferred from an observed convergence slope or a numerical solver status. -/
noncomputable section
open Finset
namespace GNC.FuelCertificate
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def rowAllowance (e : ι → κ → ℝ) (db : ι → ℝ) (i : ι) : ℝ := db i+∑ j, e i j

def lowerAllowance (ell : ι → ℝ) (e : ι → κ → ℝ) (db : ι → ℝ) (dc : κ → ℝ) : ℝ :=
  (∑ i, ell i*rowAllowance e db i)+∑ j, dc j

/-- Directed coefficient tightening certifies feasibility of the exact
program, for a nonnegative candidate, without trusting floating-point data. -/
theorem feasible_of_errors (A Ah e : ι → κ → ℝ) (b bh db : ι → ℝ) (x : κ → ℝ)
    (hA : ∀ i j, |A i j-Ah i j| ≤ e i j) (hb : ∀ i, |b i-bh i| ≤ db i)
    (hx : ∀ j, 0 ≤ x j)
    (htight : Feasible (fun i j => Ah i j+e i j) (fun i => bh i-db i) x) :
    Feasible A b x := by
  intro i
  have hrow : (∑ j, A i j*x j) ≤ ∑ j, (Ah i j+e i j)*x j := by
    apply sum_le_sum
    intro j _
    exact mul_le_mul_of_nonneg_right (by linarith [(abs_le.mp (hA i j)).2]) (hx j)
  exact hrow.trans ((htight i).trans (by linarith [(abs_le.mp (hb i)).1]))

theorem approximate_feasible_of_errors (A Ah e : ι → κ → ℝ) (b bh db : ι → ℝ)
    (y : κ → ℝ) (hA : ∀ i j, |A i j-Ah i j| ≤ e i j)
    (hb : ∀ i, |b i-bh i| ≤ db i) (hy : Feasible A b y)
    (hbox : ∀ j, 0 ≤ y j ∧ y j ≤ 1) :
    Feasible Ah (fun i => bh i+rowAllowance e db i) y := by
  intro i
  have hrow : (∑ j, Ah i j*y j) ≤ (∑ j, A i j*y j)+(∑ j, e i j) := by
    rw [← sum_add_distrib]
    apply sum_le_sum
    intro j _
    have he := (abs_nonneg (A i j-Ah i j)).trans (hA i j)
    have h₁ := mul_le_mul_of_nonneg_right
      (by linarith [(abs_le.mp (hA i j)).1] : Ah i j ≤ A i j+e i j) (hbox j).1
    have h₂ := mul_le_mul_of_nonneg_left (hbox j).2 he
    nlinarith
  have h := hy i
  have hbi := (abs_le.mp (hb i)).2
  dsimp [rowAllowance]
  linarith

theorem cost_upper_of_errors (c ch dc y : κ → ℝ)
    (hc : ∀ j, |c j-ch j| ≤ dc j) (hbox : ∀ j, 0 ≤ y j ∧ y j ≤ 1) :
    Cost c y ≤ Cost ch y+∑ j, dc j := by
  unfold Cost
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro j _
  have hd := (abs_nonneg (c j-ch j)).trans (hc j)
  have h₁ := mul_le_mul_of_nonneg_right
    (by linarith [(abs_le.mp (hc j)).2] : c j ≤ ch j+dc j) (hbox j).1
  have h₂ := mul_le_mul_of_nonneg_left (hbox j).2 hd
  nlinarith

theorem boxLower_rhs_shift (A : ι → κ → ℝ) (b d ell : ι → ℝ) (c : κ → ℝ) :
    boxLower A (fun i => b i+d i) c ell = boxLower A b c ell-∑ i, ell i*d i := by
  simp only [boxLower, mul_add, sum_add_distrib]
  ring

/-- A lower bound on the exact comparison program after charging all
coefficient, right-hand-side and cost errors in common physical units. -/
theorem lower_of_errors (A Ah e : ι → κ → ℝ) (b bh db ell : ι → ℝ)
    (c ch dc y : κ → ℝ)
    (hA : ∀ i j, |A i j-Ah i j| ≤ e i j) (hb : ∀ i, |b i-bh i| ≤ db i)
    (hc : ∀ j, |c j-ch j| ≤ dc j) (hell : ∀ i, 0 ≤ ell i)
    (hy : Feasible A b y) (hbox : ∀ j, 0 ≤ y j ∧ y j ≤ 1) :
    boxLower Ah bh ch ell-lowerAllowance ell e db dc ≤ Cost c y := by
  have hf := approximate_feasible_of_errors A Ah e b bh db y hA hb hy hbox
  have hl := box_weak_duality Ah (fun i => bh i+rowAllowance e db i) ch y ell hf hbox hell
  rw [boxLower_rhs_shift] at hl
  have hcs := cost_upper_of_errors ch c dc y (fun j => by simpa only [abs_sub_comm] using hc j) hbox
  dsimp [lowerAllowance]
  linarith

/-- Strict physical propellant saving for a candidate whose cost upper bound
beats the error-corrected dual lower bound of the comparison program. Feasibility
of the candidate itself is separately certified by `feasible_of_errors`. -/
theorem strict_propellant_of_errors (A Ah e : ι → κ → ℝ) (b bh db ell : ι → ℝ)
    (c ch dc x y : κ → ℝ) {m₀ exhaust upper : ℝ}
    (hm : 0 < m₀) (he : 0 < exhaust)
    (hA : ∀ i j, |A i j-Ah i j| ≤ e i j) (hb : ∀ i, |b i-bh i| ≤ db i)
    (hc : ∀ j, |c j-ch j| ≤ dc j) (hell : ∀ i, 0 ≤ ell i)
    (hy : Feasible A b y) (hbox : ∀ j, 0 ≤ y j ∧ y j ≤ 1)
    (hupper : Cost c x ≤ upper)
    (hgap : upper < boxLower Ah bh ch ell-lowerAllowance ell e db dc) :
    Propellant.consumedMass m₀ exhaust (Cost c x) <
      Propellant.consumedMass m₀ exhaust (Cost c y) := by
  exact Propellant.consumed_strictMono hm he
    (hupper.trans_lt (hgap.trans_le (lower_of_errors A Ah e b bh db ell c ch dc y
      hA hb hc hell hy hbox)))

end GNC.FuelCertificate
