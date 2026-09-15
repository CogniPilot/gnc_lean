import GNC.Control.SharedBias
import GNC.Control.FuelRobustness

/-! Robustness of common-bias fuel programs to certified terminal-map errors.
Vector sensitivity errors control every admissible unit-direction cut. The
candidate keeps shared uncertainty; comparator lower bounds charge the same
physical data errors, including right-hand-side and cost errors.
-/
noncomputable section
open Matrix Finset
namespace GNC.SharedBias
open ThrustSupport FuelCertificate
variable {ι ρ : Type*} [Fintype ι]

theorem pairing_error (h hh q : Vec3) {ε : ℝ}
    (he : enorm (h-hh) ≤ ε) (hq : q ⬝ᵥ q = 1) :
    |h ⬝ᵥ q-hh ⬝ᵥ q| ≤ ε := by
  have hp := dot_le_enorm (h-hh) q
  have hn := dot_le_enorm (-(h-hh)) q
  rw [unit_enorm q hq, mul_one, sub_dotProduct] at hp
  rw [unit_enorm q hq, mul_one, enorm_neg, neg_dotProduct, sub_dotProduct] at hn
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- A tightened common-bias candidate is feasible for the exact vector map.
The row charge uses its actual nonnegative burn fractions. -/
theorem common_feasible_of_errors (n : Vec3) (κ : ℝ)
    (h hh : ρ → ι → Vec3) (e : ρ → ι → ℝ) (b bh db : ρ → ℝ) (x : ι → ℝ)
    (he : ∀ i j, enorm (h i j-hh i j) ≤ e i j)
    (hb : ∀ i, |b i-bh i| ≤ db i) (hx : ∀ j, 0 ≤ x j)
    (htight : CommonFeasible n κ hh (fun i => bh i-db i-∑ j, x j*e i j) x) :
    CommonFeasible n κ h b x := by
  intro i q hq
  have hs := sum_le_sum (fun j (_ : j ∈ (univ : Finset ι)) =>
    mul_le_mul_of_nonneg_left
      (show h i j ⬝ᵥ q ≤ hh i j ⬝ᵥ q+e i j by
        have hp := (abs_le.mp (pairing_error _ _ q (he i j) hq.1)).2
        linarith) (hx j))
  simp only [mul_add, sum_add_distrib] at hs
  have ht := htight i q hq
  rw [combined_pairing] at ht ⊢
  linarith [(abs_le.mp (hb i)).1]

theorem common_lower_of_errors [Fintype ρ] (n : Vec3) (κ : ℝ)
    (h hh : ρ → ι → Vec3) (e : ρ → ι → ℝ) (b bh db ell : ρ → ℝ)
    (c ch dc y : ι → ℝ) (q : ρ → Vec3)
    (he : ∀ i j, enorm (h i j-hh i j) ≤ e i j)
    (hb : ∀ i, |b i-bh i| ≤ db i) (hc : ∀ j, |c j-ch j| ≤ dc j)
    (hq : ∀ i, q i ∈ Cap n κ) (hell : ∀ i, 0 ≤ ell i)
    (hy : CommonFeasible n κ h b y) (hbox : ∀ j, 0 ≤ y j ∧ y j ≤ 1) :
    boxLower (fun i j => hh i j ⬝ᵥ q i) bh ch ell-lowerAllowance ell e db dc ≤ Cost c y := by
  exact lower_of_errors (fun i j => h i j ⬝ᵥ q i) (fun i j => hh i j ⬝ᵥ q i)
    e b bh db ell c ch dc y (fun i j => pairing_error _ _ _ (he i j) (hq i).1)
    hb hc hell (common_implies_cuts n κ h b y q hq hy) hbox

theorem independent_lower_of_errors [Fintype ρ] (n : Vec3) (κ : ℝ)
    (h hh : ρ → ι → Vec3) (e : ρ → ι → ℝ) (b bh db ell : ρ → ℝ)
    (c ch dc y : ι → ℝ) (q : ρ → ι → Vec3)
    (he : ∀ i j, enorm (h i j-hh i j) ≤ e i j)
    (hb : ∀ i, |b i-bh i| ≤ db i) (hc : ∀ j, |c j-ch j| ≤ dc j)
    (hq : ∀ i j, q i j ∈ Cap n κ) (hell : ∀ i, 0 ≤ ell i)
    (hy : IndependentFeasible n κ h b y) (hbox : ∀ j, 0 ≤ y j ∧ y j ≤ 1) :
    boxLower (fun i j => hh i j ⬝ᵥ q i j) bh ch ell-lowerAllowance ell e db dc ≤ Cost c y := by
  apply lower_of_errors (fun i j => h i j ⬝ᵥ q i j) (fun i j => hh i j ⬝ᵥ q i j)
    e b bh db ell c ch dc y (fun i j => pairing_error _ _ _ (he i j) (hq i j).1)
    hb hc hell ?_ hbox
  intro i
  simpa only [mul_comm] using hy i (q i) (hq i)

/-- An exact common positive conversion of cost preserves a strict fuel
ordering. Irrational SI scaling need not be rounded into a new cost model. -/
theorem scaled_propellant_saving (c x y : ι → ℝ) {scale mass exhaust : ℝ}
    (hs : 0 < scale) (hm : 0 < mass) (he : 0 < exhaust)
    (hcost : Cost c x < Cost c y) :
    Propellant.consumedMass mass exhaust (Cost (fun j => scale*c j) x) <
      Propellant.consumedMass mass exhaust (Cost (fun j => scale*c j) y) := by
  apply Propellant.consumed_strictMono hm he
  simpa only [Cost, mul_assoc, ← mul_sum] using mul_lt_mul_of_pos_left hcost hs

end GNC.SharedBias
