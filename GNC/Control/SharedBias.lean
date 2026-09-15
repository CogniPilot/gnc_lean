import GNC.Control.ThrustSupport
import GNC.Control.FuelCertificate

/-! Shared body-fixed pointing parameters across multiple burns. The common
uncertainty is retained before taking support bounds. Independent-per-burn
uncertainty is an outer model; a Cartesian calculation with the same shared
parameter has exactly the same constraints. -/
noncomputable section
open Matrix Finset
namespace GNC.SharedBias
open ThrustSupport
variable {ι ρ : Type*} [Fintype ι]

def combined (h : ι → Vec3) (u : ι → ℝ) : Vec3 := ∑ j, u j • h j

theorem combined_pairing (h : ι → Vec3) (u : ι → ℝ) (q : Vec3) :
    combined h u ⬝ᵥ q = ∑ j, u j*(h j ⬝ᵥ q) := by
  simp [combined, sum_dotProduct, smul_dotProduct, smul_eq_mul]

/-- Pulling an output sensitivity into a known body frame is an exact
matrix identity. In particular, a rotation does not change the physics. -/
theorem body_pairing (C : Matrix (Fin 3) (Fin 3) ℝ) (h q : Vec3) :
    h ⬝ᵥ (C *ᵥ q) = (C.transpose *ᵥ h) ⬝ᵥ q := by
  rw [dotProduct_mulVec, ← vecMul_transpose, transpose_transpose]

def CommonFeasible (n : Vec3) (κ : ℝ) (h : ρ → ι → Vec3)
    (b : ρ → ℝ) (u : ι → ℝ) : Prop :=
  ∀ i q, q ∈ Cap n κ → combined (h i) u ⬝ᵥ q ≤ b i

def IndependentFeasible (n : Vec3) (κ : ℝ) (h : ρ → ι → Vec3)
    (b : ρ → ℝ) (u : ι → ℝ) : Prop :=
  ∀ i (q : ι → Vec3), (∀ j, q j ∈ Cap n κ) →
    (∑ j, u j*(h i j ⬝ᵥ q j)) ≤ b i

theorem independent_implies_common (n : Vec3) (κ : ℝ) (h : ρ → ι → Vec3)
    (b : ρ → ℝ) (u : ι → ℝ) (hu : IndependentFeasible n κ h b u) :
    CommonFeasible n κ h b u := by
  intro i q hq
  rw [combined_pairing]
  exact hu i (fun _ => q) (fun _ => hq)

/-- Exact squared-length certificates prove feasibility for every shared
direction. Neither a numerical optimizer nor a square root is a proof oracle. -/
theorem common_of_certificate (n : Vec3) (κ : ℝ) (h : ρ → ι → Vec3)
    (b : ρ → ℝ) (u : ι → ℝ) (ell s : ρ → ℝ)
    (hell : ∀ i, 0 ≤ ell i) (hs : ∀ i, 0 ≤ s i)
    (hlength : ∀ i, lengthSq (combined (h i) u+ell i • n) ≤ (s i)^2)
    (hbudget : ∀ i, s i-ell i*κ ≤ b i) : CommonFeasible n κ h b u := by
  intro i q hq
  exact (cap_support_of_squared_bound n (combined (h i) u) q κ (ell i) (s i)
    hq (hell i) (hs i) (hlength i)).trans (hbudget i)

/-- A feasible uncertainty witness supplies a necessary linear cut. -/
theorem common_implies_cuts (n : Vec3) (κ : ℝ) (h : ρ → ι → Vec3)
    (b : ρ → ℝ) (u : ι → ℝ) (q : ρ → Vec3)
    (hq : ∀ i, q i ∈ Cap n κ) (hu : CommonFeasible n κ h b u) :
    FuelCertificate.Feasible (fun i j => h i j ⬝ᵥ q i) b u := by
  intro i
  have hi := hu i (q i) (hq i)
  rw [combined_pairing] at hi
  simpa only [mul_comm] using hi

/-- Weak duality of necessary cuts gives a lower bound for the full
semi-infinite common-bias problem, even with rounded dual multipliers. -/
theorem common_cost_lower [Fintype ρ] (n : Vec3) (κ : ℝ) (h : ρ → ι → Vec3)
    (b : ρ → ℝ) (c u : ι → ℝ) (q : ρ → Vec3) (ell : ρ → ℝ)
    (hq : ∀ i, q i ∈ Cap n κ) (hu : CommonFeasible n κ h b u)
    (hbox : ∀ j, 0 ≤ u j ∧ u j ≤ 1) (hell : ∀ i, 0 ≤ ell i) :
    FuelCertificate.boxLower (fun i j => h i j ⬝ᵥ q i) b c ell ≤
      FuelCertificate.Cost c u :=
  FuelCertificate.box_weak_duality _ b c u ell
    (common_implies_cuts n κ h b u q hq hu) hbox hell

/-- Independent uncertainty allows a different admissible witness for every
burn in every necessary terminal inequality. -/
theorem independent_cost_lower [Fintype ρ] (n : Vec3) (κ : ℝ)
    (h : ρ → ι → Vec3) (b : ρ → ℝ) (c u : ι → ℝ)
    (q : ρ → ι → Vec3) (ell : ρ → ℝ)
    (hq : ∀ i j, q i j ∈ Cap n κ) (hu : IndependentFeasible n κ h b u)
    (hbox : ∀ j, 0 ≤ u j ∧ u j ≤ 1) (hell : ∀ i, 0 ≤ ell i) :
    FuelCertificate.boxLower (fun i j => h i j ⬝ᵥ q i j) b c ell ≤
      FuelCertificate.Cost c u := by
  apply FuelCertificate.box_weak_duality _ b c u ell ?_ hbox hell
  intro i
  simpa only [mul_comm] using hu i (q i) (hq i)

/-- Fast drift or imperfect correlation is charged separately. The actual
directions need not equal the common bias, and need not be independent. -/
theorem shared_with_drift (n : Vec3) (h : ι → Vec3) (q : Vec3)
    (actual : ι → Vec3) (ε : ι → ℝ) (κ ell : ℝ)
    (hq : q ∈ Cap n κ) (hell : 0 ≤ ell)
    (hε : ∀ j, enorm (actual j-q) ≤ ε j) :
    (∑ j, h j ⬝ᵥ actual j) ≤
      dualBound n (∑ j, h j) κ ell+∑ j, enorm (h j)*ε j := by
  have he (j : ι) : h j ⬝ᵥ actual j ≤ h j ⬝ᵥ q+enorm (h j)*ε j := by
    have hd := (dot_le_enorm (h j) (actual j-q)).trans
      (mul_le_mul_of_nonneg_left (hε j) (enorm_nonneg _))
    rw [dotProduct_sub] at hd
    linarith
  have hs := sum_le_sum (fun j (_ : j ∈ (univ : Finset ι)) => he j)
  rw [sum_add_distrib] at hs
  have hc := coherent_support n h q κ ell hq hell
  linarith

end GNC.SharedBias
