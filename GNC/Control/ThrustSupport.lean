import GNC.Lie.Euclidean
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Directional bounds for uncertain thrust, preserving unit length and
constant pointing offsets across a burn. These are support certificates,
not a claim that every spacecraft disturbance is a pointing rotation.
-/
noncomputable section
open Matrix Real
namespace GNC.ThrustSupport

def Cap (n : Vec3) (κ : ℝ) : Set Vec3 :=
  {q | q ⬝ᵥ q = 1 ∧ κ ≤ n ⬝ᵥ q}

theorem dot_le_enorm (h q : Vec3) : h ⬝ᵥ q ≤ enorm h*enorm q := by
  have hh := real_inner_le_norm (WithLp.toLp 2 q : EuclideanSpace ℝ (Fin 3))
    (WithLp.toLp 2 h : EuclideanSpace ℝ (Fin 3))
  change h ⬝ᵥ star q ≤ enorm q*enorm h at hh
  simpa only [star_trivial, mul_comm] using hh

theorem unit_enorm (q : Vec3) (hq : q ⬝ᵥ q = 1) : enorm q = 1 := by
  have he := enorm_sq q
  rw [← dot_self_lengthSq, hq] at he
  nlinarith [enorm_nonneg q]

/-- A nonnegative multiplier produces an upper support bound for a spherical
cap. Optimizing the multiplier is optional; validity is algebraic. -/
def dualBound (n h : Vec3) (κ ell : ℝ) : ℝ := enorm (h+ell • n)-ell*κ

theorem cap_support_bound (n h q : Vec3) (κ ell : ℝ)
    (hq : q ∈ Cap n κ) (hell : 0 ≤ ell) : h ⬝ᵥ q ≤ dualBound n h κ ell := by
  have hh := dot_le_enorm (h+ell • n) q
  rw [unit_enorm q hq.1, mul_one, add_dotProduct, smul_dotProduct, smul_eq_mul] at hh
  have hm := mul_le_mul_of_nonneg_left hq.2 hell
  dsimp [dualBound]
  linarith

/-- Exact squared chord distance for two physical unit directions. -/
theorem chord_sq (n q : Vec3) (hn : n ⬝ᵥ n = 1) (hq : q ⬝ᵥ q = 1) :
    enorm (q-n)^2 = 2*(1-n ⬝ᵥ q) := by
  rw [enorm_sq, ← dot_self_lengthSq]
  simp only [sub_dotProduct, dotProduct_sub, hn, hq, dotProduct_comm q n]
  ring

/-- The usual isotropic chord ball is a valid outer enclosure of the cap.
The nonnegative radius δ may be any certified upper bound on its radius. -/
theorem cap_in_chord_ball (n q : Vec3) (κ δ : ℝ)
    (hn : n ⬝ᵥ n = 1) (hq : q ∈ Cap n κ)
    (hδ : 0 ≤ δ) (hr : 2*(1-κ) ≤ δ^2) : enorm (q-n) ≤ δ := by
  have he := chord_sq n q hn hq.1
  nlinarith [hq.2, enorm_nonneg (q-n)]

def ballBound (n h : Vec3) (δ : ℝ) : ℝ := h ⬝ᵥ n+δ*enorm h

theorem chord_ball_support (n h q : Vec3) (δ : ℝ)
    (hq : enorm (q-n) ≤ δ) : h ⬝ᵥ q ≤ ballBound n h δ := by
  have hh := dot_le_enorm h (q-n)
  rw [dotProduct_sub] at hh
  have hm := mul_le_mul_of_nonneg_left hq (enorm_nonneg h)
  dsimp [ballBound]
  nlinarith

/-- Taking the smaller certified bound guarantees that adding geometry
cannot make the support enclosure more conservative than the ball. -/
theorem combined_support (n h q : Vec3) (κ δ ell : ℝ)
    (hn : n ⬝ᵥ n = 1) (hq : q ∈ Cap n κ)
    (hδ : 0 ≤ δ) (hr : 2*(1-κ) ≤ δ^2) (hell : 0 ≤ ell) :
    h ⬝ᵥ q ≤ min (dualBound n h κ ell) (ballBound n h δ) :=
  le_min (cap_support_bound n h q κ ell hq hell)
    (chord_ball_support n h q δ (cap_in_chord_ball n q κ δ hn hq hδ hr))

/-- A rational support certificate need only verify a squared length and
a sign. No numerical square root is accepted as a proof oracle. -/
theorem cap_support_of_squared_bound (n h q : Vec3) (κ ell s : ℝ)
    (hq : q ∈ Cap n κ) (hell : 0 ≤ ell) (hs : 0 ≤ s)
    (hbound : lengthSq (h+ell • n) ≤ s^2) : h ⬝ᵥ q ≤ s-ell*κ := by
  have hh := cap_support_bound n h q κ ell hq hell
  have hn := enorm_sq (h+ell • n)
  dsimp [dualBound] at hh
  nlinarith [enorm_nonneg (h+ell • n)]

/-- The transverse decomposition underlying the cap's closed-form support. -/
theorem transverse_sq (n h : Vec3) (hn : n ⬝ᵥ n = 1) :
    enorm (h-(h ⬝ᵥ n) • n)^2 = enorm h^2-(h ⬝ᵥ n)^2 := by
  simp only [enorm_sq, ← dot_self_lengthSq, sub_dotProduct, dotProduct_sub,
    smul_dotProduct, dotProduct_smul, smul_eq_mul, hn, dotProduct_comm n h]
  ring

/-- Boundary-branch formula, using κ²+τ²=1 instead of assuming a numerical
trigonometric evaluation is exact. Its hypotheses include the branch test. -/
theorem cap_boundary_support (n h q : Vec3) {κ tau : ℝ}
    (hn : n ⬝ᵥ n = 1) (hq : q ∈ Cap n κ) (ht : 0 < tau)
    (hsphere : κ^2+tau^2 = 1)
    (hbranch : (h ⬝ᵥ n)*tau ≤ enorm (h-(h ⬝ᵥ n) • n)*κ) :
    h ⬝ᵥ q ≤ (h ⬝ᵥ n)*κ+enorm (h-(h ⬝ᵥ n) • n)*tau := by
  let a := h ⬝ᵥ n
  let b := enorm (h-a • n)
  let ell := b*κ/tau-a
  have hell : 0 ≤ ell := by
    dsimp [ell]
    exact sub_nonneg.mpr ((le_div_iff₀ ht).mpr hbranch)
  have hb : 0 ≤ b := enorm_nonneg _
  have ht0 : tau ≠ 0 := ne_of_gt ht
  have hsq : b^2 = enorm h^2-a^2 := transverse_sq n h hn
  have hlength : lengthSq (h+ell • n) = (b/tau)^2 := by
    rw [← dot_self_lengthSq]
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
      smul_eq_mul, hn, dotProduct_comm n h, dot_self_lengthSq]
    rw [← enorm_sq]
    change enorm h^2+ell*a+ell*(a+ell*1) = (b/tau)^2
    dsimp [ell]
    field_simp
    nlinarith [congrArg (fun z : ℝ => b^2*z) hsphere,
      congrArg (fun z : ℝ => z*tau^2) hsq]
  have bound := cap_support_of_squared_bound n h q κ ell (b/tau) hq hell
    (div_nonneg hb ht.le) hlength.le
  have value : b/tau-ell*κ = a*κ+b*tau := by
    dsimp [ell]
    field_simp
    nlinarith [congrArg (fun z : ℝ => b*z) hsphere]
  rw [value] at bound
  exact bound

/-- At zero pointing uncertainty the physical direction is exactly n. -/
theorem cap_one_eq (n q : Vec3) (hn : n ⬝ᵥ n = 1) (hq : q ∈ Cap n 1) : q = n := by
  have h := cap_in_chord_ball n q 1 0 hn hq (by norm_num) (by norm_num)
  have he : enorm (q-n) = 0 := le_antisymm h (enorm_nonneg _)
  exact sub_eq_zero.mp ((enorm_eq_zero_iff _).mp he)

variable {ι : Type*} [Fintype ι]

/-- A constant physical pointing direction is shared by every sample of a
burn. Sum the sensitivity first; this is an exact identity, not independence. -/
theorem coherent_pairing (h : ι → Vec3) (q : Vec3) :
    (∑ i, h i) ⬝ᵥ q = ∑ i, h i ⬝ᵥ q := by
  simp only [sum_dotProduct]

theorem coherent_support (n : Vec3) (h : ι → Vec3) (q : Vec3) (κ ell : ℝ)
    (hq : q ∈ Cap n κ) (hell : 0 ≤ ell) :
    (∑ i, h i ⬝ᵥ q) ≤ dualBound n (∑ i, h i) κ ell := by
  rw [← coherent_pairing]
  exact cap_support_bound n (∑ i, h i) q κ ell hq hell

/-- Fuel-feasibility constraints preserve order under smaller support
coefficients, because commanded burn magnitudes are nonnegative. -/
theorem support_constraint_mono (u geometric ball : ι → ℝ) (offset budget : ℝ)
    (hu : ∀ i, 0 ≤ u i) (horder : ∀ i, geometric i ≤ ball i)
    (hfeasible : offset+∑ i, u i*ball i ≤ budget) :
    offset+∑ i, u i*geometric i ≤ budget := by
  have hh : (∑ i, u i*geometric i) ≤ ∑ i, u i*ball i :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (horder i) (hu i)
  linarith

end GNC.ThrustSupport
