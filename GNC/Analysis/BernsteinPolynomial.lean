import GNC.Analysis.BernsteinCertificate
import GNC.Analysis.PolynomialOrder

/-! Executable Bernstein range certificates for rational power polynomials.
An arbitrary conversion proposal is accepted only after exact coefficient
reconstruction. Mathlib supplies positivity and partition of unity. Neither
the proposer nor floating-point arithmetic is part of the trust boundary.
-/
namespace GNC.BernsteinPolynomial
open Planning.PolynomialKernel PolynomialBounds
open scoped BigOperators unitInterval

/-- Ascending coefficients of a polynomial power. -/
def power (p : List ℚ) : ℕ → List ℚ
  | 0 => [1]
  | n+1 => multiply p (power p n)

def shift (p : List ℚ) (lo hi : ℚ) : List ℚ :=
  match p with
  | [] => []
  | a::q => add [a] (multiply [lo,hi-lo] (shift q lo hi))

def basis (n k : ℕ) : List ℚ :=
  scale (n.choose k : ℚ) (multiply (power [0,1] k) (power [1,-1] (n-k)))

def combine (n : ℕ) (b : Fin (n+1) → ℚ) : List ℚ :=
  (List.finRange (n+1)).foldr (fun k p => add (scale (b k) (basis n k)) p) []

def zero (p : List ℚ) : Prop := ∀ a ∈ p, a = 0
instance (p : List ℚ) : Decidable (zero p) := by unfold zero; infer_instance

def valid (p : List ℚ) (lo hi : ℚ) (n : ℕ) (b : Fin (n+1) → ℚ) : Prop :=
  zero (subtract (combine n b) (shift p lo hi))
instance (p : List ℚ) (lo hi : ℚ) (n : ℕ) (b : Fin (n+1) → ℚ) :
    Decidable (valid p lo hi n b) := by unfold valid; infer_instance

def maximum (p : List ℚ) : ℚ := p.foldr (fun a m => max |a| m) 0

def bound (n : ℕ) (b : Fin (n+1) → ℚ) : ℚ :=
  maximum ((List.finRange (n+1)).map b)

private theorem value_mul (p q : List ℚ) (x : ℝ) :
    PolynomialOrder.value (multiply p q) x = PolynomialOrder.value p x*PolynomialOrder.value q x := by
  simp only [PolynomialOrder.value,multiply_map,evaluate_multiply]

private theorem value_power (p : List ℚ) (n : ℕ) (x : ℝ) :
    PolynomialOrder.value (power p n) x = PolynomialOrder.value p x^n := by
  induction n with
  | zero => simp [power,PolynomialOrder.value,evaluate]
  | succ n ih => rw [power,value_mul,ih,pow_succ'];

private theorem value_shift (p : List ℚ) (lo hi : ℚ) (x : ℝ) :
    PolynomialOrder.value (shift p lo hi) x =
      PolynomialOrder.value p ((lo:ℝ)+((hi:ℝ)-lo)*x) := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    rw [shift,PolynomialOrder.value_add,value_mul,ih]
    simp only [PolynomialOrder.value,evaluate,List.map_cons,List.map_nil,
      Rat.coe_castHom,Rat.cast_sub]
    ring

private theorem value_basis (n k : ℕ) (x : I) :
    PolynomialOrder.value (basis n k) x = bernstein n k x := by
  rw [basis,PolynomialOrder.value_scale,value_mul,value_power,value_power,bernstein_apply]
  simp [PolynomialOrder.value,evaluate,sub_eq_add_neg,mul_assoc]

private theorem value_combine (n : ℕ) (b : Fin (n+1) → ℚ) (x : I) :
    PolynomialOrder.value (combine n b) x = ∑ k, (b k:ℝ)*bernstein n k x := by
  have hf (l : List (Fin (n+1))) :
      PolynomialOrder.value (l.foldr (fun k p => add (scale (b k) (basis n k)) p) []) x =
      (l.map (fun k => (b k:ℝ)*bernstein n k x)).sum := by
    induction l with
    | nil => simp [PolynomialOrder.value,evaluate]
    | cons k l ih =>
      simp only [List.foldr_cons,PolynomialOrder.value_add,PolynomialOrder.value_scale,
        value_basis,ih,List.map_cons,List.sum_cons]
  rw [combine,hf]
  rw [← List.sum_toFinset _ (List.nodup_finRange _),List.toFinset_finRange]

private theorem value_zero (p : List ℚ) (hp : zero p) (x : ℝ) :
    PolynomialOrder.value p x = 0 := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    have ha := hp a (by simp)
    have ht := ih (fun b hb => hp b (by simp [hb]))
    change (a:ℝ)+x*PolynomialOrder.value p x = 0
    simp [ha,ht]

theorem maximum_nonnegative (p : List ℚ) : 0 ≤ maximum p := by
  induction p with
  | nil => exact le_refl 0
  | cons a p ih => exact ih.trans (le_max_right _ _)

theorem le_maximum (p : List ℚ) {a : ℚ} (ha : a ∈ p) : |a| ≤ maximum p := by
  induction p with
  | nil => simp at ha
  | cons b p ih =>
    rcases List.mem_cons.mp ha with rfl | ha
    · exact le_max_left _ _
    · exact (ih ha).trans (le_max_right _ _)

theorem bound_nonnegative (n : ℕ) (b : Fin (n+1) → ℚ) : 0 ≤ bound n b :=
  maximum_nonnegative _

theorem bound_coefficient (n : ℕ) (b : Fin (n+1) → ℚ) (k : Fin (n+1)) :
    |b k| ≤ bound n b := le_maximum _ (List.mem_map.mpr ⟨k,by simp,rfl⟩)

/-- Exact reconstruction certifies a proposed basis conversion on the whole
real parameter interval, including both endpoints. -/
theorem valid_sound (p : List ℚ) {lo hi : ℚ} (hinterval : lo < hi)
    (n : ℕ) (b : Fin (n+1) → ℚ) (hb : valid p lo hi n b) {θ : ℝ}
    (hθ : θ ∈ Set.Icc (lo:ℝ) hi) :
    |PolynomialOrder.value p θ| ≤ (bound n b:ℝ) := by
  have hw : (0:ℝ) < (hi:ℝ)-lo := by exact_mod_cast sub_pos.mpr hinterval
  let x : I := ⟨(θ-lo)/((hi:ℝ)-lo),
    ⟨div_nonneg (sub_nonneg.mpr hθ.1) hw.le,
      (div_le_one hw).mpr (sub_le_sub_right hθ.2 _)⟩⟩
  have hx : (lo:ℝ)+((hi:ℝ)-lo)*(x:ℝ) = θ := by
    dsimp [x]
    field_simp
    ring
  have he := value_zero _ hb (x:ℝ)
  rw [PolynomialOrder.value_subtract,value_combine,value_shift,hx] at he
  have hcoef (k : Fin (n+1)) : |(b k:ℝ)| ≤ (bound n b:ℝ) := by
    exact_mod_cast bound_coefficient n b k
  calc
    _ = |∑ k, (b k:ℝ)*bernstein n k x| := congrArg abs (sub_eq_zero.mp he).symm
    _ ≤ ∑ k, |(b k:ℝ)*bernstein n k x| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k, |(b k:ℝ)| * bernstein n k x := by simp [abs_mul,abs_of_nonneg bernstein_nonneg]
    _ ≤ ∑ k : Fin (n+1), (bound n b:ℝ)*bernstein n k x :=
      Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_right (hcoef k) bernstein_nonneg)
    _ = (bound n b:ℝ) := by rw [← Finset.mul_sum,bernstein.probability,mul_one]

/-- A conventional power-to-Bernstein proposal. Soundness below does not
assume this formula is correct: exact coefficient reconstruction checks it. -/
def degree (p : List ℚ) : ℕ := (p.reverse.dropWhile (· == 0)).length-1

def proposal (p : List ℚ) (lo hi : ℚ) (k : Fin (degree p+1)) : ℚ :=
  ∑ j ∈ Finset.range p.length, p[j]! *
    ∑ i ∈ Finset.range (min j k.val+1),
      ((j.choose i:ℚ)*(k.val.choose i:ℚ)/((degree p).choose i:ℚ))*lo^(j-i)*(hi-lo)^i

/-- Total sound bounder. An invalid proposal falls back to the absolute
coefficient sum on a symmetric interval covering both endpoints. -/
def checked (p : List ℚ) (lo hi : ℚ) : ℚ :=
  if valid p lo hi (degree p) (proposal p lo hi) then bound (degree p) (proposal p lo hi)
  else PolynomialBounds.bound p (max |lo| |hi|)

theorem checked_nonnegative (p : List ℚ) (lo hi : ℚ) : 0 ≤ checked p lo hi := by
  unfold checked
  split
  · exact bound_nonnegative _ _
  · have h := PolynomialBounds.bound_sound p (x := 0)
      (show |(0:ℝ)| ≤ ((max |lo| |hi|:ℚ):ℝ) by
        exact_mod_cast (abs_nonneg lo).trans (le_max_left _ _))
    exact_mod_cast (abs_nonneg _).trans h

theorem checked_sound (p : List ℚ) {lo hi : ℚ} (hinterval : lo < hi) {θ : ℝ}
    (hθ : θ ∈ Set.Icc (lo:ℝ) hi) :
    |PolynomialOrder.value p θ| ≤ (checked p lo hi:ℝ) := by
  unfold checked
  split
  · exact valid_sound p hinterval _ _ (by assumption) hθ
  · apply PolynomialBounds.bound_sound
    rw [abs_le]
    constructor
    · have h : -(max |lo| |hi|:ℚ) ≤ lo := (neg_le_neg (le_max_left _ _)).trans (neg_abs_le lo)
      exact (show -((max |lo| |hi|:ℚ):ℝ) ≤ (lo:ℝ) by exact_mod_cast h).trans hθ.1
    · have h : hi ≤ (max |lo| |hi|:ℚ) := (le_abs_self hi).trans (le_max_right _ _)
      exact hθ.2.trans (by exact_mod_cast h)

end GNC.BernsteinPolynomial
