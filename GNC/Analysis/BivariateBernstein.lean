import GNC.Analysis.BivariatePolynomial
import GNC.Analysis.BernsteinPolynomial

/-! Exact tensor-product Bernstein certificates on rectangles. Conversion
and subdivision proposals are untrusted; coefficient reconstruction checks
the complete polynomial. Mathlib supplies Bernstein positivity and unity.
-/
namespace GNC.BivariateBernstein
open BivariatePolynomial
open scoped BigOperators unitInterval

def rationalValue (p : Coefficients) (u v : ℚ) : ℚ :=
  Planning.PolynomialKernel.evaluate (p.map (fun row => Planning.PolynomialKernel.evaluate row v)) u

theorem rationalValue_cast (p : Coefficients) (u v : ℚ) :
    (rationalValue p u v : ℝ) = value p (u:ℝ) (v:ℝ) := by
  induction p with
  | nil => simp [rationalValue, value, slice, Planning.PolynomialKernel.evaluate]
  | cons a p ih =>
    have hr : row a (v:ℝ) = ((Planning.PolynomialKernel.evaluate a v:ℚ):ℝ) :=
      PolynomialOrder.value_at_rational a v
    change ((Planning.PolynomialKernel.evaluate a v + u*rationalValue p u v:ℚ):ℝ) =
      row a (v:ℝ) + (u:ℝ)*value p (u:ℝ) (v:ℝ)
    push_cast
    rw [hr, ih]

def composeRow : List ℚ → Coefficients → Coefficients
  | [], _ => []
  | a::p, q => add [[a]] (multiply q (composeRow p q))

def compose : Coefficients → Coefficients → Coefficients → Coefficients
  | [], _, _ => []
  | a::p, u, v => add (composeRow a v) (multiply u (compose p u v))

theorem value_composeRow (p : List ℚ) (q : Coefficients) (x y : ℝ) :
    value (composeRow p q) x y = PolynomialOrder.value p (value q x y) := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    rw [composeRow, value_add, value_multiply, ih]
    have hc : value [[a]] x y = (a:ℝ) := by
      simp [value, slice, row, Planning.PolynomialKernel.evaluate]
    rw [hc]
    rfl

theorem value_compose (p u v : Coefficients) (x y : ℝ) :
    value (compose p u v) x y = value p (value u x y) (value v x y) := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    rw [compose, value_add, value_composeRow, value_multiply, ih]
    rfl

def shift (p : Coefficients) (lo hi bot top : ℚ) : Coefficients :=
  compose p [[lo],[hi-lo]] [[bot,top-bot]]

theorem value_shift (p : Coefficients) (lo hi bot top : ℚ) (x y : ℝ) :
    value (shift p lo hi bot top) x y =
      value p ((lo:ℝ)+(hi-lo)*x) ((bot:ℝ)+(top-bot)*y) := by
  rw [shift, value_compose]
  congr 1 <;> simp [value, slice, row, Planning.PolynomialKernel.evaluate] <;> ring

def zero (p : Coefficients) : Prop := ∀ row ∈ p, BernsteinPolynomial.zero row
instance (p : Coefficients) : Decidable (zero p) := by unfold zero; infer_instance

theorem value_zero (p : Coefficients) (h : zero p) (x y : ℝ) : value p x y = 0 := by
  have hz (p : List ℚ) (hp : BernsteinPolynomial.zero p) : row p y = 0 := by
    induction p with
    | nil => rfl
    | cons a p ih =>
      have ha := hp a (by simp)
      have hr := ih (fun a ha => hp a (by simp [ha]))
      change (a:ℝ) + y * row p y = 0
      simp [ha,hr]
  induction p with
  | nil => rfl
  | cons a p ih =>
    change row a y + x * value p x y = 0
    rw [hz a (h a (by simp)), ih (fun a ha => h a (by simp [ha]))]
    ring

private theorem row_power (p : List ℚ) (n : ℕ) (x : ℝ) :
    row (BernsteinPolynomial.power p n) x = row p x ^ n := by
  induction n with
  | zero => simp [BernsteinPolynomial.power, row, Planning.PolynomialKernel.evaluate]
  | succ n ih => rw [BernsteinPolynomial.power, row_multiply, ih, pow_succ]; ring

private theorem row_basis (n k : ℕ) (x : I) :
    row (BernsteinPolynomial.basis n k) x = bernstein n k x := by
  rw [BernsteinPolynomial.basis, row_scale, row_multiply, row_power, row_power,
    bernstein_apply]
  simp [row, Planning.PolynomialKernel.evaluate, sub_eq_add_neg, mul_assoc]

private theorem row_combine (n : ℕ) (b : Fin (n+1) → ℚ) (x : I) :
    row (BernsteinPolynomial.combine n b) x = ∑ k, (b k:ℝ)*bernstein n k x := by
  have hf (l : List (Fin (n+1))) : row
      (l.foldr (fun k p => PolynomialBounds.add
        (PolynomialBounds.scale (b k) (BernsteinPolynomial.basis n k)) p) []) x =
      (l.map (fun k => (b k:ℝ)*bernstein n k x)).sum := by
    induction l with
    | nil => rfl
    | cons k l ih => simp only [List.foldr_cons, row_add, row_scale, row_basis,
        ih, List.map_cons, List.sum_cons]
  rw [BernsteinPolynomial.combine, hf]
  rw [← List.sum_toFinset _ (List.nodup_finRange _), List.toFinset_finRange]

def outerProduct (p q : List ℚ) : Coefficients :=
  p.map fun a => PolynomialBounds.scale a q

theorem value_outerProduct (p q : List ℚ) (x y : ℝ) :
    value (outerProduct p q) x y = row p x * row q y := by
  induction p with
  | nil => simp [outerProduct, value, slice, row, Planning.PolynomialKernel.evaluate]
  | cons a p ih =>
    change row (PolynomialBounds.scale a q) y + x * value (outerProduct p q) x y =
      ((a:ℝ)+x*row p x)*row q y
    rw [row_scale, ih]
    ring

def combine (n m : ℕ) (b : Fin (n+1) → Fin (m+1) → ℚ) : Coefficients :=
  (List.finRange (n+1)).foldr (fun (i : Fin (n+1)) p => add
    (outerProduct (BernsteinPolynomial.basis n i) (BernsteinPolynomial.combine m (b i))) p) []

theorem value_combine (n m : ℕ) (b : Fin (n+1) → Fin (m+1) → ℚ) (x y : I) :
    value (combine n m b) x y = ∑ i : Fin (n+1), bernstein n i x *
      ∑ j : Fin (m+1), (b i j:ℝ)*bernstein m j y := by
  have hf (l : List (Fin (n+1))) : value
      (l.foldr (fun (i : Fin (n+1)) p => add (outerProduct (BernsteinPolynomial.basis n i)
        (BernsteinPolynomial.combine m (b i))) p) []) x y =
      (l.map fun (i : Fin (n+1)) => bernstein n i x * ∑ j : Fin (m+1), (b i j:ℝ)*bernstein m j y).sum := by
    induction l with
    | nil => rfl
    | cons i l ih => simp only [List.foldr_cons, value_add, value_outerProduct,
        row_basis, row_combine, ih, List.map_cons, List.sum_cons]
  rw [combine, hf]
  rw [← List.sum_toFinset _ (List.nodup_finRange _), List.toFinset_finRange]

def valid (p : Coefficients) (lo hi bot top : ℚ) (n m : ℕ)
    (b : Fin (n+1) → Fin (m+1) → ℚ) : Prop :=
  zero (subtract (combine n m b) (shift p lo hi bot top))
instance (p : Coefficients) (lo hi bot top : ℚ) (n m : ℕ)
    (b : Fin (n+1) → Fin (m+1) → ℚ) : Decidable (valid p lo hi bot top n m b) := by
  unfold valid
  infer_instance

theorem combine_upper (n m : ℕ) (b : Fin (n+1) → Fin (m+1) → ℚ)
    {upper : ℚ} (hb : ∀ i j, b i j ≤ upper) (x y : I) :
    value (combine n m b) x y ≤ (upper:ℝ) := by
  rw [value_combine]
  have hi (i : Fin (n+1)) : (∑ j, (b i j:ℝ)*bernstein m j y) ≤ (upper:ℝ) := calc
    _ ≤ ∑ j : Fin (m+1), (upper:ℝ)*bernstein m j y := Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_right (by exact_mod_cast hb i j) bernstein_nonneg
    _ = (upper:ℝ) := by rw [← Finset.mul_sum, bernstein.probability, mul_one]
  calc
    _ ≤ ∑ i : Fin (n+1), bernstein n i x*(upper:ℝ) := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (hi i) bernstein_nonneg
    _ = (upper:ℝ) := by rw [← Finset.sum_mul, bernstein.probability, one_mul]

theorem valid_upper (p : Coefficients) {lo hi bot top : ℚ} (hx : lo < hi) (hy : bot < top)
    (n m : ℕ) (b : Fin (n+1) → Fin (m+1) → ℚ) (hc : valid p lo hi bot top n m b)
    {upper : ℚ} (hb : ∀ i j, b i j ≤ upper) {u v : ℝ}
    (hu : u ∈ Set.Icc (lo:ℝ) hi) (hv : v ∈ Set.Icc (bot:ℝ) top) :
    value p u v ≤ (upper:ℝ) := by
  have hxp : (0:ℝ) < (hi:ℝ)-lo := by exact_mod_cast sub_pos.mpr hx
  have hyp : (0:ℝ) < (top:ℝ)-bot := by exact_mod_cast sub_pos.mpr hy
  let x : I := ⟨(u-lo)/((hi:ℝ)-lo),
    ⟨div_nonneg (sub_nonneg.mpr hu.1) hxp.le,
      (div_le_one hxp).mpr (sub_le_sub_right hu.2 _)⟩⟩
  let y : I := ⟨(v-bot)/((top:ℝ)-bot),
    ⟨div_nonneg (sub_nonneg.mpr hv.1) hyp.le,
      (div_le_one hyp).mpr (sub_le_sub_right hv.2 _)⟩⟩
  have he := value_zero _ hc (x:ℝ) (y:ℝ)
  rw [value_subtract, value_shift] at he
  have hxe : (lo:ℝ)+(hi-lo)*(x:ℝ) = u := by dsimp [x]; field_simp; ring
  have hye : (bot:ℝ)+(top-bot)*(y:ℝ) = v := by dsimp [y]; field_simp; ring
  rw [hxe,hye] at he
  rw [← sub_eq_zero.mp he]
  exact combine_upper n m b hb x y

end GNC.BivariateBernstein
