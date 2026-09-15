import GNC.Analysis.PolynomialBounds

/-! Exact two-variable polynomial arithmetic for uniform time/parameter
certificates. Outer coefficients are powers of time, inner coefficients
powers of a parameter. Proposals are rational; bounds cover every real point
of the declared rectangle. No grid sampling or floating arithmetic is used.
-/
namespace GNC.BivariatePolynomial
open Planning.PolynomialKernel PolynomialBounds

abbrev Coefficients := List (List ℚ)

noncomputable def row (cs : List ℚ) (x : ℝ) : ℝ :=
  evaluate (cs.map (Rat.castHom ℝ)) x
noncomputable def slice (p : Coefficients) (x : ℝ) : List ℝ := p.map (fun cs => row cs x)
noncomputable def value (p : Coefficients) (t x : ℝ) : ℝ := evaluate (slice p x) t

def add : Coefficients → Coefficients → Coefficients
  | [], q => q
  | p, [] => p
  | a::p,b::q => PolynomialBounds.add a b :: add p q

def scaleRow (a : List ℚ) (p : Coefficients) : Coefficients :=
  p.map (PolynomialBounds.multiply a)

def multiply : Coefficients → Coefficients → Coefficients
  | [], _ => []
  | a::p,q => add (scaleRow a q) ([] :: multiply p q)

def scale (a : ℚ) (p : Coefficients) : Coefficients := p.map (PolynomialBounds.scale a)
def subtract (p q : Coefficients) : Coefficients := add p (scale (-1) q)

def weighted : ℕ → Coefficients → Coefficients
  | _,[] => []
  | n,a::p => PolynomialBounds.scale (n:ℚ) a :: weighted (n+1) p
def derivative (p : Coefficients) : Coefficients := weighted 1 p.tail

def bound : Coefficients → ℚ → ℚ → ℚ
  | [],_,_ => 0
  | a::p,h,b => PolynomialBounds.bound a b+h*bound p h b

theorem row_add (a b : List ℚ) (x : ℝ) :
    row (PolynomialBounds.add a b) x = row a x+row b x := by
  unfold row
  rw [add_map,evaluate_add]
theorem row_multiply (a b : List ℚ) (x : ℝ) :
    row (PolynomialBounds.multiply a b) x = row a x*row b x := by
  unfold row
  rw [multiply_map,evaluate_multiply]
theorem row_scale (a : ℚ) (b : List ℚ) (x : ℝ) :
    row (PolynomialBounds.scale a b) x = (a:ℝ)*row b x := by
  unfold row
  rw [scale_map,evaluate_scale]
  rfl

theorem slice_add (p q : Coefficients) (x : ℝ) :
    slice (add p q) x = PolynomialBounds.add (slice p x) (slice q x) := by
  induction p generalizing q with
  | nil => simp [slice,add,PolynomialBounds.add]
  | cons a p ih =>
    cases q with
    | nil => rfl
    | cons b q =>
      change row (PolynomialBounds.add a b) x :: slice (add p q) x =
        (row a x+row b x) :: PolynomialBounds.add (slice p x) (slice q x)
      rw [row_add,ih]

theorem slice_scaleRow (a : List ℚ) (p : Coefficients) (x : ℝ) :
    slice (scaleRow a p) x = PolynomialBounds.scale (row a x) (slice p x) := by
  induction p with
  | nil => rfl
  | cons b p ih =>
    change row (PolynomialBounds.multiply a b) x :: slice (scaleRow a p) x =
      (row a x*row b x) :: PolynomialBounds.scale (row a x) (slice p x)
    rw [row_multiply,ih]

theorem slice_multiply (p q : Coefficients) (x : ℝ) :
    slice (multiply p q) x = PolynomialBounds.multiply (slice p x) (slice q x) := by
  induction p with
  | nil => simp [slice,multiply,PolynomialBounds.multiply]
  | cons a p ih =>
    simp only [multiply,slice_add,slice_scaleRow]
    simp only [slice,List.map_cons,row,List.map_nil,evaluate,PolynomialBounds.multiply]
    exact congrArg (PolynomialBounds.add _) (congrArg (List.cons 0) ih)

theorem slice_scale (a : ℚ) (p : Coefficients) (x : ℝ) :
    slice (scale a p) x = PolynomialBounds.scale (a:ℝ) (slice p x) := by
  induction p with
  | nil => rfl
  | cons b p ih =>
    change row (PolynomialBounds.scale a b) x :: slice (scale a p) x =
      ((a:ℝ)*row b x) :: PolynomialBounds.scale (a:ℝ) (slice p x)
    rw [row_scale,ih]

theorem value_add (p q : Coefficients) (t x : ℝ) :
    value (add p q) t x = value p t x+value q t x := by
  simp [value,slice_add,evaluate_add]
theorem value_multiply (p q : Coefficients) (t x : ℝ) :
    value (multiply p q) t x = value p t x*value q t x := by
  simp [value,slice_multiply,evaluate_multiply]
theorem value_scale (a : ℚ) (p : Coefficients) (t x : ℝ) :
    value (scale a p) t x = (a:ℝ)*value p t x := by
  simp [value,slice_scale,evaluate_scale]
theorem value_subtract (p q : Coefficients) (t x : ℝ) :
    value (subtract p q) t x = value p t x-value q t x := by
  simp [subtract,value_add,value_scale,sub_eq_add_neg]

theorem slice_weighted (p : Coefficients) (n : ℕ) (x : ℝ) :
    slice (weighted n p) x = Planning.PolynomialKernel.weighted n (slice p x) := by
  induction p generalizing n with
  | nil => simp [weighted,slice,Planning.PolynomialKernel.weighted]
  | cons a p ih =>
    change row (PolynomialBounds.scale (n:ℚ) a) x :: slice (weighted (n+1) p) x =
      ((n:ℝ)*row a x) :: Planning.PolynomialKernel.weighted (n+1) (slice p x)
    rw [row_scale,ih]
    norm_cast

theorem slice_derivative (p : Coefficients) (x : ℝ) :
    slice (derivative p) x = differentiate (slice p x) := by
  cases p with
  | nil => rfl
  | cons a p => exact slice_weighted p 1 x

theorem value_derivative (p : Coefficients) (t x : ℝ) :
    HasDerivAt (fun s => value p s x) (value (derivative p) t x) t := by
  simpa only [value,slice_derivative] using evaluate_hasDerivAt (slice p x) t

theorem value_continuous (p : Coefficients) (x : ℝ) : Continuous (fun t => value p t x) :=
  continuous_iff_continuousAt.mpr (fun t => (value_derivative p t x).continuousAt)

/-- A coefficient sum bounds every time and parameter in the rectangle. -/
theorem bound_sound (p : Coefficients) {h b : ℚ} {t x : ℝ}
    (ht : |t| ≤ (h:ℝ)) (hx : |x| ≤ (b:ℝ)) :
    |value p t x| ≤ (bound p h b:ℝ) := by
  have hh : (0:ℝ) ≤ h := (abs_nonneg t).trans ht
  induction p with
  | nil => simp [value,slice,evaluate,bound]
  | cons a p ih =>
    have ha := PolynomialBounds.bound_sound a hx
    change |row a x+t*value p t x| ≤ _
    have hmul := mul_le_mul ht ih (abs_nonneg _) hh
    have hs := (abs_add_le (row a x) (t*value p t x)).trans
      (add_le_add ha (by simpa only [abs_mul] using hmul))
    simpa only [bound,Rat.cast_add,Rat.cast_mul] using hs

theorem bound_nonneg (p : Coefficients) {h b : ℚ} (hh : 0 ≤ h) (hb : 0 ≤ b) :
    0 ≤ bound p h b := by
  have h := (abs_nonneg (value p 0 0)).trans
    (bound_sound p (t := 0) (x := 0) (by exact_mod_cast hh) (by exact_mod_cast hb))
  exact_mod_cast h

end GNC.BivariatePolynomial
