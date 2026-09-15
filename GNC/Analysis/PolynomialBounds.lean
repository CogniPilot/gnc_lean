import GNC.Planning.PolynomialKernel

/-! Exact coefficient bounds for polynomial differential defects. A floating
or symbolic program may propose coefficients; the bounds below concern the
entire real interval and use only rational arithmetic in their executable part.
-/
namespace GNC.PolynomialBounds
open Planning.PolynomialKernel
variable {K : Type*} [CommRing K]

def add : List K → List K → List K
  | [], bs => bs
  | as, [] => as
  | a :: as, b :: bs => (a+b) :: add as bs

def scale (a : K) (bs : List K) : List K := bs.map (a * ·)

def multiply : List K → List K → List K
  | [], _ => []
  | a :: as, bs => add (scale a bs) (0 :: multiply as bs)

def subtract (as bs : List K) : List K := add as (scale (-1) bs)

theorem evaluate_add (as bs : List K) (x : K) :
    evaluate (add as bs) x = evaluate as x + evaluate bs x := by
  induction as generalizing bs with
  | nil => simp [add, evaluate]
  | cons a as ih =>
    cases bs <;> simp [add, evaluate, ih] <;> ring

theorem evaluate_scale (a : K) (bs : List K) (x : K) :
    evaluate (scale a bs) x = a * evaluate bs x := by
  induction bs with
  | nil => simp [scale, evaluate]
  | cons b bs ih => simp [scale, evaluate, scale] at *; rw [ih]; ring

theorem evaluate_multiply (as bs : List K) (x : K) :
    evaluate (multiply as bs) x = evaluate as x * evaluate bs x := by
  induction as with
  | nil => simp [multiply, evaluate]
  | cons a as ih => simp [multiply, evaluate_add, evaluate_scale, evaluate, ih]; ring

theorem evaluate_subtract (as bs : List K) (x : K) :
    evaluate (subtract as bs) x = evaluate as x - evaluate bs x := by
  simp [subtract, evaluate_add, evaluate_scale, sub_eq_add_neg]

theorem add_map {L : Type*} [CommRing L] (f : K →+* L) (as bs : List K) :
    (add as bs).map f = add (as.map f) (bs.map f) := by
  induction as generalizing bs with
  | nil => rfl
  | cons a as ih => cases bs <;> simp [add, ih]

theorem scale_map {L : Type*} [CommRing L] (f : K →+* L) (a : K) (bs : List K) :
    (scale a bs).map f = scale (f a) (bs.map f) := by
  simp [scale, List.map_map, Function.comp_def]

theorem multiply_map {L : Type*} [CommRing L] (f : K →+* L) (as bs : List K) :
    (multiply as bs).map f = multiply (as.map f) (bs.map f) := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [multiply, add_map, scale_map, ih]

theorem subtract_map {L : Type*} [CommRing L] (f : K →+* L) (as bs : List K) :
    (subtract as bs).map f = subtract (as.map f) (bs.map f) := by
  simp [subtract, add_map, scale_map]

/-- Absolute coefficient sum on a symmetric interval of radius `h`. -/
def bound (cs : List ℚ) (h : ℚ) : ℚ := evaluate (cs.map abs) h

theorem absolute_bound (cs : List ℝ) {x h : ℝ} (hx : |x| ≤ h) :
    |evaluate cs x| ≤ evaluate (cs.map abs) h := by
  have hh : 0 ≤ h := (abs_nonneg x).trans hx
  induction cs with
  | nil => simp [evaluate]
  | cons a cs ih =>
    simp only [evaluate, List.map_cons]
    calc
      _ ≤ |a| + |x| * |evaluate cs x| := by simpa [abs_mul] using abs_add_le a (x*evaluate cs x)
      _ ≤ |a| + h * evaluate (List.map abs cs) h := by
        linarith [mul_le_mul hx ih (abs_nonneg _) hh]

theorem bound_sound (cs : List ℚ) {x : ℝ} {h : ℚ} (hx : |x| ≤ (h : ℝ)) :
    |evaluate (cs.map (Rat.castHom ℝ)) x| ≤ (bound cs h : ℚ) := by
  have he : evaluate ((cs.map (Rat.castHom ℝ)).map abs) (h : ℝ) =
      ((bound cs h : ℚ) : ℝ) := by
    have hm := evaluate_map (Rat.castHom ℝ) (cs.map abs) h
    simpa [bound, List.map_map, Function.comp_def] using hm
  exact (absolute_bound _ hx).trans_eq he

theorem evaluate_hasDerivAt (cs : List ℝ) (x : ℝ) :
    HasDerivAt (evaluate cs) (evaluate (differentiate cs) x) x := by
  convert (polynomial cs).hasDerivAt x using 1
  · funext t
    exact evaluate_correct cs t
  · rw [evaluate_correct, differentiate_correct]

end GNC.PolynomialBounds
