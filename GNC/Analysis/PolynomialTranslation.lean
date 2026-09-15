import GNC.Analysis.PolynomialBounds

/-! Recenter exact coefficient lists before bounding a polynomial interval.
The arithmetic algorithm and its real evaluation identity are checked. A
generator can choose the center and subdivision; the bound covers every
real point in the corresponding interval, not just its sampled nodes.
-/
namespace GNC.PolynomialTranslation
open Planning.PolynomialKernel PolynomialBounds
variable {K : Type*} [CommRing K]

def translate (a : K) : List K → List K
  | [] => []
  | c :: cs => add [c] (multiply [a,1] (translate a cs))

theorem evaluate_translate (a : K) (cs : List K) (x : K) :
    evaluate (translate a cs) x = evaluate cs (a+x) := by
  induction cs with
  | nil => simp [translate, evaluate]
  | cons c cs ih => simp [translate, evaluate_add, evaluate_multiply, evaluate, ih]

theorem translate_map {L : Type*} [CommRing L] (f : K →+* L) (a : K) (cs : List K) :
    (translate a cs).map f = translate (f a) (cs.map f) := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [translate, add_map, multiply_map, ih]

theorem rational_translate (a : ℚ) (cs : List ℚ) (x : ℝ) :
    evaluate ((translate a cs).map (Rat.castHom ℝ)) x =
      evaluate (cs.map (Rat.castHom ℝ)) ((a:ℝ)+x) := by
  rw [translate_map, evaluate_translate]
  rfl

theorem centered_bound (cs : List ℚ) (a h : ℚ) {x : ℝ}
    (hx : |x-(a:ℝ)| ≤ (h:ℝ)) :
    |evaluate (cs.map (Rat.castHom ℝ)) x| ≤ (bound (translate a cs) h:ℚ) := by
  have hb := bound_sound (translate a cs) hx
  rw [rational_translate] at hb
  simpa only [add_sub_cancel] using hb

theorem centered_error (cs proposed : List ℚ) (a h : ℚ) {x : ℝ}
    (hx : |x-(a:ℝ)| ≤ (h:ℝ)) :
    |evaluate (cs.map (Rat.castHom ℝ)) x-evaluate (proposed.map (Rat.castHom ℝ)) x| ≤
      (bound (translate a (subtract cs proposed)) h:ℚ) := by
  have hb := centered_bound (subtract cs proposed) a h hx
  simpa only [subtract_map, evaluate_subtract] using hb

end GNC.PolynomialTranslation
