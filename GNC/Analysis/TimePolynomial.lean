import GNC.Analysis.CirclePolynomial
import GNC.Analysis.PolynomialOrder

/-! Polynomial-in-time envelopes for both ordinary and rotation-circle
coefficient algebras. Only the parameter is bounded; time powers remain.+-/
namespace GNC.TimePolynomial
open Planning.PolynomialKernel

def bivariate (p : BivariatePolynomial.Coefficients) (a : ℚ) : List ℚ :=
  p.map (fun row => PolynomialBounds.bound row a)

theorem bivariate_nonnegative (p : BivariatePolynomial.Coefficients) {a : ℚ}
    (ha : 0 ≤ a) : PolynomialOrder.nonnegative (bivariate p a) := by
  intro b hb
  rcases List.mem_map.mp hb with ⟨row,_,rfl⟩
  have h := (abs_nonneg _).trans (PolynomialBounds.bound_sound row
    (x := 0) (h := a) (by simpa only [abs_zero] using (show (0:ℝ) ≤ a by exact_mod_cast ha)))
  exact_mod_cast h

theorem bivariate_sound (p : BivariatePolynomial.Coefficients) {a : ℚ} {t θ : ℝ}
    (ht : 0 ≤ t) (hθ : |θ| ≤ (a:ℝ)) :
    |BivariatePolynomial.value p t θ| ≤ PolynomialOrder.value (bivariate p a) t := by
  induction p with
  | nil => simp [BivariatePolynomial.value,BivariatePolynomial.slice,bivariate,
      PolynomialOrder.value,evaluate]
  | cons row p ih =>
    have hrow := PolynomialBounds.bound_sound row hθ
    have h := (abs_add_le (BivariatePolynomial.row row θ)
      (t*BivariatePolynomial.value p t θ)).trans
      (add_le_add hrow (show |t*BivariatePolynomial.value p t θ| ≤
        t*PolynomialOrder.value (bivariate p a) t by
          rw [abs_mul,abs_of_nonneg ht]
          exact mul_le_mul_of_nonneg_left ih ht))
    exact h

def circle (p : CirclePolynomial.Coefficients) (a : ℚ) : List ℚ :=
  PolynomialBounds.add (bivariate p.even (a^2/2))
    (PolynomialBounds.scale a (bivariate p.odd (a^2/2)))

theorem circle_nonnegative (p : CirclePolynomial.Coefficients) {a : ℚ} (ha : 0 ≤ a) :
    PolynomialOrder.nonnegative (circle p a) :=
  PolynomialOrder.nonnegative_add _ _ (bivariate_nonnegative _ (by positivity))
    (PolynomialOrder.nonnegative_scale ha _ (bivariate_nonnegative _ (by positivity)))

theorem circle_sound (p : CirclePolynomial.Coefficients) {a : ℚ} {t θ : ℝ}
    (ht : 0 ≤ t) (hθ : |θ| ≤ (a:ℝ)) :
    |CirclePolynomial.value p t θ| ≤ PolynomialOrder.value (circle p a) t := by
  have ha : (0:ℝ) ≤ a := (abs_nonneg θ).trans hθ
  have hc : |1-Real.cos θ| ≤ ((a^2/2:ℚ):ℝ) := by
    push_cast
    have h := CirclePolynomial.cosine_bound θ
    nlinarith [sq_abs θ,abs_nonneg θ]
  have he := bivariate_sound p.even ht hc
  have ho := bivariate_sound p.odd ht hc
  have hs := (Real.abs_sin_le_abs (x := θ)).trans hθ
  have hm := mul_le_mul hs ho (abs_nonneg _) ha
  have hb := (abs_add_le (BivariatePolynomial.value p.even t (1-Real.cos θ))
    (Real.sin θ*BivariatePolynomial.value p.odd t (1-Real.cos θ))).trans
      (add_le_add he (by simpa only [abs_mul] using hm))
  simpa only [CirclePolynomial.value,circle,PolynomialOrder.value_add,
    PolynomialOrder.value_scale] using hb

end GNC.TimePolynomial
