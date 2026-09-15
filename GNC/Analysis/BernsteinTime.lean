import GNC.Analysis.BernsteinPolynomial
import GNC.Analysis.CirclePolynomial

/-! Time-polynomial envelopes using checked Bernstein parameter bounds.
The circle representation uses the nonnegative interval for 1-cos(theta);
ordinary angle polynomials use the full signed pointing interval.
-/
namespace GNC.BernsteinTime
open Planning.PolynomialKernel

def bivariate (p : BivariatePolynomial.Coefficients) (lo hi : ℚ) : List ℚ :=
  p.map (fun row => BernsteinPolynomial.checked row lo hi)

theorem bivariate_nonnegative (p : BivariatePolynomial.Coefficients) (lo hi : ℚ) :
    PolynomialOrder.nonnegative (bivariate p lo hi) := by
  intro b hb
  rcases List.mem_map.mp hb with ⟨row,_,rfl⟩
  exact BernsteinPolynomial.checked_nonnegative row lo hi

theorem bivariate_sound (p : BivariatePolynomial.Coefficients) {lo hi : ℚ} {t θ : ℝ}
    (hinterval : lo < hi) (ht : 0 ≤ t) (hθ : θ ∈ Set.Icc (lo:ℝ) hi) :
    |BivariatePolynomial.value p t θ| ≤ PolynomialOrder.value (bivariate p lo hi) t := by
  induction p with
  | nil => simp [BivariatePolynomial.value,BivariatePolynomial.slice,bivariate,
      PolynomialOrder.value,evaluate]
  | cons row p ih =>
    have hrow := BernsteinPolynomial.checked_sound row hinterval hθ
    exact (abs_add_le (BivariatePolynomial.row row θ) (t*BivariatePolynomial.value p t θ)).trans
      (add_le_add hrow (show |t*BivariatePolynomial.value p t θ| ≤
        t*PolynomialOrder.value (bivariate p lo hi) t by
          rw [abs_mul,abs_of_nonneg ht]
          exact mul_le_mul_of_nonneg_left ih ht))

def circle (p : CirclePolynomial.Coefficients) (a : ℚ) : List ℚ :=
  PolynomialBounds.add (bivariate p.even 0 (a^2/2))
    (PolynomialBounds.scale a (bivariate p.odd 0 (a^2/2)))

theorem circle_nonnegative (p : CirclePolynomial.Coefficients) {a : ℚ} (ha : 0 ≤ a) :
    PolynomialOrder.nonnegative (circle p a) :=
  PolynomialOrder.nonnegative_add _ _ (bivariate_nonnegative _ _ _)
    (PolynomialOrder.nonnegative_scale ha _ (bivariate_nonnegative _ _ _))

theorem circle_sound (p : CirclePolynomial.Coefficients) {a : ℚ} {t θ : ℝ}
    (ha : 0 < a) (ht : 0 ≤ t) (hθ : |θ| ≤ (a:ℝ)) :
    |CirclePolynomial.value p t θ| ≤ PolynomialOrder.value (circle p a) t := by
  have ha' : (0:ℝ) ≤ a := (abs_nonneg θ).trans hθ
  have hc : 1-Real.cos θ ∈ Set.Icc ((0:ℚ):ℝ) ((a^2/2:ℚ):ℝ) := by
    constructor
    · simpa using sub_nonneg.mpr (Real.cos_le_one θ)
    · have hh := CirclePolynomial.cosine_bound θ
      push_cast
      nlinarith [sq_abs θ,abs_nonneg θ,le_abs_self (1-Real.cos θ)]
  have he := bivariate_sound p.even (by positivity : (0:ℚ) < a^2/2) ht hc
  have ho := bivariate_sound p.odd (by positivity : (0:ℚ) < a^2/2) ht hc
  have hs := (Real.abs_sin_le_abs (x := θ)).trans hθ
  have hm := mul_le_mul hs ho (abs_nonneg _) ha'
  have hb := (abs_add_le (BivariatePolynomial.value p.even t (1-Real.cos θ))
    (Real.sin θ*BivariatePolynomial.value p.odd t (1-Real.cos θ))).trans
      (add_le_add he (by simpa only [abs_mul] using hm))
  simpa only [CirclePolynomial.value,circle,PolynomialOrder.value_add,
    PolynomialOrder.value_scale] using hb

/-- Records that no fallback was used for any parameter row. -/
def accepted (p : BivariatePolynomial.Coefficients) (lo hi : ℚ) : Prop :=
  ∀ row ∈ p, BernsteinPolynomial.valid row lo hi (BernsteinPolynomial.degree row)
    (BernsteinPolynomial.proposal row lo hi)
instance (p : BivariatePolynomial.Coefficients) (lo hi : ℚ) :
    Decidable (accepted p lo hi) := by unfold accepted; infer_instance

def circleAccepted (p : CirclePolynomial.Coefficients) (a : ℚ) : Prop :=
  accepted p.even 0 (a^2/2) ∧ accepted p.odd 0 (a^2/2)
instance (p : CirclePolynomial.Coefficients) (a : ℚ) : Decidable (circleAccepted p a) := by
  unfold circleAccepted; infer_instance

end GNC.BernsteinTime
