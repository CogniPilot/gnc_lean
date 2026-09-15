import GNC.Analysis.ParameterPolynomial

/-! A cheap coefficient-sum range for small polynomial tails. Unlike a
Bernstein conversion this requires only linear work in the coefficient list.
The user chooses this bound when tight range optimization is unnecessary. -/
namespace GNC.ParameterPolynomial
def l1Bound (p : Coefficients) (r : Fin 3 → ℚ) : ℚ :=
  (p.map fun a => PolynomialBounds.bound a.time 1*r 0^a.u*r 1^a.v*r 2^a.c).sum

theorem l1Bound_sound (p : Coefficients) {x : Fin 3 → ℝ} {r : Fin 3 → ℚ}
    (hx : ∀ i, |x i|≤(r i:ℝ)) {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    |value p x t|≤(l1Bound p r:ℝ) := by
  induction p with
  | nil => simp [l1Bound]
  | cons a p ih =>
    have habs : |t|≤((1:ℚ):ℝ) := by simpa only [Rat.cast_one,abs_of_nonneg ht.1] using ht.2
    have hb := PolynomialBounds.bound_sound a.time habs
    have hm := monomial_bound a hx
    have hnonneg : (0:ℝ)≤(PolynomialBounds.bound a.time 1:ℝ) := (abs_nonneg _).trans hb
    have hprod := mul_le_mul hb hm (abs_nonneg _) hnonneg
    rw [value_cons]
    apply (abs_add_le _ _).trans
    have hterm : |termValue a x t|≤(PolynomialBounds.bound a.time 1:ℝ)*
        ((r 0^a.u*r 1^a.v*r 2^a.c:ℚ):ℝ) := by
      simpa only [termValue,abs_mul] using hprod
    convert add_le_add hterm ih using 1 <;> simp [l1Bound] <;> ring
end GNC.ParameterPolynomial
