import GNC.Analysis.BallMonomial
import GNC.Analysis.CoefficientNormProfile

/-! Polynomial norm profiles over a full three-axis ball. This reuses the
same rational coefficient-norm and decomposition checks as the disk checker;
the monomial weight now includes all three powers jointly. Both Cartesian
and Lie-coordinate residuals can use it. -/
namespace GNC.BallNormProfile
open DiskPolynomial ParameterPolynomial

def TermValid {n : ℕ} (p : DiskTimePolynomial.Term n) (σ : ℚ) : Prop :=
  CoefficientNormProfile.Valid p.curve.coefficients p.curve.bound ∧ 0≤p.monomialBound ∧
    σ^(2*(p.u+p.v+p.c))*(p.u:ℚ)^p.u*(p.v:ℚ)^p.v*(p.c:ℚ)^p.c ≤
      p.monomialBound^2*((p.u+p.v+p.c:ℕ):ℚ)^(p.u+p.v+p.c)

instance {n : ℕ} (p : DiskTimePolynomial.Term n) (σ : ℚ) : Decidable (TermValid p σ) := by
  unfold TermValid
  infer_instance

structure CertificateValid {n : ℕ} (D : DiskTimePolynomial.Certificate n)
    (p : Vector n) (σ : ℚ) : Prop where
  terms : ∀ k, TermValid (D.terms k) σ
  decomposition : ∀ i, ParameterPolynomial.zero
    (ParameterPolynomial.subtract (p i) (D.polynomial i))

noncomputable section

/-- The third exponent is included in the ball monomial weight. Therefore
the existing certificate's bound is evaluated at axial multiplier one. -/
theorem certifies {n : ℕ} (D : DiskTimePolynomial.Certificate n) (p : Vector n) {σ : ℚ}
    (hD : CertificateValid D p σ) {x : Fin 3 → ℝ}
    (hx : x 0^2+x 1^2+x 2^2≤(σ:ℝ)^2)
    {t : ℝ} (ht : 0≤t) : ‖vectorValue p x t‖≤PolynomialOrder.value (D.bound 1) t := by
  have he : vectorValue p x t=vectorValue D.polynomial x t := by
    ext i
    exact ParameterPolynomial.identity _ _ (hD.decomposition i) x t
  rw [he,D.polynomial_value,D.bound_value]
  simp only [Rat.cast_one,one_pow,mul_one]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro k _
  have hmon := BallMonomial.certifies
    (show (0:ℝ)≤(D.terms k).monomialBound by exact_mod_cast (hD.terms k).2.1)
    hx (D.terms k).u (D.terms k).v (D.terms k).c
    (by exact_mod_cast (hD.terms k).2.2)
  rw [norm_smul,Real.norm_eq_abs]
  exact mul_le_mul hmon (CoefficientNormProfile.sound _ _ (hD.terms k).1 ht)
    (norm_nonneg _) (by exact_mod_cast (hD.terms k).2.1)

end
end GNC.BallNormProfile
