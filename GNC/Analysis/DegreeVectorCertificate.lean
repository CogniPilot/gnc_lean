import GNC.Analysis.AffineProductCertificate

/-! Reassemble vector range certificates without merging their coefficients.
Degree pieces share the same attitude and time parameters throughout. -/
namespace GNC.DegreeVectorCertificate
open ParameterPolynomial BallPolynomialEnclosure DegreeProductCertificate
noncomputable section

theorem vector_sum_value {n m : ℕ} (p : Fin n → DiskPolynomial.Vector m)
    (x : Fin 3 → ℝ) (t : ℝ) :
    DiskPolynomial.vectorValue (fun i => assemble fun d => p d i) x t=
      ∑ d, DiskPolynomial.vectorValue (p d) x t := by
  ext i
  simp [DiskPolynomial.vectorValue,assemble_value]

theorem vector_sum_bound {n m : ℕ} (p : Fin n → DiskPolynomial.Vector m)
    (D : Fin n → DiskTimePolynomial.Certificate m) {σ : ℚ}
    (hD : ∀ d, BallNormProfile.CertificateValid (D d) (p d) σ)
    {x : Fin 3 → ℝ} (hx : x 0^2+x 1^2+x 2^2≤(σ:ℝ)^2) {t : ℝ} (ht : 0≤t) :
    ‖DiskPolynomial.vectorValue (fun i => assemble fun d => p d i) x t‖≤
      PolynomialOrder.value (profileSum fun d => (D d).bound 1) t := by
  rw [vector_sum_value,profileSum_value]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun d _ =>
    BallNormProfile.certifies (D d) (p d) (hD d) hx ht)

theorem component_error {m : ℕ} (v w : EuclideanSpace ℝ (Fin m)) (E : Fin m → ℝ)
    (h : ∀ i, |v i-w i|≤E i) : ‖v‖≤‖w‖+∑ i, E i := by
  have hl1 (z : EuclideanSpace ℝ (Fin m)) : ‖z‖≤∑ i, |z i| := by
    let f : Fin m → EuclideanSpace ℝ (Fin m) := fun i => PiLp.single 2 i (z i)
    have he : z=∑ i, f i := by ext j; simp [f]
    calc
      ‖z‖=‖∑ i, f i‖ := congrArg norm he
      _≤∑ i, ‖f i‖ := norm_sum_le _ _
      _=∑ i, |z i| := by simp [f,PiLp.norm_single,Real.norm_eq_abs]
  have he : ‖v-w‖≤∑ i, E i := (hl1 _).trans (Finset.sum_le_sum fun i _ => h i)
  have hv : v=w+(v-w) := by abel
  calc
    ‖v‖≤‖w‖+‖v-w‖ := by simpa only [←hv] using norm_add_le w (v-w)
    _≤‖w‖+∑ i, E i := add_le_add le_rfl he

end
end GNC.DegreeVectorCertificate
