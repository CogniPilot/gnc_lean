import GNC.Analysis.DegreeVectorCertificate
import GNC.Applications.OrbitalComparison.JointErrorPolynomial

/-! Compose degreewise affine coefficient identities and whole-ball vector
ranges into the actual executable three-axis residual. The cubic-factor
tail is a separate input of JointErrorPolynomial.Input.physical_defect. -/
namespace GNC.OrbitalComparison.JointErrorPolynomial
open ParameterPolynomial BallPolynomialEnclosure DegreeProductCertificate
open LieSTTOutput
noncomputable section

theorem Input.residualWith_component (D : Input) (a : Coefficients)
    (x : Fin 3 → ℝ) (t : ℝ) (i : Fin 3) :
    value (D.residualWith a i) x t=value (D.baseResidual i) x t+
      (D.K:ℝ)*((value a x t-1)*value (D.coupled i) x t) := by
  simp only [Input.residualWith,value_add,value_scale,value_multiply,value_subtract,
    value_constant,Rat.cast_one]

theorem Input.residual_enclosure (D : Input) (a : Coefficients) (N : ℕ)
    (p : Partition) (q : Fin 3 → Partition)
    (base r : Fin 3 → Fin (N+1) → Coefficients)
    (R : Fin (N+1) → DiskTimePolynomial.Certificate 3)
    (hK : 0≤D.K) {σ : ℚ} (hp : p.Valid σ) (hq : ∀ i, (q i).Valid σ)
    (hr : ∀ i d, zero (subtract
      (add (base i d) (scale D.K (degreeProduct d.val p (q i)))) (r i d)))
    (hR : ∀ d, BallNormProfile.CertificateValid (R d) (fun i => r i d) σ)
    {x : Fin 3 → ℝ} (hx : x 0^2+x 1^2+x 2^2≤(σ:ℝ)^2) {t : ℝ} (ht : 0≤t)
    (hbase : ∀ i, value (assemble (base i)) x t=value (D.baseResidual i) x t)
    (hpvalue : value p.core x t=value a x t-1)
    (hqvalue : ∀ i, value (q i).core x t=value (D.coupled i) x t) :
    enorm (value3 (D.residualWith a) x t)≤
      PolynomialOrder.value
        (PolynomialBounds.add (profileSum fun d => (R d).bound 1)
          (PolynomialBounds.scale D.K (profileSum fun i => discardedProfile N p (q i)))) t := by
  let v : EuclideanSpace ℝ (Fin 3) := DiskPolynomial.vectorValue (D.residualWith a) x t
  let w : EuclideanSpace ℝ (Fin 3) := DiskPolynomial.vectorValue (fun i => assemble (r i)) x t
  have he (i : Fin 3) : |v i-w i|≤
      (D.K:ℝ)*PolynomialOrder.value (discardedProfile N p (q i)) t := by
    have h := affine_error N p (q i) D.K hK (base i) (r i) (hr i) hp (hq i) hx ht
    rw [hbase i,hpvalue,hqvalue i,←D.residualWith_component] at h
    exact h
  have hw := DegreeVectorCertificate.vector_sum_bound (fun d i => r i d) R hR hx ht
  have hv := DegreeVectorCertificate.component_error v w _ he
  change ‖v‖≤_ at ⊢
  rw [PolynomialOrder.value_add,PolynomialOrder.value_scale,
    profileSum_value (fun i => discardedProfile N p (q i)) t,Finset.mul_sum]
  exact hv.trans (add_le_add hw le_rfl)

/-- Charge the previously checked cubic-factor error once, after preserving
the joint gravity multiplier inside its Euclidean norm. -/
theorem Input.full_residual_enclosure (D : Input) (a : Coefficients)
    (x : Fin 3 → ℝ) (t : ℝ) {R ε B : ℝ} (hK : 0≤(D.K:ℝ))
    (hR : enorm (value3 (D.residualWith a) x t)≤R)
    (hc : |(1+value D.h x t)^3-value a x t|≤ε)
    (hB : enorm (value3 D.coupled x t)≤B) :
    enorm (value3 D.residual x t)≤R+(D.K:ℝ)*ε*B := by
  rw [Input.residual,D.residualWith_value,D.cube_value]
  rw [D.residualWith_value] at hR
  have h := LieRadiusFullDefect.cubic_residual_bound (D.K:ℝ) (value D.h x t)
    (value a x t) ε R
    (value3 (PointingCapPolynomial.derivative (PointingCapPolynomial.derivative D.rho)) x t)
    (value3 D.rho x t) x (value3 D.force x t)
    (jacobianInverseQuadratic x (value3 D.reference x t)) hK hc hR
  rw [←D.coupled_value] at h
  exact h.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hB
    (mul_nonneg hK ((abs_nonneg _).trans hc))))

end
end GNC.OrbitalComparison.JointErrorPolynomial
