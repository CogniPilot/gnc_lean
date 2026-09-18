import GNC.Analysis.DiskTimePolynomial

/-! A linear-in-degree range checker for a vector polynomial. Each rational
coefficient vector has a supplied rational upper norm. Checking its squared
norm uses no square roots and does not convolve the whole polynomial with
itself. The soundness theorem covers every nonnegative real time.

This option is shared by Lie and Cartesian certificates. It may be less
sharp than a prefix-square certificate, which remains independently useful.
-/
namespace GNC.CoefficientNormProfile
open DiskPolynomial

def Valid {n : ℕ} (p : Curve n) : List ℚ → Prop
  | [] => ∀ i, p i=[]
  | b::bs => 0≤b ∧ (∑ i, ((p i).headD 0)^2)≤b^2 ∧ Valid (fun i => (p i).tail) bs

instance {n : ℕ} (p : Curve n) (b : List ℚ) : Decidable (Valid p b) := by
  induction b generalizing p with
  | nil => unfold Valid; infer_instance
  | cons b bs ih =>
    letI := ih (fun i => (p i).tail)
    unfold Valid
    infer_instance

def TermValid {n : ℕ} (p : DiskTimePolynomial.Term n) (σ : ℚ) : Prop :=
  Valid p.curve.coefficients p.curve.bound ∧ 0≤p.monomialBound ∧
    σ^(2*(p.u+p.v))*(p.u:ℚ)^p.u*(p.v:ℚ)^p.v ≤
      p.monomialBound^2*((p.u+p.v:ℕ):ℚ)^(p.u+p.v)

instance {n : ℕ} (p : DiskTimePolynomial.Term n) (σ : ℚ) : Decidable (TermValid p σ) := by
  unfold TermValid
  infer_instance

structure CertificateValid {n : ℕ} (D : DiskTimePolynomial.Certificate n)
    (p : Vector n) (σ : ℚ) : Prop where
  terms : ∀ k, TermValid (D.terms k) σ
  decomposition : ∀ i, ParameterPolynomial.zero
    (ParameterPolynomial.subtract (p i) (D.polynomial i))

noncomputable section

theorem sound {n : ℕ} (p : Curve n) (b : List ℚ) (h : Valid p b)
    {t : ℝ} (ht : 0≤t) : ‖curveValue p t‖≤PolynomialOrder.value b t := by
  induction b generalizing p with
  | nil =>
    have he : curveValue p t=0 := by
      ext i
      simp only [curveValue,PiLp.toLp_apply,PiLp.zero_apply,h i]
      rfl
    rw [he,norm_zero]
    exact le_rfl
  | cons a b ih =>
    let c : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun i => ((p i).headD 0:ℝ))
    have hnorm : ‖c‖≤(a:ℝ) := by
      have ha : (0:ℝ)≤a := by exact_mod_cast h.1
      have hs : (∑ i, (((p i).headD 0:ℚ):ℝ)^2)≤(a:ℝ)^2 := by exact_mod_cast h.2.1
      have he : ‖c‖^2=∑ i, (((p i).headD 0:ℚ):ℝ)^2 := by
        rw [EuclideanSpace.real_norm_sq_eq]
      nlinarith [norm_nonneg c]
    have he : curveValue p t=c+t • curveValue (fun i => (p i).tail) t := by
      ext i
      change PolynomialOrder.value (p i) t=((p i).headD 0:ℝ)+t*PolynomialOrder.value (p i).tail t
      cases p i <;> simp [PolynomialOrder.value,Planning.PolynomialKernel.evaluate]
    rw [he]
    have hb := ih _ h.2.2
    have hm : ‖t • curveValue (fun i => (p i).tail) t‖≤t*PolynomialOrder.value b t := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht]
      exact mul_le_mul_of_nonneg_left hb ht
    exact (norm_add_le _ _).trans (add_le_add hnorm hm)

theorem nonnegative {n : ℕ} (p : Curve n) (b : List ℚ) (h : Valid p b) :
    PolynomialOrder.nonnegative b := by
  induction b generalizing p with
  | nil => intro a ha; simp at ha
  | cons a b ih =>
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact h.1
    · exact ih _ h.2.2 c hc

/-- Retain the known quadratic growth of a candidate without introducing
a constant-in-time worst case. The zeros are checked coefficient data. -/
theorem quadratic_bound {n : ℕ} (p : Curve n) (b : List ℚ) (h : Valid p b)
    (hz : b=0::0::b.drop 2) {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    ‖curveValue p t‖≤t^2*PolynomialOrder.value b 1 :=
  (sound p b h ht.1).trans (PolynomialOrder.quadratic_time_bound b (nonnegative p b h) hz ht)

/-- The alternative checker uses the same residual decomposition and
disk monomial bounds as the prefix-square checker. Only the vector-curve
norm test changes; it applies equally to every predictor representation. -/
theorem certifies {n : ℕ} (D : DiskTimePolynomial.Certificate n) (p : Vector n) {σ C : ℚ}
    (hD : CertificateValid D p σ) {x : Fin 3 → ℝ}
    (hx : x 0^2+x 1^2≤(σ:ℝ)^2) (hc : |x 2|≤(C:ℝ))
    {t : ℝ} (ht : 0≤t) : ‖vectorValue p x t‖≤PolynomialOrder.value (D.bound C) t := by
  have he : vectorValue p x t=vectorValue D.polynomial x t := by
    ext i
    exact ParameterPolynomial.identity _ _ (hD.decomposition i) x t
  rw [he,D.polynomial_value,D.bound_value]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro k _
  have hmon := DiskMonomial.certifies
    (show (0:ℝ)≤(D.terms k).monomialBound by exact_mod_cast (hD.terms k).2.1)
    hx (D.terms k).u (D.terms k).v
    (by exact_mod_cast (hD.terms k).2.2)
  have hcp := pow_le_pow_left₀ (abs_nonneg (x 2)) hc (D.terms k).c
  have hb : (0:ℝ)≤(D.terms k).monomialBound := by exact_mod_cast (hD.terms k).2.1
  have hC : (0:ℝ)≤C := (abs_nonneg _).trans hc
  have hm := mul_le_mul hmon hcp (by positivity) hb
  rw [norm_smul,Real.norm_eq_abs,abs_mul,abs_pow]
  exact mul_le_mul hm (sound _ _ (hD.terms k).1 ht)
    (norm_nonneg _) (mul_nonneg hb (pow_nonneg hC _))

end
end GNC.CoefficientNormProfile
