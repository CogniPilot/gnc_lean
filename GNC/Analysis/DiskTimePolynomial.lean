import GNC.Analysis.DiskPolynomial

/-! Polynomial time profiles for vector residuals on a pointing cap.
Unlike a uniform norm bound, the profile retains when the residual grows.
The decomposition, disk powers and squared-vector bounds are all checked. -/
namespace GNC.DiskTimePolynomial
open DiskPolynomial ParameterPolynomial

structure Curve (n : ℕ) where
  coefficients : DiskPolynomial.Curve n
  bound : List ℚ

def Curve.Valid {n : ℕ} (p : Curve n) : Prop :=
  PolynomialOrder.nonnegative p.bound ∧
    PolynomialOrder.prefixes 0 (PolynomialBounds.subtract
      (PolynomialBounds.multiply p.bound p.bound) (dot p.coefficients p.coefficients))

instance {n : ℕ} (p : Curve n) : Decidable p.Valid := by
  unfold Curve.Valid
  infer_instance

structure Term (n : ℕ) where
  u : ℕ
  v : ℕ
  c : ℕ
  curve : Curve n
  monomialBound : ℚ

def Term.Valid {n : ℕ} (p : Term n) (σ : ℚ) : Prop :=
  p.curve.Valid ∧ 0≤p.monomialBound ∧
    σ^(2*(p.u+p.v))*(p.u:ℚ)^p.u*(p.v:ℚ)^p.v ≤
      p.monomialBound^2*((p.u+p.v:ℕ):ℚ)^(p.u+p.v)

instance {n : ℕ} (p : Term n) (σ : ℚ) : Decidable (p.Valid σ) := by
  unfold Term.Valid
  infer_instance

structure Certificate (n : ℕ) where
  count : ℕ
  terms : Fin count → Term n

def Certificate.polynomial {n : ℕ} (D : Certificate n) : Vector n := fun i =>
  (List.finRange D.count).foldr (fun k p =>
    add (term (D.terms k).curve.coefficients (D.terms k).u
      (D.terms k).v (D.terms k).c i) p) []

def Certificate.bound {n : ℕ} (D : Certificate n) (C : ℚ) : List ℚ :=
  (List.finRange D.count).foldr (fun k p =>
    PolynomialBounds.add (PolynomialBounds.scale
      ((D.terms k).monomialBound*C^(D.terms k).c) (D.terms k).curve.bound) p) []

structure Certificate.Valid {n : ℕ} (D : Certificate n) (p : Vector n) (σ : ℚ) : Prop where
  terms : ∀ k, (D.terms k).Valid σ
  decomposition : ∀ i, zero (subtract (p i) (D.polynomial i))

noncomputable section

theorem Curve.certifies {n : ℕ} (p : Curve n) (hp : p.Valid)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    ‖curveValue p.coefficients t‖≤PolynomialOrder.value p.bound t := by
  have h := PolynomialOrder.prefixes_sound _ hp.2 ht
  rw [PolynomialOrder.value_subtract,DiskPolynomial.value_multiply,
    ← curve_norm_square] at h
  have hb := PolynomialOrder.value_nonnegative _ hp.1 ht.1
  nlinarith [norm_nonneg (curveValue p.coefficients t)]

theorem Certificate.polynomial_value {n : ℕ} (D : Certificate n) (x : Fin 3 → ℝ) (t : ℝ) :
    vectorValue D.polynomial x t =
      ∑ k, (x 0^(D.terms k).u*x 1^(D.terms k).v*x 2^(D.terms k).c) •
        curveValue (D.terms k).curve.coefficients t := by
  have hf (i : Fin n) (l : List (Fin D.count)) :
      value (l.foldr (fun k p => add (term (D.terms k).curve.coefficients
        (D.terms k).u (D.terms k).v (D.terms k).c i) p) []) x t =
      (l.map (fun k => value (term (D.terms k).curve.coefficients
        (D.terms k).u (D.terms k).v (D.terms k).c i) x t)).sum := by
    induction l with
    | nil => rfl
    | cons k l ih => simp only [List.foldr_cons,value_add,ih,List.map_cons,List.sum_cons]
  ext i
  simp only [vectorValue,Certificate.polynomial,PiLp.toLp_apply,hf]
  rw [← List.sum_toFinset _ (List.nodup_finRange D.count),List.toFinset_finRange]
  simp [term,curveValue,value,termValue,monomial,Finset.sum_apply,mul_comm]

theorem Certificate.bound_value {n : ℕ} (D : Certificate n) (C : ℚ) (t : ℝ) :
    PolynomialOrder.value (D.bound C) t =
      ∑ k, ((D.terms k).monomialBound:ℝ)*(C:ℝ)^(D.terms k).c*
        PolynomialOrder.value (D.terms k).curve.bound t := by
  have hf (l : List (Fin D.count)) :
      PolynomialOrder.value (l.foldr (fun k p => PolynomialBounds.add
        (PolynomialBounds.scale ((D.terms k).monomialBound*C^(D.terms k).c)
          (D.terms k).curve.bound) p) []) t =
      (l.map (fun k => ((D.terms k).monomialBound:ℝ)*(C:ℝ)^(D.terms k).c*
        PolynomialOrder.value (D.terms k).curve.bound t)).sum := by
    induction l with
    | nil => rfl
    | cons k l ih => simp only [List.foldr_cons,PolynomialOrder.value_add,
        PolynomialOrder.value_scale,ih,List.map_cons,List.sum_cons,Rat.cast_mul,Rat.cast_pow]
  rw [Certificate.bound,hf]
  rw [← List.sum_toFinset _ (List.nodup_finRange D.count),List.toFinset_finRange]

/-- The profile applies to every real time in the unit interval and
every point of the disk with the stated axial-depth bound. -/
theorem Certificate.certifies {n : ℕ} (D : Certificate n) (p : Vector n) {σ C : ℚ}
    (hD : D.Valid p σ) {x : Fin 3 → ℝ}
    (hx : x 0^2+x 1^2≤(σ:ℝ)^2) (hc : |x 2|≤(C:ℝ))
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) : ‖vectorValue p x t‖≤PolynomialOrder.value (D.bound C) t := by
  have he : vectorValue p x t=vectorValue D.polynomial x t := by
    ext i
    exact identity _ _ (hD.decomposition i) x t
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
  have hC : (0:ℝ)≤C := (abs_nonneg (x 2)).trans hc
  have hm := mul_le_mul hmon hcp (by positivity) hb
  rw [norm_smul,Real.norm_eq_abs,abs_mul,abs_pow]
  exact mul_le_mul hm ((D.terms k).curve.certifies (hD.terms k).1 ht)
    (norm_nonneg _) (mul_nonneg hb (pow_nonneg hC _))

end
end GNC.DiskTimePolynomial
