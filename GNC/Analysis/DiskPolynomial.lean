import GNC.Analysis.DiskMonomial
import GNC.Analysis.ParameterPolynomial
import GNC.Analysis.HomogeneousPolynomial
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Exact certificates for vector parameter polynomials on a disk.
The coefficient decomposition, orthogonality and norm bounds are all checked.
The output dimension is arbitrary; the three parameters are two disk
coordinates and one separately bounded scalar. -/
namespace GNC.DiskPolynomial
open scoped BigOperators
open ParameterPolynomial

abbrev Curve (n : ℕ) := Fin n → List ℚ
abbrev Vector (n : ℕ) := Fin n → Coefficients

def dot {n : ℕ} (p q : Curve n) : List ℚ :=
  (List.finRange n).foldr (fun i s =>
    PolynomialBounds.add (PolynomialBounds.multiply (p i) (q i)) s) []

structure CurveCertificate (n : ℕ) where
  coefficients : Curve n
  bound : ℚ

def CurveCertificate.Valid {n : ℕ} (p : CurveCertificate n) : Prop :=
  0≤p.bound ∧ PolynomialOrder.nonnegative (HomogeneousPolynomial.lift
    (PolynomialBounds.subtract [p.bound^2] (dot p.coefficients p.coefficients)))

instance {n : ℕ} (p : CurveCertificate n) : Decidable p.Valid := by
  unfold CurveCertificate.Valid
  infer_instance

structure TermCertificate (n : ℕ) where
  u : ℕ
  v : ℕ
  c : ℕ
  curve : CurveCertificate n
  monomialBound : ℚ

def TermCertificate.Valid {n : ℕ} (a : TermCertificate n) (σ : ℚ) : Prop :=
  a.curve.Valid ∧ 0≤a.monomialBound ∧
    σ^(2*(a.u+a.v))*(a.u:ℚ)^a.u*(a.v:ℚ)^a.v≤
      a.monomialBound^2*((a.u+a.v:ℕ):ℚ)^(a.u+a.v)

instance {n : ℕ} (a : TermCertificate n) (σ : ℚ) : Decidable (a.Valid σ) := by
  unfold TermCertificate.Valid
  infer_instance

def term {n : ℕ} (p : Curve n) (u v c : ℕ) : Vector n :=
  fun i => [⟨u,v,c,p i⟩]

structure Certificate (n : ℕ) where
  left : CurveCertificate n
  right : CurveCertificate n
  count : ℕ
  higher : Fin count → TermCertificate n

def Certificate.polynomial {n : ℕ} (D : Certificate n) : Vector n := fun i =>
  add (term D.left.coefficients 1 0 0 i)
    (add (term D.right.coefficients 0 1 0 i)
      ((List.finRange D.count).foldr (fun k p =>
        add (term (D.higher k).curve.coefficients (D.higher k).u
          (D.higher k).v (D.higher k).c i) p) []))

def Certificate.bound {n : ℕ} (D : Certificate n) (σ C : ℚ) : ℚ :=
  σ*max D.left.bound D.right.bound+
    ∑ k, (D.higher k).monomialBound*C^(D.higher k).c*(D.higher k).curve.bound

structure Certificate.Valid {n : ℕ} (D : Certificate n) (p : Vector n) (σ C B : ℚ) : Prop where
  left : D.left.Valid
  right : D.right.Valid
  orthogonal : BernsteinPolynomial.zero (dot D.left.coefficients D.right.coefficients)
  higher : ∀ k, (D.higher k).Valid σ
  decomposition : ∀ i, zero (subtract (p i) (D.polynomial i))
  bound : D.bound σ C≤B

noncomputable section

def curveValue {n : ℕ} (p : Curve n) (t : ℝ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => PolynomialOrder.value (p i) t)

def vectorValue {n : ℕ} (p : Vector n) (x : Fin 3 → ℝ) (t : ℝ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => value (p i) x t)

theorem value_multiply (p q : List ℚ) (t : ℝ) :
    PolynomialOrder.value (PolynomialBounds.multiply p q) t=
      PolynomialOrder.value p t*PolynomialOrder.value q t := by
  simp only [PolynomialOrder.value,PolynomialBounds.multiply_map,PolynomialBounds.evaluate_multiply]

theorem zero_value (p : List ℚ) (h : BernsteinPolynomial.zero p) (t : ℝ) :
    PolynomialOrder.value p t=0 := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    have ha := h a (by simp)
    have hp := ih (fun b hb => h b (by simp [hb]))
    change (a:ℝ)+t*PolynomialOrder.value p t=0
    simp [ha,hp]

theorem dot_value {n : ℕ} (p q : Curve n) (t : ℝ) :
    PolynomialOrder.value (dot p q) t=inner ℝ (curveValue p t) (curveValue q t) := by
  have hf (l : List (Fin n)) :
      PolynomialOrder.value (l.foldr (fun i s =>
        PolynomialBounds.add (PolynomialBounds.multiply (p i) (q i)) s) []) t=
      (l.map (fun i => PolynomialOrder.value (p i) t*PolynomialOrder.value (q i) t)).sum := by
    induction l with
    | nil => rfl
    | cons i l ih => simp only [List.foldr_cons,PolynomialOrder.value_add,value_multiply,ih,List.map_cons,List.sum_cons]
  rw [dot,hf]
  rw [← List.sum_toFinset _ (List.nodup_finRange n),List.toFinset_finRange]
  simp only [curveValue,PiLp.inner_apply]
  change (∑ i, PolynomialOrder.value (p i) t*PolynomialOrder.value (q i) t)=
    ∑ i, PolynomialOrder.value (q i) t*PolynomialOrder.value (p i) t
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

theorem curve_norm_square {n : ℕ} (p : Curve n) (t : ℝ) :
    ‖curveValue p t‖^2=PolynomialOrder.value (dot p p) t := by
  rw [dot_value,real_inner_self_eq_norm_sq]

theorem CurveCertificate.certifies {n : ℕ} (p : CurveCertificate n) (hp : p.Valid)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) : ‖curveValue p.coefficients t‖≤(p.bound:ℝ) := by
  rcases hp with ⟨hB,hp⟩
  have h := HomogeneousPolynomial.certifies _ hp ht
  rw [PolynomialOrder.value_subtract,← curve_norm_square] at h
  have he : PolynomialOrder.value [p.bound^2] t=(p.bound:ℝ)^2 := by
    simp [PolynomialOrder.value,Planning.PolynomialKernel.evaluate]
  rw [he] at h
  have hb : (0:ℝ)≤p.bound := by exact_mod_cast hB
  nlinarith [norm_nonneg (curveValue p.coefficients t)]

theorem term_value {n : ℕ} (p : Curve n) (u v c : ℕ) (x : Fin 3 → ℝ) (t : ℝ) :
    vectorValue (term p u v c) x t=(x 0^u*x 1^v*x 2^c) • curveValue p t := by
  ext i
  simp [vectorValue,term,curveValue,value,termValue,monomial,mul_comm]

theorem Certificate.polynomial_value {n : ℕ} (D : Certificate n) (x : Fin 3 → ℝ) (t : ℝ) :
    vectorValue D.polynomial x t=x 0 • curveValue D.left.coefficients t+
      x 1 • curveValue D.right.coefficients t+
      ∑ k, (x 0^(D.higher k).u*x 1^(D.higher k).v*x 2^(D.higher k).c) •
        curveValue (D.higher k).curve.coefficients t := by
  have hf (i : Fin n) (l : List (Fin D.count)) :
      value (l.foldr (fun k p => add (term (D.higher k).curve.coefficients
        (D.higher k).u (D.higher k).v (D.higher k).c i) p) []) x t=
      (l.map (fun k => value (term (D.higher k).curve.coefficients
        (D.higher k).u (D.higher k).v (D.higher k).c i) x t)).sum := by
    induction l with
    | nil => rfl
    | cons k l ih => simp only [List.foldr_cons,value_add,ih,List.map_cons,List.sum_cons]
  ext i
  simp only [vectorValue,Certificate.polynomial,PiLp.toLp_apply,value_add,hf]
  rw [← List.sum_toFinset _ (List.nodup_finRange D.count),List.toFinset_finRange]
  simp [term,curveValue,value,termValue,monomial,Finset.sum_apply,PiLp.add_apply,PiLp.smul_apply,mul_comm,add_assoc]

/-- The certificate checks the complete vector polynomial, rather than
assuming that an external grouping of its coefficients is correct. -/
theorem Certificate.certifies {n : ℕ} (D : Certificate n) (p : Vector n) {σ C B : ℚ}
    (hD : D.Valid p σ C B) (hσ : 0≤σ) {x : Fin 3 → ℝ}
    (hx : x 0^2+x 1^2≤(σ:ℝ)^2) (hc : |x 2|≤(C:ℝ))
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) : ‖vectorValue p x t‖≤(B:ℝ) := by
  have he : vectorValue p x t=vectorValue D.polynomial x t := by
    ext i
    exact identity _ _ (hD.decomposition i) x t
  rw [he,D.polynomial_value]
  have hL : (0:ℝ)≤max (D.left.bound:ℝ) (D.right.bound:ℝ) :=
    (show (0:ℝ)≤D.left.bound by exact_mod_cast hD.left.1).trans (le_max_left _ _)
  have hleft := (D.left.certifies hD.left ht).trans (le_max_left (D.left.bound:ℝ) (D.right.bound:ℝ))
  have hright := (D.right.certifies hD.right ht).trans (le_max_right (D.left.bound:ℝ) (D.right.bound:ℝ))
  have horth : inner ℝ (curveValue D.left.coefficients t) (curveValue D.right.coefficients t)=0 := by
    rw [← dot_value]
    exact zero_value _ hD.orthogonal t
  have h := DiskMonomial.family_bound Finset.univ
    (fun k => (D.higher k).u) (fun k => (D.higher k).v) (fun k => (D.higher k).c)
    (fun k => curveValue (D.higher k).curve.coefficients t)
    (fun k => ((D.higher k).monomialBound:ℝ)) (fun k => ((D.higher k).curve.bound:ℝ))
    (show (0:ℝ)≤σ by exact_mod_cast hσ) hL hx hc hleft hright horth
    (fun k _ => by dsimp only; exact_mod_cast (hD.higher k).2.1)
    (fun k _ => (D.higher k).curve.certifies (hD.higher k).1 ht)
    (fun k _ => by dsimp only; exact_mod_cast (hD.higher k).2.2)
  have hb : (D.bound σ C:ℝ)≤(B:ℝ) := by exact_mod_cast hD.bound
  apply h.trans
  simpa [Certificate.bound] using hb

end
end GNC.DiskPolynomial
