import GNC.Analysis.PolynomialTranslation
import GNC.Control.PointingAffine

/-! Continuous norm certificates for polynomial affine pointing responses.
The finite rational checks cover every real time in the declared interval
and every direction in the common cap. A separate approximation theorem
must relate the polynomial response to an actual dynamical trajectory.
-/
namespace GNC.PolynomialAffine
open Matrix Planning.PolynomialKernel PolynomialBounds PolynomialTranslation ThrustSupport

abbrev VectorPolynomial := Fin 3 → List ℚ

noncomputable def value (p : VectorPolynomial) (t : ℝ) : Vec3 :=
  fun i => evaluate ((p i).map (Rat.castHom ℝ)) t

def plus (a b : VectorPolynomial) : VectorPolynomial := fun i => add (a i) (b i)

def pairing (a b : VectorPolynomial) : List ℚ :=
  add (add (multiply (a 0) (b 0)) (multiply (a 1) (b 1))) (multiply (a 2) (b 2))

theorem value_plus (a b : VectorPolynomial) (t : ℝ) :
    value (plus a b) t = value a t+value b t := by
  ext i
  change evaluate ((add (a i) (b i)).map (Rat.castHom ℝ)) t =
    evaluate ((a i).map (Rat.castHom ℝ)) t+evaluate ((b i).map (Rat.castHom ℝ)) t
  rw [add_map, evaluate_add]

theorem pairing_value (a b : VectorPolynomial) (t : ℝ) :
    evaluate ((pairing a b).map (Rat.castHom ℝ)) t = value a t ⬝ᵥ value b t := by
  simp only [pairing, add_map, multiply_map, evaluate_add, evaluate_multiply]
  simp [value, dotProduct, Fin.sum_univ_succ, add_assoc]

/-- Nominal energy, three cross terms, transverse and axial column energies. -/
def statistics (p a b c : VectorPolynomial) : Fin 6 → List ℚ :=
  ![pairing p p, pairing p a, pairing p b, pairing p c,
    add (pairing a a) (pairing b b), pairing c c]

theorem statistics_value (p a b c : VectorPolynomial) (t : ℝ) :
    (fun i => evaluate ((statistics p a b c i).map (Rat.castHom ℝ)) t) =
      ![enorm (value p t)^2, value p t ⬝ᵥ value a t, value p t ⬝ᵥ value b t,
        value p t ⬝ᵥ value c t, enorm (value a t)^2+enorm (value b t)^2,
        enorm (value c t)^2] := by
  ext i
  fin_cases i
  · change evaluate ((pairing p p).map (Rat.castHom ℝ)) t = enorm (value p t)^2
    rw [pairing_value, dot_self_lengthSq, enorm_sq]
  · exact pairing_value p a t
  · exact pairing_value p b t
  · exact pairing_value p c t
  · change evaluate ((add (pairing a a) (pairing b b)).map (Rat.castHom ℝ)) t =
      enorm (value a t)^2+enorm (value b t)^2
    rw [add_map, evaluate_add, pairing_value, pairing_value,
      dot_self_lengthSq, dot_self_lengthSq, enorm_sq, enorm_sq]
  · change evaluate ((pairing c c).map (Rat.castHom ℝ)) t = enorm (value c t)^2
    rw [pairing_value, dot_self_lengthSq, enorm_sq]

structure Certificate where
  center : ℚ
  radius : ℚ
  rho : ℚ
  eta : ℚ
  bounds : Fin 6 → ℚ
  crossRadius : ℚ
  transverseRadius : ℚ
  axialRadius : ℚ
  resultRadius : ℚ

def Certificate.Valid (s : Certificate) (κ : ℚ) (p a b c : VectorPolynomial) : Prop :=
  0 ≤ κ ∧ 0 ≤ s.rho ∧ 1-κ^2 ≤ s.rho^2 ∧ 1-κ ≤ s.eta ∧
  0 ≤ s.crossRadius ∧ (s.bounds 1)^2+(s.bounds 2)^2 ≤ s.crossRadius^2 ∧
  0 ≤ s.transverseRadius ∧ s.bounds 4 ≤ s.transverseRadius^2 ∧
  0 ≤ s.axialRadius ∧ s.bounds 5 ≤ s.axialRadius^2 ∧
  0 ≤ s.resultRadius ∧
  s.bounds 0+2*(s.rho*s.crossRadius+s.eta*s.bounds 3)+
    (s.rho*s.transverseRadius+s.eta*s.axialRadius)^2 ≤ s.resultRadius^2 ∧
  ∀ i, bound (translate s.center (statistics p a b c i)) s.radius ≤ s.bounds i

instance (s : Certificate) (κ : ℚ) (p a b c : VectorPolynomial) :
    Decidable (s.Valid κ p a b c) := by unfold Certificate.Valid; infer_instance

/-- Soundness of the executable rational certificate, for an arbitrary real
time and unit direction. This is stronger than checking time/cap samples. -/
theorem certificate_sound (s : Certificate) (κ : ℚ) (p a b c : VectorPolynomial)
    (hs : s.Valid κ p a b c) {t : ℝ} (ht : |t-(s.center:ℝ)| ≤ (s.radius:ℝ))
    (q : Vec3) (hq : q ∈ Cap pointingAxis (κ:ℝ)) :
    enorm (value p t+q 0 • value a t+q 1 • value b t+(q 2-1) • value c t) ≤
      (s.resultRadius:ℝ) := by
  obtain ⟨hκ,hρ,hρsq,hη,hH,hHs,hF,hFs,hG,hGs,hR,hbudget,hcheck⟩ := hs
  let v : Fin 6 → ℝ := ![enorm (value p t)^2, value p t ⬝ᵥ value a t,
    value p t ⬝ᵥ value b t, value p t ⬝ᵥ value c t,
    enorm (value a t)^2+enorm (value b t)^2, enorm (value c t)^2]
  have hval (i : Fin 6) : |v i| ≤ (s.bounds i:ℝ) := by
    have he := congrFun (statistics_value p a b c t) i
    have hb := (centered_bound (statistics p a b c i) s.center s.radius ht).trans
      (show ((bound (translate s.center (statistics p a b c i)) s.radius:ℚ):ℝ) ≤
          (s.bounds i:ℝ) by exact_mod_cast hcheck i)
    simpa only [he] using hb
  have hv (i : Fin 6) : v i ≤ (s.bounds i:ℝ) := (le_abs_self _).trans (hval i)
  have hv2 (i : Fin 6) : (v i)^2 ≤ (s.bounds i:ℝ)^2 := by
    obtain ⟨hl,hu⟩ := abs_le.mp (hval i)
    nlinarith [mul_nonneg (show 0 ≤ (s.bounds i:ℝ)+v i by linarith)
      (show 0 ≤ (s.bounds i:ℝ)-v i by linarith)]
  apply cap_affine_norm_le (value p t) (value a t) (value b t) (value c t) q
    (κ := (κ:ℝ)) (ρ := (s.rho:ℝ)) (η := (s.eta:ℝ)) (N := (s.bounds 0:ℝ))
    (H := (s.crossRadius:ℝ)) (C := (s.bounds 3:ℝ)) (F := (s.transverseRadius:ℝ))
    (G := (s.axialRadius:ℝ)) (R := (s.resultRadius:ℝ))
    hq (by exact_mod_cast hκ) (by exact_mod_cast hρ) (by exact_mod_cast hρsq)
    (by exact_mod_cast hη) (hv 0) (by exact_mod_cast hH) ?_ (hval 3)
    (by exact_mod_cast hF) ?_ ?_ (by exact_mod_cast hR) (by exact_mod_cast hbudget)
  · have hh : (s.bounds 1:ℝ)^2+(s.bounds 2:ℝ)^2 ≤ (s.crossRadius:ℝ)^2 := by
      exact_mod_cast hHs
    exact (add_le_add (hv2 1) (hv2 2)).trans hh
  · exact (hv 4).trans (by exact_mod_cast hFs)
  · have hh : (s.bounds 5:ℝ) ≤ (s.axialRadius:ℝ)^2 := by exact_mod_cast hGs
    have hn : (0:ℝ) ≤ (s.axialRadius:ℝ) := by exact_mod_cast hG
    have hx := (hv 5).trans hh
    change enorm (value c t)^2 ≤ (s.axialRadius:ℝ)^2 at hx
    nlinarith [enorm_nonneg (value c t)]

/-- Four stored affine columns use `free + c` as the nominal response. -/
theorem affine_certificate_sound (s : Certificate) (κ : ℚ)
    (free a b c : VectorPolynomial) (hs : s.Valid κ (plus free c) a b c)
    {t : ℝ} (ht : |t-(s.center:ℝ)| ≤ (s.radius:ℝ))
    (q : Vec3) (hq : q ∈ Cap pointingAxis (κ:ℝ)) :
    enorm (value free t+q 0 • value a t+q 1 • value b t+q 2 • value c t) ≤
      (s.resultRadius:ℝ) := by
  have h := certificate_sound s κ (plus free c) a b c hs ht q hq
  rw [value_plus] at h
  have he : value free t+value c t+q 0 • value a t+q 1 • value b t+
      (q 2-1) • value c t =
      value free t+q 0 • value a t+q 1 • value b t+q 2 • value c t := by
    rw [sub_smul, one_smul]
    abel
  rwa [he] at h

end GNC.PolynomialAffine
