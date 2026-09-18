import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Simplex moments for the Magnus expansion of the linear generator
(Appendix B of main.pdf), together with the ordered double integrals
used in Lemma 1 and Proposition 6 and the direct integral evaluation of
the -1/240 coefficient of Lemma 3 (Remark 2) and the 1/360 coefficient
of Proposition 6.

All integrals are iterated real interval integrals of polynomials over
the ordered simplices 0 < t2 < t1 < T and 0 < t3 < t2 < t1 < T. -/
noncomputable section
namespace GNC.Magnus
open intervalIntegral MeasureTheory

/-! ### Polynomial interval integrals -/

/-- Integral of a monomial from 0 to `b`. -/
theorem integral_monomial (b c : ℝ) (n : ℕ) :
    ∫ x in (0:ℝ)..b, c * x ^ n = c * b ^ (n + 1) / ((n : ℝ) + 1) := by
  rw [intervalIntegral.integral_const_mul, integral_pow, zero_pow (Nat.succ_ne_zero n), sub_zero]
  ring

/-- Integral from 0 to `b` of a polynomial of degree at most four, given by an
identity for the integrand; the coefficients may depend on outer variables. -/
theorem integral_of_poly {f : ℝ → ℝ} (b c0 c1 c2 c3 c4 : ℝ)
    (hf : ∀ x, f x = c0 + c1 * x + c2 * x ^ 2 + c3 * x ^ 3 + c4 * x ^ 4) :
    ∫ x in (0:ℝ)..b, f x =
      c0 * b + c1 * b ^ 2 / 2 + c2 * b ^ 3 / 3 + c3 * b ^ 4 / 4 + c4 * b ^ 5 / 5 := by
  have e : f = fun x => c0 * x ^ 0 + c1 * x ^ 1 + c2 * x ^ 2 + c3 * x ^ 3 + c4 * x ^ 4 := by
    funext x; rw [hf]; ring
  subst e
  rw [integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _),
    integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _),
    integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _),
    integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
  simp only [integral_monomial]
  push_cast
  ring

/-! ### Ordered simplex integrals -/

/-- Ordered double integral over the simplex 0 < t2 < t1 < T. -/
def simplex2 (T : ℝ) (f : ℝ → ℝ → ℝ) : ℝ :=
  ∫ t1 in (0:ℝ)..T, ∫ t2 in (0:ℝ)..t1, f t1 t2

/-- Ordered triple integral over the simplex 0 < t3 < t2 < t1 < T. -/
def simplex3 (T : ℝ) (f : ℝ → ℝ → ℝ → ℝ) : ℝ :=
  ∫ t1 in (0:ℝ)..T, ∫ t2 in (0:ℝ)..t1, ∫ t3 in (0:ℝ)..t2, f t1 t2 t3

/-- Evaluation of a double simplex integral from its two iterated integrals. -/
theorem simplex2_eq (T : ℝ) (f : ℝ → ℝ → ℝ) (g : ℝ → ℝ) (v : ℝ)
    (h2 : ∀ t1, (∫ t2 in (0:ℝ)..t1, f t1 t2) = g t1)
    (h1 : (∫ t1 in (0:ℝ)..T, g t1) = v) : simplex2 T f = v := by
  unfold simplex2
  simp only [h2]
  exact h1

/-- Evaluation of a triple simplex integral from its three iterated integrals. -/
theorem simplex3_eq (T : ℝ) (f : ℝ → ℝ → ℝ → ℝ) (g : ℝ → ℝ → ℝ) (h : ℝ → ℝ) (v : ℝ)
    (h3 : ∀ t1 t2, (∫ t3 in (0:ℝ)..t2, f t1 t2 t3) = g t1 t2)
    (h2 : ∀ t1, (∫ t2 in (0:ℝ)..t1, g t1 t2) = h t1)
    (h1 : (∫ t1 in (0:ℝ)..T, h t1) = v) : simplex3 T f = v := by
  unfold simplex3
  simp only [h3, h2]
  exact h1

/-! ### Double integrals (Lemma 1 and Proposition 6) -/

/-- Lemma 1: the left-convention pairwise commutator weight
`∫_0^T ∫_0^{t1} (t2 - t1) = -T^3/6`. -/
theorem simplex2_sub_rev (T : ℝ) :
    simplex2 T (fun t1 t2 => t2 - t1) = -T ^ 3 / 6 :=
  simplex2_eq T _ (fun t1 => -t1 ^ 2 / 2) _
    (fun t1 => by rw [integral_of_poly t1 (-t1) 1 0 0 0 (fun x => by ring)]; ring)
    (by rw [integral_of_poly T 0 0 (-1 / 2) 0 0 (fun x => by ring)]; ring)

/-- Proposition 6: `∫_0^T ∫_0^{t1} (t1 - t2) = T^3/6`, the `[A, B]` double integral. -/
theorem simplex2_sub (T : ℝ) :
    simplex2 T (fun t1 t2 => t1 - t2) = T ^ 3 / 6 :=
  simplex2_eq T _ (fun t1 => t1 ^ 2 / 2) _
    (fun t1 => by rw [integral_of_poly t1 t1 (-1) 0 0 0 (fun x => by ring)]; ring)
    (by rw [integral_of_poly T 0 0 (1 / 2) 0 0 (fun x => by ring)]; ring)

/-- Proposition 6: `∫_0^T ∫_0^{t1} (t1^2 - t2^2) = T^4/6`, the `[A, C]` double integral. -/
theorem simplex2_sq_sub (T : ℝ) :
    simplex2 T (fun t1 t2 => t1 ^ 2 - t2 ^ 2) = T ^ 4 / 6 :=
  simplex2_eq T _ (fun t1 => 2 * t1 ^ 3 / 3) _
    (fun t1 => by rw [integral_of_poly t1 (t1 ^ 2) 0 (-1) 0 0 (fun x => by ring)]; ring)
    (by rw [integral_of_poly T 0 0 0 (2 / 3) 0 (fun x => by ring)]; ring)

/-- Proposition 6: `∫_0^T ∫_0^{t1} t1 t2 (t1 - t2) = T^5/30`, the `[B, C]` double integral. -/
theorem simplex2_mul_sub (T : ℝ) :
    simplex2 T (fun t1 t2 => t1 * t2 * (t1 - t2)) = T ^ 5 / 30 :=
  simplex2_eq T _ (fun t1 => t1 ^ 4 / 6) _
    (fun t1 => by rw [integral_of_poly t1 0 (t1 ^ 2) (-t1) 0 0 (fun x => by ring)]; ring)
    (by rw [integral_of_poly T 0 0 0 0 (1 / 6) (fun x => by ring)]; ring)

/-- Lemma 1: the second Magnus term of the left-composed flow carries
`(1/2) ∫∫ (t2 - t1) = -T^3/12` on `[N0, N1]`. -/
theorem lemma1_left_coefficient (T : ℝ) :
    (1 / 2 : ℝ) * simplex2 T (fun t1 t2 => t2 - t1) = -T ^ 3 / 12 := by
  rw [simplex2_sub_rev]; ring

/-- Lemma 1: the right-composed flow carries `+T^3/12` on `[N0, N1]`, the
negative of the left-convention coefficient. -/
theorem lemma1_right_coefficient (T : ℝ) :
    -((1 / 2 : ℝ) * simplex2 T (fun t1 t2 => t2 - t1)) = T ^ 3 / 12 := by
  rw [simplex2_sub_rev]; ring

/-- Proposition 6, Eq. (32): halving the three ordered double integrals gives the
pairwise coefficients `h^3/12` on `[A, B]`, `h^4/12` on `[A, C]`, `h^5/60` on `[B, C]`. -/
theorem prop6_pairwise_coefficients (h : ℝ) :
    (1 / 2 : ℝ) * simplex2 h (fun t1 t2 => t1 - t2) = h ^ 3 / 12 ∧
    (1 / 2 : ℝ) * simplex2 h (fun t1 t2 => t1 ^ 2 - t2 ^ 2) = h ^ 4 / 12 ∧
    (1 / 2 : ℝ) * simplex2 h (fun t1 t2 => t1 * t2 * (t1 - t2)) = h ^ 5 / 60 := by
  rw [simplex2_sub, simplex2_sq_sub, simplex2_mul_sub]
  refine ⟨?_, ?_, ?_⟩ <;> ring

/-! ### Appendix B: first moments over 0 < t3 < t2 < t1 < T -/

/-- Appendix B: `∫ t1 = T^4/8`. -/
theorem simplex3_t1 (T : ℝ) : simplex3 T (fun t1 _ _ => t1) = T ^ 4 / 8 :=
  simplex3_eq T _ (fun t1 t2 => t1 * t2) (fun t1 => t1 ^ 3 / 2) _
    (fun t1 t2 => by rw [integral_of_poly t2 t1 0 0 0 0 (fun x => by ring)]; ring)
    (fun t1 => by rw [integral_of_poly t1 0 t1 0 0 0 (fun x => by ring)]; ring)
    (by rw [integral_of_poly T 0 0 0 (1 / 2) 0 (fun x => by ring)]; ring)

/-- Appendix B: `∫ t2 = T^4/12`. -/
theorem simplex3_t2 (T : ℝ) : simplex3 T (fun _ t2 _ => t2) = T ^ 4 / 12 :=
  simplex3_eq T _ (fun _ t2 => t2 ^ 2) (fun t1 => t1 ^ 3 / 3) _
    (fun _ t2 => by rw [integral_of_poly t2 t2 0 0 0 0 (fun x => by ring)]; ring)
    (fun t1 => by rw [integral_of_poly t1 0 0 1 0 0 (fun x => by ring)]; ring)
    (by rw [integral_of_poly T 0 0 0 (1 / 3) 0 (fun x => by ring)]; ring)

/-- Appendix B: `∫ t3 = T^4/24`. -/
theorem simplex3_t3 (T : ℝ) : simplex3 T (fun _ _ t3 => t3) = T ^ 4 / 24 :=
  simplex3_eq T _ (fun _ t2 => t2 ^ 2 / 2) (fun t1 => t1 ^ 3 / 6) _
    (fun _ t2 => by rw [integral_of_poly t2 0 1 0 0 0 (fun x => by ring)]; ring)
    (fun t1 => by rw [integral_of_poly t1 0 0 (1 / 2) 0 0 (fun x => by ring)]; ring)
    (by rw [integral_of_poly T 0 0 0 (1 / 6) 0 (fun x => by ring)]; ring)

/-! ### Appendix B: second moments -/

/-- Appendix B: `∫ t1 t2 = T^5/15`. -/
theorem simplex3_t1_t2 (T : ℝ) : simplex3 T (fun t1 t2 _ => t1 * t2) = T ^ 5 / 15 :=
  simplex3_eq T _ (fun t1 t2 => t1 * t2 ^ 2) (fun t1 => t1 ^ 4 / 3) _
    (fun t1 t2 => by rw [integral_of_poly t2 (t1 * t2) 0 0 0 0 (fun x => by ring)]; ring)
    (fun t1 => by rw [integral_of_poly t1 0 0 t1 0 0 (fun x => by ring)]; ring)
    (by rw [integral_of_poly T 0 0 0 0 (1 / 3) (fun x => by ring)]; ring)

/-- Appendix B: `∫ t1 t3 = T^5/30`. -/
theorem simplex3_t1_t3 (T : ℝ) : simplex3 T (fun t1 _ t3 => t1 * t3) = T ^ 5 / 30 :=
  simplex3_eq T _ (fun t1 t2 => t1 * t2 ^ 2 / 2) (fun t1 => t1 ^ 4 / 6) _
    (fun t1 t2 => by rw [integral_of_poly t2 0 t1 0 0 0 (fun x => by ring)]; ring)
    (fun t1 => by rw [integral_of_poly t1 0 0 (t1 / 2) 0 0 (fun x => by ring)]; ring)
    (by rw [integral_of_poly T 0 0 0 0 (1 / 6) (fun x => by ring)]; ring)

/-- Appendix B: `∫ t2 t3 = T^5/40`. -/
theorem simplex3_t2_t3 (T : ℝ) : simplex3 T (fun _ t2 t3 => t2 * t3) = T ^ 5 / 40 :=
  simplex3_eq T _ (fun _ t2 => t2 ^ 3 / 2) (fun t1 => t1 ^ 4 / 8) _
    (fun _ t2 => by rw [integral_of_poly t2 0 t2 0 0 0 (fun x => by ring)]; ring)
    (fun t1 => by rw [integral_of_poly t1 0 0 0 (1 / 2) 0 (fun x => by ring)]; ring)
    (by rw [integral_of_poly T 0 0 0 0 (1 / 8) (fun x => by ring)]; ring)

/-- Proposition 6 proof: `∫ t1^2 = T^5/10`. -/
theorem simplex3_t1_sq (T : ℝ) : simplex3 T (fun t1 _ _ => t1 ^ 2) = T ^ 5 / 10 :=
  simplex3_eq T _ (fun t1 t2 => t1 ^ 2 * t2) (fun t1 => t1 ^ 4 / 2) _
    (fun t1 t2 => by rw [integral_of_poly t2 (t1 ^ 2) 0 0 0 0 (fun x => by ring)]; ring)
    (fun t1 => by rw [integral_of_poly t1 0 (t1 ^ 2) 0 0 0 (fun x => by ring)]; ring)
    (by rw [integral_of_poly T 0 0 0 0 (1 / 2) (fun x => by ring)]; ring)

/-- Proposition 6 proof: `∫ t2^2 = T^5/20`. -/
theorem simplex3_t2_sq (T : ℝ) : simplex3 T (fun _ t2 _ => t2 ^ 2) = T ^ 5 / 20 :=
  simplex3_eq T _ (fun _ t2 => t2 ^ 3) (fun t1 => t1 ^ 4 / 4) _
    (fun _ t2 => by rw [integral_of_poly t2 (t2 ^ 2) 0 0 0 0 (fun x => by ring)]; ring)
    (fun t1 => by rw [integral_of_poly t1 0 0 0 1 0 (fun x => by ring)]; ring)
    (by rw [integral_of_poly T 0 0 0 0 (1 / 4) (fun x => by ring)]; ring)

/-- Proposition 6 proof: `∫ t3^2 = T^5/60`. -/
theorem simplex3_t3_sq (T : ℝ) : simplex3 T (fun _ _ t3 => t3 ^ 2) = T ^ 5 / 60 :=
  simplex3_eq T _ (fun _ t2 => t2 ^ 3 / 3) (fun t1 => t1 ^ 4 / 12) _
    (fun _ t2 => by rw [integral_of_poly t2 0 0 1 0 0 (fun x => by ring)]; ring)
    (fun t1 => by rw [integral_of_poly t1 0 0 0 (1 / 3) 0 (fun x => by ring)]; ring)
    (by rw [integral_of_poly T 0 0 0 0 (1 / 12) (fun x => by ring)]; ring)

/-! ### Derived combinations: Lemma 2, Remark 2, Proposition 6 -/

/-- Lemma 2 / Appendix B: `∫ (t3 - t2) = -T^4/24`. -/
theorem simplex3_t3_sub_t2 (T : ℝ) :
    simplex3 T (fun _ t2 t3 => t3 - t2) = -T ^ 4 / 24 :=
  simplex3_eq T _ (fun _ t2 => -t2 ^ 2 / 2) (fun t1 => -t1 ^ 3 / 6) _
    (fun _ t2 => by rw [integral_of_poly t2 (-t2) 1 0 0 0 (fun x => by ring)]; ring)
    (fun t1 => by rw [integral_of_poly t1 0 0 (-1 / 2) 0 0 (fun x => by ring)]; ring)
    (by rw [integral_of_poly T 0 0 0 (-1 / 6) 0 (fun x => by ring)]; ring)

/-- Lemma 2 / Appendix B: `∫ (t1 - t2) = T^4/24`. -/
theorem simplex3_t1_sub_t2 (T : ℝ) :
    simplex3 T (fun t1 t2 _ => t1 - t2) = T ^ 4 / 24 :=
  simplex3_eq T _ (fun t1 t2 => t1 * t2 - t2 ^ 2) (fun t1 => t1 ^ 3 / 6) _
    (fun t1 t2 => by rw [integral_of_poly t2 (t1 - t2) 0 0 0 0 (fun x => by ring)]; ring)
    (fun t1 => by rw [integral_of_poly t1 0 t1 (-1) 0 0 (fun x => by ring)]; ring)
    (by rw [integral_of_poly T 0 0 0 (1 / 6) 0 (fun x => by ring)]; ring)

/-- Lemma 2: the `[N0, [N0, N1]]` coefficient of the third Magnus term,
`(1/6) (∫ (t3 - t2) + ∫ (t1 - t2))`, vanishes: the `T^4` grade is zero. -/
theorem lemma2_cancellation (T : ℝ) :
    (1 / 6 : ℝ) * (simplex3 T (fun _ t2 t3 => t3 - t2) + simplex3 T (fun t1 t2 _ => t1 - t2)) = 0 := by
  rw [simplex3_t3_sub_t2, simplex3_t1_sub_t2]; ring

/-- Lemma 2, evaluated on the combined integrand `(t3 - t2) + (t1 - t2)` directly. -/
theorem lemma2_direct (T : ℝ) :
    simplex3 T (fun t1 t2 t3 => (t3 - t2) + (t1 - t2)) = 0 :=
  simplex3_eq T _ (fun t1 t2 => t1 * t2 - 3 * t2 ^ 2 / 2) (fun _ => 0) _
    (fun t1 t2 => by rw [integral_of_poly t2 (t1 - 2 * t2) 1 0 0 0 (fun x => by ring)]; ring)
    (fun t1 => by rw [integral_of_poly t1 0 t1 (-3 / 2) 0 0 (fun x => by ring)]; ring)
    (by rw [integral_of_poly T 0 0 0 0 0 (fun x => by ring)]; ring)

/-- Appendix B: `∫ t1 (t3 - t2) = -T^5/30`. -/
theorem simplex3_t1_mul_t3_sub_t2 (T : ℝ) :
    simplex3 T (fun t1 t2 t3 => t1 * (t3 - t2)) = -T ^ 5 / 30 :=
  simplex3_eq T _ (fun t1 t2 => -t1 * t2 ^ 2 / 2) (fun t1 => -t1 ^ 4 / 6) _
    (fun t1 t2 => by rw [integral_of_poly t2 (-t1 * t2) t1 0 0 0 (fun x => by ring)]; ring)
    (fun t1 => by rw [integral_of_poly t1 0 0 (-t1 / 2) 0 0 (fun x => by ring)]; ring)
    (by rw [integral_of_poly T 0 0 0 0 (-1 / 6) (fun x => by ring)]; ring)

/-- Appendix B: `∫ t3 (t1 - t2) = T^5/120`. -/
theorem simplex3_t3_mul_t1_sub_t2 (T : ℝ) :
    simplex3 T (fun t1 t2 t3 => t3 * (t1 - t2)) = T ^ 5 / 120 :=
  simplex3_eq T _ (fun t1 t2 => (t1 - t2) * t2 ^ 2 / 2) (fun t1 => t1 ^ 4 / 24) _
    (fun t1 t2 => by rw [integral_of_poly t2 0 (t1 - t2) 0 0 0 (fun x => by ring)]; ring)
    (fun t1 => by rw [integral_of_poly t1 0 0 (t1 / 2) (-1 / 2) 0 (fun x => by ring)]; ring)
    (by rw [integral_of_poly T 0 0 0 0 (1 / 24) (fun x => by ring)]; ring)

/-- Remark 2: the `[N1, [N0, N1]]` coefficient of the third Magnus term,
`(1/6) (∫ t1 (t3 - t2) + ∫ t3 (t1 - t2)) = (1/6)(-T^5/30 + T^5/120) = -T^5/240`,
confirming the `-1/240` of Lemma 3 by direct integral evaluation. -/
theorem remark2_confirmation (T : ℝ) :
    (1 / 6 : ℝ) * (simplex3 T (fun t1 t2 t3 => t1 * (t3 - t2)) +
      simplex3 T (fun t1 t2 t3 => t3 * (t1 - t2))) = -T ^ 5 / 240 := by
  rw [simplex3_t1_mul_t3_sub_t2, simplex3_t3_mul_t1_sub_t2]; ring

/-- Remark 2, evaluated on the combined integrand `t1 (t3 - t2) + t3 (t1 - t2)` directly:
the simplex integral is `-T^5/40`, one sixth of which is `-T^5/240`. -/
theorem remark2_direct (T : ℝ) :
    simplex3 T (fun t1 t2 t3 => t1 * (t3 - t2) + t3 * (t1 - t2)) = -T ^ 5 / 40 :=
  simplex3_eq T _ (fun _ t2 => -t2 ^ 3 / 2) (fun t1 => -t1 ^ 4 / 8) _
    (fun t1 t2 => by
      rw [integral_of_poly t2 (-t1 * t2) (2 * t1 - t2) 0 0 0 (fun x => by ring)]; ring)
    (fun t1 => by rw [integral_of_poly t1 0 0 0 (-1 / 2) 0 (fun x => by ring)]; ring)
    (by rw [integral_of_poly T 0 0 0 0 (-1 / 8) (fun x => by ring)]; ring)

/-- Remark 2 in the form of Lemma 3: one sixth of the combined simplex integral is `-T^5/240`. -/
theorem remark2_direct_coefficient (T : ℝ) :
    (1 / 6 : ℝ) * simplex3 T (fun t1 t2 t3 => t1 * (t3 - t2) + t3 * (t1 - t2)) = -T ^ 5 / 240 := by
  rw [remark2_direct]; ring

/-- Proposition 6: the `[A, [A, C]]` coefficient
`(1/6) ((∫ t3^2 - ∫ t2^2) + (∫ t1^2 - ∫ t2^2)) = (1/6)((T^5/60 - T^5/20) + (T^5/10 - T^5/20)) = T^5/360`. -/
theorem prop6_triple_coefficient (T : ℝ) :
    (1 / 6 : ℝ) * ((simplex3 T (fun _ _ t3 => t3 ^ 2) - simplex3 T (fun _ t2 _ => t2 ^ 2)) +
      (simplex3 T (fun t1 _ _ => t1 ^ 2) - simplex3 T (fun _ t2 _ => t2 ^ 2))) = T ^ 5 / 360 := by
  rw [simplex3_t3_sq, simplex3_t2_sq, simplex3_t1_sq]; ring

/-- Proposition 6, evaluated on the combined integrand `(t3^2 - t2^2) + (t1^2 - t2^2)` directly:
the simplex integral is `T^5/60`, one sixth of which is `T^5/360`. -/
theorem prop6_triple_direct (T : ℝ) :
    simplex3 T (fun t1 t2 t3 => (t3 ^ 2 - t2 ^ 2) + (t1 ^ 2 - t2 ^ 2)) = T ^ 5 / 60 :=
  simplex3_eq T _ (fun t1 t2 => t1 ^ 2 * t2 - 5 * t2 ^ 3 / 3) (fun t1 => t1 ^ 4 / 12) _
    (fun t1 t2 => by
      rw [integral_of_poly t2 (t1 ^ 2 - 2 * t2 ^ 2) 0 1 0 0 (fun x => by ring)]; ring)
    (fun t1 => by rw [integral_of_poly t1 0 (t1 ^ 2) 0 (-5 / 3) 0 (fun x => by ring)]; ring)
    (by rw [integral_of_poly T 0 0 0 0 (1 / 12) (fun x => by ring)]; ring)

/-- Proposition 6 in coefficient form: one sixth of the combined simplex integral is `T^5/360`. -/
theorem prop6_triple_direct_coefficient (T : ℝ) :
    (1 / 6 : ℝ) * simplex3 T (fun t1 t2 t3 => (t3 ^ 2 - t2 ^ 2) + (t1 ^ 2 - t2 ^ 2)) =
      T ^ 5 / 360 := by
  rw [prop6_triple_direct]; ring

end GNC.Magnus
