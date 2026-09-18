import GNC.Magnus.MagnusInputs
import GNC.Magnus.MagnusJet
import GNC.Magnus.MagnusFlow
import GNC.Preintegration.ClosedForm

/-! The first-order-hold increment of Theorem 1 (Eq. 16), the bias
bilinearity of Proposition 4 (Eq. 20), and Corollary 2: with no rotation the
third-order Magnus exponent is exact for every step size. -/
noncomputable section
namespace GNC.Magnus
open Matrix NormedSpace
open scoped Matrix Matrix.Norms.Operator

section Linearity

/-- The time-extended embedding is additive in the pair (coordinates, time). -/
theorem extended_add (x y : LogState) (β γ : ℝ) :
    extended (x + y) (β + γ) = extended x β + extended y γ := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [extended, hat, kinematicC] <;> ring

/-- The time-extended embedding is homogeneous in the pair (coordinates, time). -/
theorem extended_smul (c : ℝ) (x : LogState) (β : ℝ) :
    extended (c • x) (c * β) = c • extended x β := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [extended, hat, kinematicC]

end Linearity

section Increment

/-- Theorem 1, Eq. (16), with the second generator written through the input
slopes `sa`, `sω` (the paper's `∆a/T`, `∆ω/T`). No division by the step size
occurs, so the identity holds for every `T`, including `T = 0`. -/
theorem foh_increment_slopes (T : ℝ) (ω a sω sa : Vec3) :
    T • extended ![0, a, ω] 1 + (T^2/2) • extended ![0, sa, sω] 0 +
      (T^3/12) • (extended ![0, a, ω] 1 * extended ![0, sa, sω] 0 -
        extended ![0, sa, sω] 0 * extended ![0, a, ω] 1) =
      extended ![positionIncrement T (T • sa),
        velocityIncrement T ω a (T • sω) (T • sa),
        rotationIncrement T ω (T • sω)] T := by
  rw [foh_commutator, ← extended_smul, ← extended_smul, ← extended_smul,
    ← extended_add, ← extended_add]
  congr 1
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [positionIncrement, velocityIncrement, rotationIncrement, crossProduct,
        vecHead, vecTail] <;> ring
  · ring

/-- Theorem 1, Eq. (16), with the generators of Eq. (8): `N0 = ξ(0, a, ω; 1)`
and `N1 = ξ(0, ∆a/T, ∆ω/T; 0)`. The third-order exponent
`T N0 + (T²/2) N1 + (T³/12)[N0, N1]` is the time-extended element of the
corrected body increment `(ū2, ā, ω̄)` with time component `T`. -/
theorem foh_increment (T : ℝ) (hT : T ≠ 0) (ω a dω da : Vec3) :
    T • extended ![0, a, ω] 1 +
      (T^2/2) • extended ![0, (1/T) • da, (1/T) • dω] 0 +
      (T^3/12) • (extended ![0, a, ω] 1 * extended ![0, (1/T) • da, (1/T) • dω] 0 -
        extended ![0, (1/T) • da, (1/T) • dω] 0 * extended ![0, a, ω] 1) =
      extended ![positionIncrement T da, velocityIncrement T ω a dω da,
        rotationIncrement T ω dω] T := by
  have h := foh_increment_slopes T ω a ((1/T) • dω) ((1/T) • da)
  simpa only [smul_smul, mul_one_div_cancel hT, one_smul] using h

end Increment

section BiasBilinearity
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

/-- Proposition 4, Eq. (20): the bracket is bilinear, so along the bias ray
`N0 - s B0` (with `N1` bias-invariant) its derivative is `-[B0, N1]`. -/
theorem comm_bias_derivative (N0 B0 N1 : A) (s : ℝ) :
    HasDerivAt (fun s : ℝ => comm (N0 - s • B0) N1) (-(comm B0 N1)) s := by
  have he : (fun s : ℝ => comm (N0 - s • B0) N1) =
      fun s => comm N0 N1 + s • (-(comm B0 N1)) := by
    funext s
    simp only [comm, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm]
    module
  rw [he]
  simpa only [one_smul] using
    ((hasDerivAt_id' s).smul_const (-(comm B0 N1))).const_add (comm N0 N1)

/-- Eq. (20) with the Magnus weight `T³/12`. -/
theorem scaled_comm_bias_derivative (T : ℝ) (N0 B0 N1 : A) (s : ℝ) :
    HasDerivAt (fun s : ℝ => (T^3/12) • comm (N0 - s • B0) N1)
      ((T^3/12) • -(comm B0 N1)) s :=
  (comm_bias_derivative N0 B0 N1 s).const_smul (T^3/12)

end BiasBilinearity

section BiasSE23

/-- A constant gyro and accelerometer bias enters `N0` affinely. -/
theorem extended_bias_ray (ω a bg ba : Vec3) (s : ℝ) :
    extended ![0, a - s • ba, ω - s • bg] 1 =
      extended ![0, a, ω] 1 - s • extended ![0, ba, bg] 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [extended, hat, kinematicC] <;> ring

/-- Proposition 4, Eq. (20), for the FOH generators of Eq. (8): the bracket
correction is differentiable in the bias with derivative
`-(T³/12)[ξ(0, ba, bg; 0), N1]`. -/
theorem foh_bracket_bias_derivative (T : ℝ) (ω a bg ba : Vec3) (N1 : Mat5) (s : ℝ) :
    HasDerivAt (fun s : ℝ => (T^3/12) • comm (extended ![0, a - s • ba, ω - s • bg] 1) N1)
      ((T^3/12) • -(comm (extended ![0, ba, bg] 0) N1)) s := by
  simp only [extended_bias_ray]
  exact scaled_comm_bias_derivative T _ _ N1 s

end BiasSE23

section Termination
variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- Corollary 2: the explicit right flow of the linear generator `a + t b`
when every product of three factors from `{a, b}` vanishes. -/
def fohPolynomial (a b : A) : ℝ → A := fun t =>
  1 + t • a + (t^2/2) • (a*a + b) + t^3 • ((1/3:ℝ) • (a*b) + (1/6:ℝ) • (b*a)) +
    (t^4/8) • (b*b)

/-- The vanishing of three-factor products, in the shape needed to kill
left-associated monomials. -/
def TripleVanishes (a b : A) : Prop :=
  ∀ x y z : A, (x = a ∨ x = b) → (y = a ∨ y = b) → (z = a ∨ z = b) → x*y*z = 0

omit [Algebra ℝ A] in
theorem TripleVanishes.right {a b : A} (h : TripleVanishes a b) :
    ∀ x y z : A, (x = a ∨ x = b) → (y = a ∨ y = b) → (z = a ∨ z = b) → x*(y*z) = 0 :=
  fun x y z hx hy hz => by rw [← mul_assoc]; exact h x y z hx hy hz

/-- The polynomial multiplied by the FOH generator, with the vanishing triple
products removed. -/
theorem fohPolynomial_mul {a b : A} (h : TripleVanishes a b) (t : ℝ) :
    fohPolynomial a b t * (a + t • b) =
      a + t • (a*a + b) + t^2 • (a*b + (1/2:ℝ) • (b*a)) + (t^3/2) • (b*b) := by
  have haaa := h a a a (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)
  have haab := h a a b (Or.inl rfl) (Or.inl rfl) (Or.inr rfl)
  have haba := h a b a (Or.inl rfl) (Or.inr rfl) (Or.inl rfl)
  have habb := h a b b (Or.inl rfl) (Or.inr rfl) (Or.inr rfl)
  have hbaa := h b a a (Or.inr rfl) (Or.inl rfl) (Or.inl rfl)
  have hbab := h b a b (Or.inr rfl) (Or.inl rfl) (Or.inr rfl)
  have hbba := h b b a (Or.inr rfl) (Or.inr rfl) (Or.inl rfl)
  have hbbb := h b b b (Or.inr rfl) (Or.inr rfl) (Or.inr rfl)
  simp only [fohPolynomial, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul,
    haaa, haab, haba, habb, hbaa, hbab, hbba, hbbb, smul_zero, add_zero, zero_add]
  module

/-- The third-order Magnus exponent of the linear generator `a + t b`. -/
def fohExponent (a b : A) (t : ℝ) : A :=
  t • a + (t^2/2) • b + (t^3/12) • comm a b

/-- With vanishing triple products the exponent is cube-zero. -/
theorem fohExponent_cube {a b : A} (h : TripleVanishes a b) (t : ℝ) :
    fohExponent a b t ^ 3 = 0 := by
  have haaa := h.right a a a (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)
  have haab := h.right a a b (Or.inl rfl) (Or.inl rfl) (Or.inr rfl)
  have haba := h.right a b a (Or.inl rfl) (Or.inr rfl) (Or.inl rfl)
  have habb := h.right a b b (Or.inl rfl) (Or.inr rfl) (Or.inr rfl)
  have hbaa := h.right b a a (Or.inr rfl) (Or.inl rfl) (Or.inl rfl)
  have hbab := h.right b a b (Or.inr rfl) (Or.inl rfl) (Or.inr rfl)
  have hbba := h.right b b a (Or.inr rfl) (Or.inr rfl) (Or.inl rfl)
  have hbbb := h.right b b b (Or.inr rfl) (Or.inr rfl) (Or.inr rfl)
  simp only [fohExponent, comm, sub_eq_add_neg, pow_succ, pow_zero, one_mul,
    add_mul, mul_add, mul_assoc, smul_mul_assoc, mul_smul_comm, smul_add, smul_neg,
    smul_smul, neg_mul, mul_neg, haaa, haab, haba, habb, hbaa, hbab, hbba, hbbb,
    smul_zero, neg_zero, add_zero, mul_zero]

/-- The truncated exponential series of a cube-zero exponent equals the
polynomial flow. -/
theorem fohExponent_series {a b : A} (h : TripleVanishes a b) (t : ℝ) :
    1 + fohExponent a b t + (1/2:ℝ) • (fohExponent a b t * fohExponent a b t) =
      fohPolynomial a b t := by
  have haab := h.right a a b (Or.inl rfl) (Or.inl rfl) (Or.inr rfl)
  have haba := h.right a b a (Or.inl rfl) (Or.inr rfl) (Or.inl rfl)
  have habb := h.right a b b (Or.inl rfl) (Or.inr rfl) (Or.inr rfl)
  have hbaa := h.right b a a (Or.inr rfl) (Or.inl rfl) (Or.inl rfl)
  have hbab := h.right b a b (Or.inr rfl) (Or.inl rfl) (Or.inr rfl)
  have hbba := h.right b b a (Or.inr rfl) (Or.inr rfl) (Or.inl rfl)
  simp only [fohExponent, fohPolynomial, comm, sub_eq_add_neg, pow_succ, pow_zero, one_mul,
    add_mul, mul_add, mul_assoc, smul_mul_assoc, mul_smul_comm, smul_add, smul_neg,
    smul_smul, neg_mul, mul_neg, haab, haba, habb, hbaa, hbab, hbba,
    smul_zero, neg_zero, add_zero, mul_zero]
  module

end Termination

section TerminationBanach
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

omit [CompleteSpace A] in
/-- Corollary 2 (a): `fohPolynomial a b` solves `Y' = Y (a + t b)`. -/
theorem fohPolynomial_derivative {a b : A} (h : TripleVanishes a b) (t : ℝ) :
    HasDerivAt (fohPolynomial a b) (fohPolynomial a b t * (a + t • b)) t := by
  rw [fohPolynomial_mul h]
  have hd := ((((hasDerivAt_id' t).smul_const a).const_add (1:A)).add
    (((hasDerivAt_pow 2 t).div_const 2).smul_const (a*a + b))).add
    ((hasDerivAt_pow 3 t).smul_const ((1/3:ℝ) • (a*b) + (1/6:ℝ) • (b*a))) |>.add
    (((hasDerivAt_pow 4 t).div_const 8).smul_const (b*b))
  convert hd using 1
  simp
  module

/-- Corollary 2 (b): when the FOH problem is confined to a two-step nilpotent
part, the third-order Magnus exponent is exact for every `t`. -/
theorem exp_fohExponent {a b : A} (h : TripleVanishes a b) (t : ℝ) :
    exp (fohExponent a b t) = fohPolynomial a b t := by
  have h3 := fohExponent_cube h t
  have h4 : fohExponent a b t ^ 4 = 0 := by rw [pow_succ, h3, zero_mul]
  have h5 : fohExponent a b t ^ 5 = -((1:ℝ)^2) • fohExponent a b t ^ 3 := by
    rw [pow_succ, h4, zero_mul, h3, smul_zero]
  have he := Preintegration.exp_polynomial (fohExponent a b t) 1 1 one_ne_zero h5
  simp only [Preintegration.polynomial, one_smul, h3, h4, smul_zero, add_zero,
    pow_two] at he
  rw [he, ← fohExponent_series h t]
  norm_num

/-- Corollary 2 (c): the exact exponent is the unique right flow of the
linear FOH generator starting at the identity. -/
theorem foh_flow_unique {a b : A} (h : TripleVanishes a b) (Y : ℝ → A)
    (hY0 : Y 0 = 1) (hY : ∀ t, HasDerivAt Y (Y t * (a + t • b)) t) :
    Y = fun t => exp (fohExponent a b t) := by
  have hN : Continuous (fun t : ℝ => a + t • b) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hu := mixed_flow_unique (fun _ => (0:A)) (fun t => a + t • b) continuous_const hN
    Y (fohPolynomial a b) (fun t => by simpa using hY t)
    (fun t => by simpa using fohPolynomial_derivative h t)
    (by simp [hY0, fohPolynomial])
  rw [hu]
  funext t
  exact (exp_fohExponent h t).symm

end TerminationBanach

section TerminationSE23

/-- Proposition 2 strengthened to products: any three elements of the
translation/time ideal multiply to zero. -/
theorem ideal_triple_product (p v q w r u : Vec3) (β γ δ : ℝ) :
    ideal p v β * ideal q w γ * ideal r u δ = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ideal, extended, hat, kinematicC, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The FOH generators without rotation satisfy the triple-product hypothesis. -/
theorem ideal_tripleVanishes (a s : Vec3) :
    TripleVanishes (ideal 0 a 1) (ideal 0 s 0) := by
  intro x y z hx hy hz
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rcases hz with rfl | rfl <;>
    exact ideal_triple_product _ _ _ _ _ _ _ _ _

/-- Corollary 2 on SE₂(3): with `ω = ∆ω = 0` the exponential of the
third-order exponent is the polynomial flow, for every step size. -/
theorem exp_foh_no_rotation (a s : Vec3) (T : ℝ) :
    exp (fohExponent (ideal 0 a 1) (ideal 0 s 0) T) =
      fohPolynomial (ideal 0 a 1) (ideal 0 s 0) T :=
  exp_fohExponent (ideal_tripleVanishes a s) T

/-- Corollary 2 on SE₂(3), in the increment form of Eq. (16): the exponential
of the corrected increment `(ū2, ā, 0)` with time component `T` is the exact
polynomial flow of the FOH generator `N0 + t N1`. -/
theorem exp_foh_increment_no_rotation (T : ℝ) (hT : T ≠ 0) (a da : Vec3) :
    exp (extended ![positionIncrement T da, velocityIncrement T 0 a 0 da,
        rotationIncrement T 0 0] T) =
      fohPolynomial (ideal 0 a 1) (ideal 0 ((1/T) • da) 0) T := by
  rw [← exp_foh_no_rotation, ← foh_increment T hT 0 a 0 da]
  simp only [fohExponent, comm, ideal, smul_zero]

/-- Corollary 2 on SE₂(3), uniqueness: any right flow of the rotation-free
FOH generator from the identity is the exponential of the exact exponent. -/
theorem foh_flow_no_rotation_unique (a s : Vec3) (Y : ℝ → Mat5) (hY0 : Y 0 = 1)
    (hY : ∀ t, HasDerivAt Y (Y t * (ideal 0 a 1 + t • ideal 0 s 0)) t) :
    Y = fun t => exp (fohExponent (ideal 0 a 1) (ideal 0 s 0) t) :=
  foh_flow_unique (ideal_tripleVanishes a s) Y hY0 hY

end TerminationSE23
end GNC.Magnus
