import GNC.Magnus.FOHIncrement
import GNC.Magnus.ResidualBound

/-! The mass-depletion attitude hold on the time-extended SE₂(3) algebra.

During a constant-force burn from a fixed inertial attitude the thrust
acceleration is `a t = F w(t) e` for a constant body direction `e` and reciprocal
mass `w`. With zero body rate the generator is `N t = ξ(0, a t, 0; 1)`, an element
of the translation/time ideal, so every triple product of these generators
vanishes. Expanding the reciprocal mass to second order in the step gives a
quadratic generator `N t = A + t B + t² C` whose Magnus exponent, in the right
convention `exponent5` used by
`GNC.Applications.PreintegrationErrorTheory.lemma1_right_stem`, has the mass-hold
increment as its coefficients through degree four. At degree five the brackets
`[B,C]` and `[B,[A,B]]` vanish, leaving `[A,[A,[A,B]]]` (zero when `ω = 0`) and
`[A,[A,C]]`, both bounded through the submultiplicative estimate
`norm_comm_le`. -/
noncomputable section
namespace GNC.MassDepletionHold
open GNC GNC.Magnus Polynomial
open scoped Matrix Matrix.Norms.Operator
set_option maxHeartbeats 2000000

/-! ### Zero body-rate generator lies in the two-step nilpotent ideal -/

/-- The mass-depletion thrust generator with zero body rate:
`N t = ξ(0, F w(t) e, 0; 1)`, matching the paper's `ξ(0, [a(t) 0], 1)`. -/
def N (F : ℝ) (w : ℝ → ℝ) (e : Vec3) (t : ℝ) : Mat5 := ideal 0 ((F * w t) • e) 1

/-- Every product of three zero-body-rate generators vanishes, so their Lie
algebra is two-step nilpotent (Proposition 2 specialised to the burn). -/
theorem N_triple_product (F : ℝ) (w : ℝ → ℝ) (e : Vec3) (t₁ t₂ t₃ : ℝ) :
    N F w e t₁ * N F w e t₂ * N F w e t₃ = 0 :=
  ideal_triple_product _ _ _ _ _ _ _ _ _

/-! ### The quadratic generator `N t = A + t B + t² C`

`A` carries the constant body rate `ω` and the leading thrust `F w₀ e`; `B` and
`C` are pure translation/time generators carrying the first and second reciprocal
mass slopes. -/

/-- The constant part `A = ξ(ω, F w₀ e, 0; 1)`. -/
def Agen (F w₀ : ℝ) (ω e : Vec3) : Mat5 := extended ![0, (F * w₀) • e, ω] 1

/-- The linear slope `B = ξ(0, F w₁ e, 0; 0)`. -/
def Bgen (F w₁ : ℝ) (e : Vec3) : Mat5 := extended ![0, (F * w₁) • e, 0] 0

/-- The quadratic slope `C = ξ(0, F w₂ e, 0; 0)`. -/
def Cgen (F w₂ : ℝ) (e : Vec3) : Mat5 := extended ![0, (F * w₂) • e, 0] 0

/-! ### Bracket identities of the mass-hold generators -/

/-- The two translation/time slopes commute: `[B, C] = 0`. -/
theorem comm_Bgen_Cgen (F w₁ w₂ : ℝ) (e : Vec3) :
    Magnus.comm (Bgen F w₁ e) (Cgen F w₂ e) = 0 := by
  rw [show Bgen F w₁ e = ideal 0 ((F * w₁) • e) 0 from rfl,
    show Cgen F w₂ e = ideal 0 ((F * w₂) • e) 0 from rfl]
  unfold Magnus.comm
  rw [ideal_commutator]
  ext i j; fin_cases i <;> fin_cases j <;> simp [ideal, extended, hat, kinematicC]

/-- The leading bracket `[A, B] = ξ(0, F w₁ (ω × e), -F w₁ e; 0)`; the sign of the
time corner is that of `extended_commutator`. -/
theorem comm_Agen_Bgen (F w₀ w₁ : ℝ) (ω e : Vec3) :
    Magnus.comm (Agen F w₀ ω e) (Bgen F w₁ e) =
      extended ![-(F * w₁) • e, (F * w₁) • (ω ⨯₃ e), 0] 0 := by
  simp only [Magnus.comm, Agen, Bgen]
  rw [foh_commutator]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cross_apply]

/-- The quadratic bracket `[A, C] = ξ(0, F w₂ (ω × e), -F w₂ e; 0)`. -/
theorem comm_Agen_Cgen (F w₀ w₂ : ℝ) (ω e : Vec3) :
    Magnus.comm (Agen F w₀ ω e) (Cgen F w₂ e) =
      extended ![-(F * w₂) • e, (F * w₂) • (ω ⨯₃ e), 0] 0 := by
  simp only [Magnus.comm, Agen, Cgen]
  rw [foh_commutator]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cross_apply]

/-! ### Coefficients of the right Magnus exponent -/

theorem exponent5_coeff1 (a b c : Mat5) : (exponent5 a b c).coeff 1 = a := by
  simp [exponent5, Polynomial.coeff_add, Polynomial.coeff_monomial]

theorem exponent5_coeff2 (a b c : Mat5) :
    (exponent5 a b c).coeff 2 = (1 / 2 : ℝ) • b := by
  simp [exponent5, Polynomial.coeff_add, Polynomial.coeff_monomial]

theorem exponent5_coeff3 (a b c : Mat5) :
    (exponent5 a b c).coeff 3 = (1 / 3 : ℝ) • c + (1 / 12 : ℝ) • Magnus.comm a b := by
  simp [exponent5, Polynomial.coeff_add, Polynomial.coeff_monomial]

theorem exponent5_coeff4 (a b c : Mat5) :
    (exponent5 a b c).coeff 4 = (1 / 12 : ℝ) • Magnus.comm a c := by
  simp [exponent5, Polynomial.coeff_add, Polynomial.coeff_monomial]

/-! ### The mass-hold increment (equation mass-inc)

Through degree four the right Magnus exponent of the quadratic generator reduces
to the time-extended element of the corrected body increment `(ū₂, ā, ω̄)` with
time component `h`, where

`ω̄ = h ω`,
`ā = F(h w₀ + h²/2 w₁ + h³/3 w₂) e + F(h³/12 w₁ + h⁴/12 w₂) (ω × e)`,
`ū₂ = -F(h³/12 w₁ + h⁴/12 w₂) e`. -/
theorem massHold_increment (F w₀ w₁ w₂ h : ℝ) (ω e : Vec3) :
    h • (exponent5 (Agen F w₀ ω e) (Bgen F w₁ e) (Cgen F w₂ e)).coeff 1 +
      h ^ 2 • (exponent5 (Agen F w₀ ω e) (Bgen F w₁ e) (Cgen F w₂ e)).coeff 2 +
      h ^ 3 • (exponent5 (Agen F w₀ ω e) (Bgen F w₁ e) (Cgen F w₂ e)).coeff 3 +
      h ^ 4 • (exponent5 (Agen F w₀ ω e) (Bgen F w₁ e) (Cgen F w₂ e)).coeff 4 =
      extended
        ![(-(F * (h ^ 3 / 12 * w₁ + h ^ 4 / 12 * w₂))) • e,
          (F * (h * w₀ + h ^ 2 / 2 * w₁ + h ^ 3 / 3 * w₂)) • e +
            (F * (h ^ 3 / 12 * w₁ + h ^ 4 / 12 * w₂)) • (ω ⨯₃ e),
          h • ω] h := by
  rw [exponent5_coeff1, exponent5_coeff2, exponent5_coeff3, exponent5_coeff4,
    comm_Agen_Bgen, comm_Agen_Cgen]
  simp only [Agen, Bgen, Cgen]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [extended, hat, kinematicC, cross_apply, Matrix.add_apply,
      Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.vecHead, Matrix.vecTail, Pi.smul_apply, Pi.neg_apply,
      smul_eq_mul] <;>
    ring

/-! ### Degree-five residual bound -/

theorem exponent5_coeff5 (a b c : Mat5) :
    (exponent5 a b c).coeff 5 = (1 / 60 : ℝ) • Magnus.comm b c -
      (1 / 240 : ℝ) • Magnus.comm b (Magnus.comm a b) -
      (1 / 720 : ℝ) • Magnus.comm a (Magnus.comm a (Magnus.comm a b)) +
      (1 / 360 : ℝ) • Magnus.comm a (Magnus.comm a c) := by
  simp [exponent5, Polynomial.coeff_add, Polynomial.coeff_monomial]

/-- The slope `B` commutes with the leading bracket: `[B,[A,B]] = 0`. -/
theorem comm_Bgen_comm_Agen_Bgen (F w₀ w₁ : ℝ) (ω e : Vec3) :
    Magnus.comm (Bgen F w₁ e) (Magnus.comm (Agen F w₀ ω e) (Bgen F w₁ e)) = 0 := by
  rw [comm_Agen_Bgen,
    show Bgen F w₁ e = ideal 0 ((F * w₁) • e) 0 from rfl,
    show extended ![-(F * w₁) • e, (F * w₁) • (ω ⨯₃ e), 0] 0 =
      ideal (-(F * w₁) • e) ((F * w₁) • (ω ⨯₃ e)) 0 from rfl]
  unfold Magnus.comm
  rw [ideal_commutator]
  ext i j; fin_cases i <;> fin_cases j <;> simp [ideal, extended, hat, kinematicC]

/-- The degree-five coefficient of the mass-hold exponent reduces to
`-(1/720) [A,[A,[A,B]]] + (1/360) [A,[A,C]]`. -/
theorem massHold_degree_five (F w₀ w₁ w₂ : ℝ) (ω e : Vec3) :
    (exponent5 (Agen F w₀ ω e) (Bgen F w₁ e) (Cgen F w₂ e)).coeff 5 =
      -((1 / 720 : ℝ) • Magnus.comm (Agen F w₀ ω e)
          (Magnus.comm (Agen F w₀ ω e) (Magnus.comm (Agen F w₀ ω e) (Bgen F w₁ e)))) +
        (1 / 360 : ℝ) • Magnus.comm (Agen F w₀ ω e)
          (Magnus.comm (Agen F w₀ ω e) (Cgen F w₂ e)) := by
  rw [exponent5_coeff5, comm_Bgen_Cgen, comm_Bgen_comm_Agen_Bgen]
  simp only [smul_zero, zero_sub, sub_zero]

/-- The triple bracket obeys `‖[A,[A,[A,B]]]‖ ≤ 8 ‖A‖³ ‖B‖`. -/
theorem residual_triple_norm_le (F w₀ w₁ : ℝ) (ω e : Vec3) :
    ‖Magnus.comm (Agen F w₀ ω e)
        (Magnus.comm (Agen F w₀ ω e) (Magnus.comm (Agen F w₀ ω e) (Bgen F w₁ e)))‖ ≤
      8 * ‖Agen F w₀ ω e‖ ^ 3 * ‖Bgen F w₁ e‖ := by
  set A := Agen F w₀ ω e
  set B := Bgen F w₁ e
  have h1 := norm_comm_le A (Magnus.comm A (Magnus.comm A B))
  have h2 := norm_comm_le A (Magnus.comm A B)
  have h3 := norm_comm_le A B
  have hA : 0 ≤ ‖A‖ := norm_nonneg _
  calc ‖Magnus.comm A (Magnus.comm A (Magnus.comm A B))‖
      ≤ 2 * ‖A‖ * ‖Magnus.comm A (Magnus.comm A B)‖ := h1
    _ ≤ 2 * ‖A‖ * (2 * ‖A‖ * ‖Magnus.comm A B‖) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ ≤ 2 * ‖A‖ * (2 * ‖A‖ * (2 * ‖A‖ * ‖B‖)) := by gcongr
    _ = 8 * ‖A‖ ^ 3 * ‖B‖ := by ring

/-- The degree-five bracket `[A,[A,C]]` obeys the submultiplicative bound
`‖[A,[A,C]]‖ ≤ 4 ‖A‖² ‖C‖` (Corollary 1, specialised). -/
theorem residual_comm_norm_le (F w₀ w₂ : ℝ) (ω e : Vec3) :
    ‖Magnus.comm (Agen F w₀ ω e) (Magnus.comm (Agen F w₀ ω e) (Cgen F w₂ e))‖ ≤
      4 * ‖Agen F w₀ ω e‖ ^ 2 * ‖Cgen F w₂ e‖ := by
  have h1 := norm_comm_le (Agen F w₀ ω e) (Magnus.comm (Agen F w₀ ω e) (Cgen F w₂ e))
  have h2 := norm_comm_le (Agen F w₀ ω e) (Cgen F w₂ e)
  calc ‖Magnus.comm (Agen F w₀ ω e) (Magnus.comm (Agen F w₀ ω e) (Cgen F w₂ e))‖
      ≤ 2 * ‖Agen F w₀ ω e‖ * ‖Magnus.comm (Agen F w₀ ω e) (Cgen F w₂ e)‖ := h1
    _ ≤ 2 * ‖Agen F w₀ ω e‖ * (2 * ‖Agen F w₀ ω e‖ * ‖Cgen F w₂ e‖) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = 4 * ‖Agen F w₀ ω e‖ ^ 2 * ‖Cgen F w₂ e‖ := by ring

end GNC.MassDepletionHold
