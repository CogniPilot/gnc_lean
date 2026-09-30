import GNC.Preintegration.PhysicalDefectMoments
import GNC.Magnus.FohDefectCertificate

/-! Sparse finite FOH polynomials and their exact physical defects.
The recurrence and its cancellation are proved before applying any error
envelope. No predictor ODE or infinite-series identification is assumed. -/
noncomputable section
open Set Finset
namespace GNC.Preintegration.CenteredFoh.Defect.Sparse
open GNC.Magnus GNC.EuclideanOperator InputError

section Primitive
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def polynomial (c : ℕ → E) (n : ℕ) (t : ℝ) : E :=
  ∑ k ∈ range (n+1), t^k • c k

def integratedCoefficient (c : ℕ → E) : ℕ → E
  | 0 => 0
  | k+1 => (1/(k+1:ℕ):ℝ) • c k

@[simp] theorem polynomial_zero (c : ℕ → E) (n : ℕ) : polynomial c n 0 = c 0 := by
  rw [polynomial, sum_range_succ']
  simp

theorem polynomial_succ (c : ℕ → E) (n : ℕ) (t : ℝ) :
    polynomial c (n+1) t = polynomial c n t+t^(n+1) • c (n+1) := by
  simp only [polynomial, sum_range_succ]

theorem integratedCoefficient_step (c : ℕ → E) (n : ℕ) :
    (n+1:ℕ) • integratedCoefficient c (n+1) = c n := by
  simp only [integratedCoefficient, Nat.cast_add, Nat.cast_one]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  simp only [Nat.cast_add, Nat.cast_one]
  rw [mul_one_div_cancel (by positivity : (n:ℝ)+1 ≠ 0), one_smul]

/-- A finite antiderivative misses just the final coefficient of its forcing. -/
theorem integrated_polynomial_derivative (c : ℕ → E) (n : ℕ) (t : ℝ) :
    HasDerivAt (polynomial (integratedCoefficient c) n)
      (polynomial c n t-t^n • c n) t := by
  induction n with
  | zero =>
    have hfun : polynomial (integratedCoefficient c) 0 = fun _ => (0:E) := by
      funext s
      simp [polynomial, integratedCoefficient]
    rw [hfun]
    simpa [polynomial, integratedCoefficient] using hasDerivAt_const t (0:E)
  | succ n ih =>
    have hpow := ((hasDerivAt_id t).pow (n+1)).smul_const
      (integratedCoefficient c (n+1))
    have hfun : polynomial (integratedCoefficient c) (n+1) = fun s =>
        polynomial (integratedCoefficient c) n s+
          s^(n+1) • integratedCoefficient c (n+1) := by
      funext s
      exact polynomial_succ _ _ _
    rw [hfun]
    convert ih.add hpow using 1
    rw [polynomial_succ]
    simp only [id_eq, Nat.add_sub_cancel, mul_one]
    have hn : ((n+1:ℕ):ℝ) • integratedCoefficient c (n+1) = c n := by
      rw [Nat.cast_smul_eq_nsmul]
      exact integratedCoefficient_step c n
    rw [mul_smul, smul_comm (((n+1:ℕ):ℝ)) (t^n), hn]
    abel

end Primitive

def rotationCoefficient (W D : Op) (n : ℕ) : Op := flowCoeff W D 0 n
def previousRotation (W D : Op) : ℕ → Op
  | 0 => 0
  | k+1 => rotationCoefficient W D k
def forcingCoefficient (W D : Op) (U V : E3) (n : ℕ) : E3 :=
  rotationCoefficient W D n U+previousRotation W D n V
def velocityCoefficient (W D : Op) (U V : E3) : ℕ → E3 :=
  integratedCoefficient (forcingCoefficient W D U V)
def positionCoefficient (W D : Op) (U V : E3) (scale : ℝ) : ℕ → E3 :=
  integratedCoefficient (fun k => scale • velocityCoefficient W D U V k)

def rotationPolynomial (W D : Op) (n : ℕ) : ℝ → Op := fohTaylor W D n
def velocityPolynomial (W D : Op) (U V : E3) (n : ℕ) : ℝ → E3 :=
  polynomial (velocityCoefficient W D U V) n
def positionPolynomial (W D : Op) (U V : E3) (scale : ℝ) (n : ℕ) : ℝ → E3 :=
  polynomial (positionCoefficient W D U V scale) n

/-- Sparse operator action is the full affine forcing polynomial with its
one high-order product removed. -/
theorem forcing_polynomial (W D : Op) (U V : E3) (n : ℕ) (t : ℝ) :
    polynomial (forcingCoefficient W D U V) n t =
      rotationPolynomial W D n t (U+t • V)-
        t^(n+1) • rotationCoefficient W D n V := by
  induction n with
  | zero =>
    simp [polynomial, forcingCoefficient, previousRotation,
      rotationCoefficient, rotationPolynomial, fohTaylor, flowCoeff, map_add, map_smul]
  | succ n ih =>
    rw [polynomial_succ, ih]
    simp only [rotationPolynomial, fohTaylor, sum_range_succ]
    simp only [forcingCoefficient, previousRotation, rotationCoefficient,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, map_add, map_smul,
      pow_succ, smul_add, smul_smul]
    module

theorem rotation_polynomial_derivative (W D : Op) (n : ℕ) (t : ℝ) :
    HasDerivAt (rotationPolynomial W D n)
      (rotationPolynomial W D n t*(W+t • D)-
        t^n • ((n+1:ℕ) • rotationCoefficient W D (n+1))-
        t^(n+1) • (rotationCoefficient W D n*D)) t := by
  simpa only [rotationPolynomial, rotationCoefficient, Nat.cast_smul_eq_nsmul] using
    fohTaylor_derivative W D n t

theorem velocity_polynomial_derivative (W D : Op) (U V : E3) (n : ℕ) (t : ℝ) :
    HasDerivAt (velocityPolynomial W D U V n)
      (rotationPolynomial W D n t (U+t • V)-
        t^n • ((n+1:ℕ) • velocityCoefficient W D U V (n+1))-
        t^(n+1) • rotationCoefficient W D n V) t := by
  have h := integrated_polynomial_derivative (forcingCoefficient W D U V) n t
  rw [forcing_polynomial] at h
  rw [← integratedCoefficient_step (forcingCoefficient W D U V) n] at h
  convert h using 1
  dsimp [velocityCoefficient]
  abel

theorem position_polynomial_derivative (W D : Op) (U V : E3)
    (scale : ℝ) (n : ℕ) (t : ℝ) :
    HasDerivAt (positionPolynomial W D U V scale n)
      (scale • velocityPolynomial W D U V n t-
        t^n • (scale • velocityCoefficient W D U V n)) t := by
  have h := integrated_polynomial_derivative
    (fun k => scale • velocityCoefficient W D U V k) n t
  convert h using 1
  simp only [polynomial, velocityPolynomial, Finset.smul_sum]
  congr 1
  exact Finset.sum_congr rfl (fun k _ => smul_comm _ _ _)

def rotationDefect (W D : Op) (n : ℕ) (t : ℝ) : Op :=
  -t^n • ((n+1:ℕ) • rotationCoefficient W D (n+1))-
    t^(n+1) • (rotationCoefficient W D n*D)
def velocityDefect (W D : Op) (U V : E3) (n : ℕ) (t : ℝ) : E3 :=
  -t^n • ((n+1:ℕ) • velocityCoefficient W D U V (n+1))-
    t^(n+1) • rotationCoefficient W D n V
def positionDefect (W D : Op) (U V : E3) (scale : ℝ) (n : ℕ) (t : ℝ) : E3 :=
  -t^n • (scale • velocityCoefficient W D U V n)

section Norms
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem two_term_defect_norm (x y : E) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ‖-a • x-b • y‖ ≤ a*‖x‖+b*‖y‖ := by
  simpa only [norm_neg, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg ha, abs_of_nonneg hb] using norm_sub_le (-a • x) (b • y)

theorem affine_input_norm (U V : E) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    ‖U+t • V‖ ≤ (1-t)*‖U‖+t*‖U+V‖ := by
  have he : U+t • V = (1-t) • U+t • (U+V) := by module
  rw [he]
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1,
    abs_of_nonneg (sub_nonneg.mpr ht.2)] using
    norm_add_le ((1-t) • U) (t • (U+V))

end Norms

theorem rotation_defect_norm (W D : Op) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    frobenius (rotationDefect W D n t) ≤
      t^n*frobenius ((n+1:ℕ) • rotationCoefficient W D (n+1))+
      t^(n+1)*frobenius (rotationCoefficient W D n*D) := by
  change ‖columnsCLM 3 (rotationDefect W D n t)‖ ≤ _
  simp only [rotationDefect, map_sub, map_smul]
  exact two_term_defect_norm _ _ (pow_nonneg ht _) (pow_nonneg ht _)

/-- The computable sparse recurrence implies its full physical error budgets.
Only the actual FOH trajectory equations and initial conditions are premises;
the finite predictors' equations and defects are conclusions of earlier lemmas. -/
theorem sparse_physical_certificate (ω₀ ωs : Vec3) (U V : E3) {scale : ℝ}
    (hscale : 0 ≤ scale) (n : ℕ) (R : ℝ → SO3) (v p : ℝ → E3)
    (hR : ∀ t ∈ Set.Icc 0 1, HasDerivAt (fun s => rotation (R s))
      (rotation (R t)*hat (ω₀+t • ωs)) t)
    (hv : ∀ t ∈ Set.Icc 0 1, HasDerivAt v (rotation (R t) (U+t • V)) t)
    (hp : ∀ t ∈ Set.Icc 0 1, HasDerivAt p (scale • v t) t)
    (hR0 : rotation (R 0) = 1) (hv0 : v 0 = 0) (hp0 : p 0 = 0) :
    let W := hat ω₀; let D := hat ωs
    let cr := frobenius ((n+1:ℕ) • rotationCoefficient W D (n+1))
    let dr := frobenius (rotationCoefficient W D n*D)
    let cv := ‖(n+1:ℕ) • velocityCoefficient W D U V (n+1)‖
    let dv := ‖rotationCoefficient W D n V‖
    let cp := ‖scale • velocityCoefficient W D U V n‖
    frobenius (rotation (R 1)-rotationPolynomial W D n 1) ≤ rotationBudget n cr dr 1 ∧
      ‖v 1-velocityPolynomial W D U V n 1‖ ≤
        velocityBudget n cr dr cv dv ‖U‖ ‖U+V‖ 1 ∧
      ‖p 1-positionPolynomial W D U V scale n 1‖ ≤
        positionBudget n cr dr cv dv cp ‖U‖ ‖U+V‖ scale 1 := by
  let W := hat ω₀
  let D := hat ωs
  have hhat (t : ℝ) : hat (ω₀+t • ωs) = W+t • D := by
    simp [hat, W, D, skew_add, skew_smul, map_add, map_smul]
  apply polynomial_physical_defect_bound hscale n
    (frobenius ((n+1:ℕ) • rotationCoefficient W D (n+1)))
    (frobenius (rotationCoefficient W D n*D))
    ‖(n+1:ℕ) • velocityCoefficient W D U V (n+1)‖
    ‖rotationCoefficient W D n V‖ ‖scale • velocityCoefficient W D U V n‖ ‖U‖ ‖U+V‖
    R (rotationPolynomial W D n) (rotationDefect W D n)
    v (velocityPolynomial W D U V n) p (positionPolynomial W D U V scale n)
    (fun t => U+t • V) (velocityDefect W D U V n)
    (positionDefect W D U V scale n) (fun t => ω₀+t • ωs)
  · exact hR
  · intro t _
    convert rotation_polynomial_derivative W D n t using 1
    rw [hhat]
    dsimp [rotationDefect]
    module
  · exact hv
  · intro t _
    convert velocity_polynomial_derivative W D U V n t using 1
    dsimp [velocityDefect]
    module
  · exact hp
  · intro t _
    convert position_polynomial_derivative W D U V scale n t using 1
    dsimp [positionDefect]
    module
  · simpa only [rotationPolynomial, fohTaylor_initial] using hR0.symm
  · simp [velocityPolynomial, velocityCoefficient, polynomial_zero,
      integratedCoefficient, hv0]
  · simp [positionPolynomial, positionCoefficient, polynomial_zero,
      integratedCoefficient, hp0]
  · intro t ht
    simpa only [mul_comm] using rotation_defect_norm W D n ht.1
  · intro t ht
    simpa only [velocityDefect, mul_comm] using
      two_term_defect_norm ((n+1:ℕ) • velocityCoefficient W D U V (n+1))
        (rotationCoefficient W D n V) (pow_nonneg ht.1 n) (pow_nonneg ht.1 (n+1))
  · intro t ht
    simp only [positionDefect, norm_neg, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg ht.1 n)]
    exact le_of_eq (mul_comm _ _)
  · intro t ht
    exact affine_input_norm U V ht

end GNC.Preintegration.CenteredFoh.Defect.Sparse
