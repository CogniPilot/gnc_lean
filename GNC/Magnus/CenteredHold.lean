import GNC.Magnus.MagnusInputs
import GNC.Magnus.MagnusJet
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! The centered quadratic hold (Section V): the interpolating parabola
through three centered samples, Eq. (31); the rotation-channel increment
of Eq. (32) and its bias Jacobian, Eq. (33); the quadrature weights and
noise amplification factors of Theorem 5's honesty term; the trapezoid
noise weights of Section IV-D(ii); and the Simpson exactness on cubics
used by the process-noise integral of Section XIII. -/
noncomputable section
namespace GNC.Magnus
open Matrix Polynomial

/-! ### Eq. (31): centered differences and the centered quadratic hold -/

/-- Centered first difference `B = (up - um)/(2h)` of Eq. (31). -/
def centeredSlope (h : ℝ) (um _u up : Vec3) : Vec3 := (1/(2*h)) • (up - um)

/-- Centered second difference `C = (up - 2u + um)/(2h²)` of Eq. (31). -/
def centeredCurvature (h : ℝ) (um u up : Vec3) : Vec3 :=
  (1/(2*h^2)) • (up - (2:ℝ) • u + um)

/-- The centered quadratic hold `N(t) = A + tB + t²C` of Eq. (31) with `A = u`. -/
def centeredHold (h : ℝ) (um u up : Vec3) (t : ℝ) : Vec3 :=
  u + t • centeredSlope h um u up + t^2 • centeredCurvature h um u up

/-- The hold interpolates the earlier sample at `t = -h`. -/
theorem centeredHold_neg (h : ℝ) (hh : h ≠ 0) (um u up : Vec3) :
    centeredHold h um u up (-h) = um := by
  ext i
  simp only [centeredHold, centeredSlope, centeredCurvature, Pi.add_apply, Pi.smul_apply,
    Pi.sub_apply, smul_eq_mul]
  field_simp
  ring

/-- The hold interpolates the center sample at `t = 0`. -/
theorem centeredHold_zero (h : ℝ) (um u up : Vec3) :
    centeredHold h um u up 0 = u := by
  simp [centeredHold]

/-- The hold interpolates the later sample at `t = h`. -/
theorem centeredHold_pos (h : ℝ) (hh : h ≠ 0) (um u up : Vec3) :
    centeredHold h um u up h = up := by
  ext i
  simp only [centeredHold, centeredSlope, centeredCurvature, Pi.add_apply, Pi.smul_apply,
    Pi.sub_apply, smul_eq_mul]
  field_simp
  ring

/-- Proposition 7: the centered slope annihilates a constant bias. -/
theorem centeredSlope_bias (h : ℝ) (um u up b : Vec3) :
    centeredSlope h (um - b) (u - b) (up - b) = centeredSlope h um u up := by
  unfold centeredSlope
  have := (centered_bias_invariant h um u up b).1
  simpa only [one_div] using this

/-- Proposition 7: the centered curvature annihilates a constant bias. -/
theorem centeredCurvature_bias (h : ℝ) (um u up b : Vec3) :
    centeredCurvature h (um - b) (u - b) (up - b) = centeredCurvature h um u up := by
  unfold centeredCurvature
  have := (centered_bias_invariant h um u up b).2
  simpa only [one_div] using this

/-! ### Proposition 6, closing remark: `C = 0` recovers Theorem 1 -/

section Jet
variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- The FOH exponent of Theorem 1 through degree three. -/
def fohExponent3 (a b : A) : Polynomial A :=
  monomial 1 a + monomial 2 ((1/2:ℝ) • b) + monomial 3 ((1/12:ℝ) • comm a b)

theorem exponent5_zero_curvature_coeff_one (a b : A) :
    (exponent5 a b 0).coeff 1 = a := by
  simp [exponent5, Polynomial.coeff_monomial]

theorem exponent5_zero_curvature_coeff_two (a b : A) :
    (exponent5 a b 0).coeff 2 = (1/2:ℝ) • b := by
  simp [exponent5, Polynomial.coeff_monomial]

theorem exponent5_zero_curvature_coeff_three (a b : A) :
    (exponent5 a b 0).coeff 3 = (1/12:ℝ) • comm a b := by
  simp [exponent5, Polynomial.coeff_monomial]

/-- Proposition 6, closing remark: with `C = 0` the exponent of Eq. (32) agrees
with the FOH exponent of Theorem 1 in every coefficient through degree three. -/
theorem exponent5_zero_curvature_eq_foh (a b : A) (n : ℕ) (hn : n ≤ 3) :
    (exponent5 a b 0).coeff n = (fohExponent3 a b).coeff n := by
  interval_cases n <;> simp [exponent5, fohExponent3, Polynomial.coeff_monomial]

end Jet

/-! ### Proposition 7, Eq. (33): rotation-channel increment and bias Jacobian -/

/-- The rotation channel of Eq. (32) through the displayed brackets, with the
matrix commutators of `so(3)` written as cross products. -/
def centeredRotation (h : ℝ) (A B C : Vec3) : Vec3 :=
  h • A + (h^2/2) • B + (h^3/3) • C + (h^3/12) • (A ⨯₃ B) + (h^4/12) • (A ⨯₃ C) +
    (h^5/60) • (B ⨯₃ C)

/-- The rotation-channel increment assembled from three centered gyro samples. -/
def centeredRotationIncrement (h : ℝ) (ωm ω ωp : Vec3) : Vec3 :=
  centeredRotation h ω (centeredSlope h ωm ω ωp) (centeredCurvature h ωm ω ωp)

/-- The bias enters only through `A`: exact affine identity behind Eq. (33). -/
theorem centeredRotation_bias_affine (h : ℝ) (A B C b : Vec3) :
    centeredRotation h (A - b) B C = centeredRotation h A B C +
      (-h) • b + (h^3/12) • (B ⨯₃ b) + (h^4/12) • (C ⨯₃ b) := by
  ext i; fin_cases i <;> simp [centeredRotation, crossProduct, vecHead, vecTail] <;> ring

/-- Proposition 7: a constant gyro bias on all three samples shifts the
centered increment affinely, with `ωB` and `ωC` unchanged. -/
theorem centeredRotationIncrement_bias_affine (h : ℝ) (ωm ω ωp b : Vec3) :
    centeredRotationIncrement h (ωm - b) (ω - b) (ωp - b) =
      centeredRotationIncrement h ωm ω ωp + (-h) • b +
        (h^3/12) • (centeredSlope h ωm ω ωp ⨯₃ b) +
        (h^4/12) • (centeredCurvature h ωm ω ωp ⨯₃ b) := by
  unfold centeredRotationIncrement
  rw [centeredSlope_bias, centeredCurvature_bias, centeredRotation_bias_affine]

/-- Eq. (33): the bias Jacobian acts as `-h I + (h³/12)[ωB]× + (h⁴/12)[ωC]×`. -/
theorem centeredRotation_bias_derivative (h : ℝ) (A B C b : Vec3) :
    HasDerivAt (fun s : ℝ => centeredRotation h (A - s • b) B C)
      ((-h) • b + (h^3/12) • (B ⨯₃ b) + (h^4/12) • (C ⨯₃ b)) 0 := by
  have he : (fun s : ℝ => centeredRotation h (A - s • b) B C) =
      fun s => centeredRotation h A B C +
        s • ((-h) • b + (h^3/12) • (B ⨯₃ b) + (h^4/12) • (C ⨯₃ b)) := by
    funext s; rw [centeredRotation_bias_affine]
    ext i; fin_cases i <;> simp [crossProduct, vecHead, vecTail] <;> ring
  rw [he]
  simpa only [one_smul] using ((hasDerivAt_id (0:ℝ)).smul_const
    ((-h) • b + (h^3/12) • (B ⨯₃ b) + (h^4/12) • (C ⨯₃ b))).const_add
    (centeredRotation h A B C)

/-- Eq. (33) for the increment assembled from the three biased gyro samples. -/
theorem centeredRotationIncrement_bias_derivative (h : ℝ) (ωm ω ωp b : Vec3) :
    HasDerivAt (fun s : ℝ => centeredRotationIncrement h (ωm - s • b) (ω - s • b) (ωp - s • b))
      ((-h) • b + (h^3/12) • (centeredSlope h ωm ω ωp ⨯₃ b) +
        (h^4/12) • (centeredCurvature h ωm ω ωp ⨯₃ b)) 0 := by
  have he : (fun s : ℝ => centeredRotationIncrement h (ωm - s • b) (ω - s • b) (ωp - s • b)) =
      fun s => centeredRotation h (ω - s • b) (centeredSlope h ωm ω ωp)
        (centeredCurvature h ωm ω ωp) := by
    funext s
    unfold centeredRotationIncrement
    rw [centeredSlope_bias, centeredCurvature_bias]
  rw [he]
  exact centeredRotation_bias_derivative h ω _ _ b

/-! ### Polynomial interval integrals -/

/-- The integral of a cubic over `[0, d]`. -/
theorem integral_cubic (c0 c1 c2 c3 d : ℝ) :
    ∫ s in (0:ℝ)..d, (c0 + c1*s + c2*s^2 + c3*s^3) =
      c0*d + c1*d^2/2 + c2*d^3/3 + c3*d^4/4 := by
  rw [intervalIntegral.integral_add, intervalIntegral.integral_add,
    intervalIntegral.integral_add, intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_id, integral_pow, integral_pow]
  · simp; ring
  all_goals (apply Continuous.intervalIntegrable; fun_prop)

/-- Theorem 5 (noise term): the integral of a quadratic over `[0, h]`. -/
theorem integral_quadratic (A B C h : ℝ) :
    ∫ t in (0:ℝ)..h, (A + B*t + C*t^2) = h*A + h^2/2*B + h^3/3*C := by
  have := integral_cubic A B C 0 h
  simp only [zero_mul, add_zero] at this
  rw [this]; ring

/-- Theorem 5 (noise term), scalar form: the centered quadratic hold integrates
to the weights `(2/3, 5/12, -1/12)` on `(u, up, um)`. -/
theorem integral_centeredHold_real (h : ℝ) (hh : h ≠ 0) (um u up : ℝ) :
    ∫ t in (0:ℝ)..h, (u + t*((up - um)/(2*h)) + t^2*((up - 2*u + um)/(2*h^2))) =
      h*((2/3)*u + (5/12)*up - (1/12)*um) := by
  have := integral_quadratic u ((up - um)/(2*h)) ((up - 2*u + um)/(2*h^2)) h
  simp only [mul_comm _ (_ : ℝ)] at this ⊢
  rw [this]
  field_simp
  ring

/-- Theorem 5 (noise term), vector form: the per-interval increment of the
centered quadratic hold carries the weights `(2/3, 5/12, -1/12)`. -/
theorem integral_centeredHold (h : ℝ) (hh : h ≠ 0) (um u up : Vec3) :
    ∫ t in (0:ℝ)..h, centeredHold h um u up t =
      h • ((2/3:ℝ) • u + (5/12:ℝ) • up - (1/12:ℝ) • um) := by
  simp only [centeredHold]
  rw [intervalIntegral.integral_add, intervalIntegral.integral_add,
    intervalIntegral.integral_const, intervalIntegral.integral_smul_const,
    intervalIntegral.integral_smul_const, integral_id, integral_pow]
  · ext i
    simp only [centeredSlope, centeredCurvature, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul]
    push_cast
    field_simp
    ring
  all_goals (apply Continuous.intervalIntegrable; fun_prop)

/-! ### Theorem 5 (noise term): weight sums of squares -/

/-- Centered quadratic weights: `(2/3)² + (5/12)² + (1/12)² = 5/8`. -/
theorem centered_weight_variance : (2/3:ℝ)^2 + (5/12)^2 + (1/12)^2 = 5/8 := by norm_num

/-- Trapezoid (FOH) weights: `(1/2)² + (1/2)² = 1/2`. -/
theorem trapezoid_weight_variance : (1/2:ℝ)^2 + (1/2)^2 = 1/2 := by norm_num

/-- FOH slope estimator: `Var(B_FOH) = 2σ²/h²`. -/
theorem foh_slope_variance (h : ℝ) : (1/h:ℝ)^2 + (1/h)^2 = 2/h^2 := by
  ring

/-- Centered slope estimator: `Var(B_centered) = σ²/(2h²)`, four times smaller. -/
theorem centered_slope_variance (h : ℝ) : (1/(2*h):ℝ)^2 + (1/(2*h))^2 = 1/(2*h^2) := by
  ring

/-- Centered curvature estimator: `Var(C) = 3σ²/(2h⁴)`. -/
theorem centered_curvature_variance (h : ℝ) :
    (1/(2*h^2):ℝ)^2 + (2/(2*h^2))^2 + (1/(2*h^2))^2 = 3/(2*h^4) := by
  ring

/-- The ratio of the two slope variances is exactly four. -/
theorem slope_variance_ratio (h : ℝ) (hh : h ≠ 0) :
    (2/h^2) / (1/(2*h^2)) = (4:ℝ) := by
  field_simp
  norm_num

/-! ### Section IV-D(ii): trapezoid noise correlation -/

/-- Per-interval trapezoid noise weights `h/2, h/2`: variance `h²σ²/2`. -/
theorem trapezoid_interval_variance (h : ℝ) : (h/2)^2 + (h/2)^2 = h^2/2 := by ring

/-- Adjacent intervals share one endpoint sample: cross-covariance `h²σ²/4`,
correlation coefficient exactly `1/2`. -/
theorem trapezoid_cross_covariance (h : ℝ) (hh : h ≠ 0) :
    (h/2)*(h/2) = h^2/4 ∧ (h^2/4) / (h^2/2) = (1/2:ℝ) := by
  constructor
  · ring
  · field_simp; ring

/-- The telescoped sum of `K` trapezoid increments,
`∑ h(n_k + n_{k+1})/2 = h(n_0/2 + n_1 + ⋯ + n_{K-1} + n_K/2)`. -/
theorem trapezoid_telescope (h : ℝ) (n : ℕ → ℝ) (K : ℕ) (hK : 1 ≤ K) :
    ∑ k ∈ Finset.range K, h*(n k + n (k+1))/2 =
      h*((1/2)*n 0 + (∑ k ∈ Finset.Ico 1 K, n k) + (1/2)*n K) := by
  induction K, hK using Nat.le_induction with
  | base => simp; ring
  | succ K hK ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_Ico_succ_top hK]
    ring

/-- The telescoped weights `(1/2, 1, …, 1, 1/2)` over `K` intervals have squared
sum `K - 1/2`, so the accumulated variance is `(K - 1/2)h²σ²`. -/
theorem trapezoid_telescope_variance (K : ℕ) :
    (1/2:ℝ)^2 + ((K:ℝ) - 1)*1 + (1/2)^2 = (K:ℝ) - 1/2 := by
  ring

/-- The squared telescoped weights as a sum over the `K+1` samples. -/
theorem trapezoid_telescope_variance_sum (K : ℕ) (hK : 1 ≤ K) :
    (1/2:ℝ)^2 + (∑ _k ∈ Finset.Ico 1 K, (1:ℝ)^2) + (1/2)^2 = (K:ℝ) - 1/2 := by
  simp only [one_pow, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one]
  rw [Nat.cast_sub hK]
  norm_num
  ring

/-! ### The 12 percent noise penalty -/

/-- The standard-deviation ratio of the centered to the trapezoid increment is
`√(5/8)/√(1/2) = √(5/4)`. -/
theorem noise_penalty_ratio : Real.sqrt (5/8) / Real.sqrt (1/2) = Real.sqrt (5/4) := by
  rw [← Real.sqrt_div (by norm_num)]
  norm_num

/-- `√(5/4)` lies between `1.11` and `1.12`: the 12 percent penalty. -/
theorem noise_penalty_bounds : (1.11:ℝ) < Real.sqrt (5/4) ∧ Real.sqrt (5/4) < 1.12 := by
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

/-- The absolute increase `√(5/8) - √(1/2)` lies between `0.083` and `0.084`. -/
theorem noise_crossover_bounds :
    (0.083:ℝ) < Real.sqrt (5/8) - Real.sqrt (1/2) ∧
      Real.sqrt (5/8) - Real.sqrt (1/2) < 0.084 := by
  have h1 : (0.79056:ℝ) < Real.sqrt (5/8) := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h2 : Real.sqrt (5/8) < (0.79057:ℝ) := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have h3 : (0.7071:ℝ) < Real.sqrt (1/2) := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h4 : Real.sqrt (1/2) < (0.70711:ℝ) := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  constructor <;> linarith

/-! ### Section XIII: Simpson quadrature is exact on cubics -/

/-- A cubic polynomial in the variable `s`. -/
def cubic (c0 c1 c2 c3 : ℝ) (s : ℝ) : ℝ := c0 + c1*s + c2*s^2 + c3*s^3

/-- Simpson's rule on the nodes `{0, d/2, d}` integrates every cubic exactly,
which is why the process-noise integral of Section XIII has only an `O(dt⁵)`
quadrature error against the third-order transition. -/
theorem simpson_exact_cubic (c0 c1 c2 c3 d : ℝ) :
    ∫ s in (0:ℝ)..d, cubic c0 c1 c2 c3 s =
      d/6 * (cubic c0 c1 c2 c3 0 + 4 * cubic c0 c1 c2 c3 (d/2) + cubic c0 c1 c2 c3 d) := by
  unfold cubic
  rw [integral_cubic]
  ring

end GNC.Magnus
