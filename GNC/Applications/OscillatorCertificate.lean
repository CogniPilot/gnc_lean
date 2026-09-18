import GNC.Analysis.ConstantSecondOrderBound
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic

/-! The harmonic-oscillator instance: a second field with nonzero curvature.
The true family `x_θ(τ) = cos(θ τ)` with uncertain frequency
`θ ∈ [4/3, 5/3]` is compared against the degree-six cosine truncation at
design frequency `3/2`. The curvature is `κ = 25/9`, so the supersolution's
curvature terms are active; every defect bound is rational arithmetic. -/
noncomputable section
namespace GNC.OscillatorCertificate
open Set PolynomialSupersolution

/-- True normalized response at frequency θ. -/
def xs (θ : ℝ) : ℝ → ℝ := fun t => Real.cos (θ * t)
/-- True velocity. -/
def vs (θ : ℝ) : ℝ → ℝ := fun t => -θ * Real.sin (θ * t)
/-- True acceleration. -/
def accel (θ : ℝ) : ℝ → ℝ := fun t => -θ^2 * Real.cos (θ * t)

/-- Degree-six cosine truncation at design frequency 3/2. -/
def q (t : ℝ) : ℝ := 1 - (9/8)*t^2 + (27/128)*t^4 - (81/5120)*t^6
/-- Its first derivative. -/
def qd (t : ℝ) : ℝ := -(9/4)*t + (27/32)*t^3 - (243/2560)*t^5
/-- Its second derivative. -/
def qdd (t : ℝ) : ℝ := -(9/4) + (81/32)*t^2 - (243/512)*t^4

/-- Prediction error position. -/
def err (θ : ℝ) : ℝ → ℝ := fun t => xs θ t - q t
/-- Prediction error velocity. -/
def verr (θ : ℝ) : ℝ → ℝ := fun t => vs θ t - qd t
/-- Prediction error acceleration. -/
def aerr (θ : ℝ) : ℝ → ℝ := fun t => accel θ t - qdd t

theorem xs_hasDeriv (θ t : ℝ) : HasDerivAt (xs θ) (vs θ t) t := by
  show HasDerivAt (fun t => Real.cos (θ * t)) (vs θ t) t
  have h : HasDerivAt (fun s : ℝ => θ * s) θ t := by
    simpa using (hasDerivAt_id t).const_mul θ
  have h2 := (Real.hasDerivAt_cos (θ * t)).comp t h
  simpa [vs, mul_comm, mul_neg, neg_mul, Function.comp_apply] using h2

theorem vs_hasDeriv (θ t : ℝ) : HasDerivAt (vs θ) (accel θ t) t := by
  show HasDerivAt (fun t => -θ * Real.sin (θ * t)) (accel θ t) t
  have h : HasDerivAt (fun s : ℝ => θ * s) θ t := by
    simpa using (hasDerivAt_id t).const_mul θ
  have h2 := ((Real.hasDerivAt_sin (θ * t)).comp t h).const_mul (-θ)
  simpa [accel, mul_assoc, mul_comm, pow_two, neg_mul, mul_neg,
    Function.comp_apply] using h2

theorem q_hasDeriv (t : ℝ) : HasDerivAt q (qd t) t := by
  unfold q qd
  exact (((hasDerivAt_const t (1:ℝ)).sub
    (((hasDerivAt_pow 2 t)).const_mul (9/8))).add
    (((hasDerivAt_pow 4 t)).const_mul (27/128))).sub
    (((hasDerivAt_pow 6 t)).const_mul (81/5120)) |>.congr_deriv (by ring)

theorem qd_hasDeriv (t : ℝ) : HasDerivAt qd (qdd t) t := by
  unfold qd qdd
  exact ((((hasDerivAt_id t).const_mul (-(9/4))).add
    (((hasDerivAt_pow 3 t)).const_mul (27/32))).sub
    (((hasDerivAt_pow 5 t)).const_mul (243/2560))) |>.congr_deriv (by ring)

theorem err_hasDeriv (θ t : ℝ) : HasDerivAt (err θ) (verr θ t) t := by
  show HasDerivAt (fun t => xs θ t - q t) (vs θ t - qd t) t
  exact (xs_hasDeriv θ t).sub (q_hasDeriv t)

theorem verr_hasDeriv (θ t : ℝ) : HasDerivAt (verr θ) (aerr θ t) t := by
  show HasDerivAt (fun t => vs θ t - qd t) (accel θ t - qdd t) t
  exact (vs_hasDeriv θ t).sub (qd_hasDeriv t)

theorem q_continuous : Continuous q := by
  show Continuous fun t : ℝ => 1 - (9/8)*t^2 + (27/128)*t^4 - (81/5120)*t^6
  exact (((continuous_const.sub (continuous_const.mul (continuous_id.pow 2))).add
    (continuous_const.mul (continuous_id.pow 4))).sub
    (continuous_const.mul (continuous_id.pow 6)))

theorem qd_continuous : Continuous qd := by
  show Continuous fun t : ℝ => -(9/4)*t + (27/32)*t^3 - (243/2560)*t^5
  exact (((continuous_const.mul continuous_id).add
    (continuous_const.mul (continuous_id.pow 3))).sub
    (continuous_const.mul (continuous_id.pow 5)))

theorem err_continuous (θ : ℝ) : Continuous (err θ) := by
  show Continuous (fun t => Real.cos (θ * t) - q t)
  exact (Real.continuous_cos.comp (continuous_const.mul continuous_id)).sub
    q_continuous

theorem verr_continuous (θ : ℝ) : Continuous (verr θ) := by
  show Continuous (fun t => -θ * Real.sin (θ * t) - qd t)
  exact (continuous_const.mul
    (Real.continuous_sin.comp (continuous_const.mul continuous_id))).sub
    qd_continuous

theorem err_zero (θ : ℝ) : err θ 0 = 0 := by
  simp [err, xs, q]

theorem verr_zero (θ : ℝ) : verr θ 0 = 0 := by
  simp [verr, vs, qd]

/-- The truncation identity: q'' + (9/4) q = -(729/20480) τ^6. -/
theorem qdd_add_q (t : ℝ) : qdd t + (9/4) * q t = -(729/20480) * t^6 := by
  unfold q qdd; ring

/-- The candidate stays in [-1, 1] on the horizon. -/
theorem q_abs_le (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : |q t| ≤ 1 := by
  have ht0 : (0:ℝ) ≤ t := ht.1
  have ht2 : t^2 ≤ 1 := by nlinarith [ht0, ht.2]
  have ht4 : (0:ℝ) ≤ t^4 := pow_nonneg ht0 4
  have ht4le : t^4 ≤ 1 := by
    have h := mul_le_mul ht2 ht2 (sq_nonneg t) (by norm_num : (0:ℝ) ≤ 1)
    nlinarith [h]
  have ht6 : t^6 ≤ 1 := by
    have h := mul_le_mul ht4le ht2 (by positivity) (by norm_num : (0:ℝ) ≤ 1)
    nlinarith [h]
  have hB : -(9/8:ℝ) + (27/128)*t^2 - (81/5120)*t^4 ≤ 0 := by
    have h1 : (27/128:ℝ)*t^2 ≤ 27/128 :=
      calc (27/128:ℝ)*t^2 ≤ (27/128)*1 := mul_le_mul_of_nonneg_left ht2 (by norm_num)
        _ = 27/128 := mul_one _
    nlinarith [ht4]
  have hup : q t ≤ 1 := by
    have hprod : t^2 * (-(9/8) + (27/128)*t^2 - (81/5120)*t^4) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sq_nonneg t) hB
    unfold q
    nlinarith [hprod]
  have hlo : -1 ≤ q t := by
    unfold q
    nlinarith [ht2, ht6, ht4]
  exact abs_le.mpr ⟨hlo, hup⟩

/-- The frequency-mismatch factor over the family. -/
theorem freq_sq_dev {θ : ℝ} (hθ : θ ∈ Icc (4/3 : ℝ) (5/3)) :
    |θ^2 - 9/4| ≤ 19/36 := by
  obtain ⟨h1, h2⟩ := hθ
  have hlo : (16/9 : ℝ) ≤ θ^2 := by nlinarith [h1]
  have hhi : θ^2 ≤ 25/9 := by nlinarith [h1, h2]
  rw [abs_le]
  constructor <;> nlinarith

/-- The defect bound: model truncation plus frequency mismatch. -/
theorem defect_bound {θ : ℝ} (hθ : θ ∈ Icc (4/3 : ℝ) (5/3))
    (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
    |θ^2 * q t + qdd t| ≤ 5634/10000 := by
  have hq := q_abs_le t ht
  have hf := freq_sq_dev hθ
  have h1 : qdd t = -(729/20480) * t^6 - (9/4) * q t := by
    have h := qdd_add_q t; linarith
  have hsplit : θ^2 * q t + qdd t = (θ^2 - 9/4) * q t + (-(729/20480) * t^6) := by
    rw [h1]; ring
  rw [hsplit]
  have ht2 : t^2 ≤ 1 := by nlinarith [ht.1, ht.2]
  have ht4 : t^4 ≤ 1 := by
    have h := mul_le_mul ht2 ht2 (sq_nonneg t) (by norm_num : (0:ℝ) ≤ 1)
    nlinarith [h]
  have ht6 : (0:ℝ) ≤ t^6 ∧ t^6 ≤ 1 := by
    refine ⟨by positivity, ?_⟩
    have h := mul_le_mul ht4 ht2 (by positivity) (by norm_num : (0:ℝ) ≤ 1)
    nlinarith [h]
  have h2 : |-(729/20480 : ℝ) * t^6| ≤ 729/20480 := by
    rw [abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 729/20480),
      abs_of_nonneg ht6.1]
    calc (729/20480 : ℝ) * t^6 ≤ (729/20480) * 1 :=
        mul_le_mul_of_nonneg_left ht6.2 (by norm_num)
      _ = 729/20480 := mul_one _
  have h3 : |(θ^2 - 9/4) * q t| ≤ (19/36) * 1 := by
    rw [abs_mul]
    exact mul_le_mul hf hq (abs_nonneg _) (by norm_num)
  calc |(θ^2 - 9/4) * q t + (-(729/20480) * t^6)|
      ≤ |(θ^2 - 9/4) * q t| + |-(729/20480) * t^6| := abs_add_le _ _
    _ ≤ (19/36) * 1 + 729/20480 := by linarith
    _ ≤ 5634/10000 := by norm_num

/-- The curvature/defect inequality for the certificate. -/
theorem acceleration_bound {θ : ℝ} (hθ : θ ∈ Icc (4/3 : ℝ) (5/3))
    (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
    |aerr θ t| ≤ (25/9) * |err θ t| + 5634/10000 := by
  have hrewrite : aerr θ t = -θ^2 * err θ t + (-(θ^2) * q t - qdd t) := by
    unfold aerr accel err xs; ring
  rw [hrewrite]
  have hθ2 : θ^2 ≤ 25/9 := by have h1 := hθ.1; have h2 := hθ.2; nlinarith
  have h1 : |-θ^2 * err θ t| ≤ (25/9) * |err θ t| := by
    rw [abs_mul, abs_neg, abs_pow, sq_abs]
    exact mul_le_mul_of_nonneg_right hθ2 (abs_nonneg _)
  have h2 : |-(θ^2) * q t - qdd t| = |θ^2 * q t + qdd t| := by
    rw [show (-(θ^2) * q t - qdd t) = -(θ^2 * q t + qdd t) by ring, abs_neg]
  have hd := defect_bound hθ t ht
  calc |-θ^2 * err θ t + (-(θ^2) * q t - qdd t)|
      ≤ |-θ^2 * err θ t| + |-(θ^2) * q t - qdd t| := abs_add_le _ _
    _ ≤ (25/9) * |err θ t| + 5634/10000 := by linarith [h1, h2 ▸ hd]

/-- The harmonic-family certificate at curvature κ = 25/9. -/
theorem oscillator_certificate {θ : ℝ} (hθ : θ ∈ Icc (4/3 : ℝ) (5/3))
    (t : ℝ) (ht : t ∈ Icc 0 1) :
    |err θ t| ≤ (5634/10000) * value (25/9) t ∧
      |verr θ t| ≤ (5634/10000) * velocity (25/9) t := by
  have h := ConstantSecondOrderBound.response (err θ) (verr θ) (aerr θ)
    (κ := 25/9) (F := 5634/10000) (by norm_num) (by norm_num) (by norm_num)
    (err_continuous θ) (verr_continuous θ)
    (fun s _ => err_hasDeriv θ s) (fun s _ => verr_hasDeriv θ s)
    (err_zero θ) (verr_zero θ) (by
      intro s hs
      simpa [Real.norm_eq_abs] using acceleration_bound hθ s hs)
  simpa [Real.norm_eq_abs] using h t ht

theorem value_at_one : value (25/9) 1 =
    1/2 + (25/9)/24 + (25/9)^2/720 + (25/9)^3/(720*(56-25/9)) := by
  simp only [value, polynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, one_pow]
  norm_num

/-- Endpoint: position error is certified at 0.3533 after the horizon. -/
theorem oscillator_endpoint_position {θ : ℝ} (hθ : θ ∈ Icc (4/3 : ℝ) (5/3)) :
    |err θ 1| ≤ 3533/10000 := by
  have h := (oscillator_certificate hθ 1 ⟨by norm_num, le_rfl⟩).1
  refine h.trans ?_
  rw [value_at_one]
  norm_num

/-- Endpoint: velocity error is certified at 0.8631 after the horizon. -/
theorem oscillator_endpoint_velocity {θ : ℝ} (hθ : θ ∈ Icc (4/3 : ℝ) (5/3)) :
    |verr θ 1| ≤ 8631/10000 := by
  have h := (oscillator_certificate hθ 1 ⟨by norm_num, le_rfl⟩).2
  refine h.trans ?_
  have hv : velocity (25/9) 1 =
      1 + (25/9)/6 + (25/9)^2/120 + (25/9)^3/(90*(56-25/9)) := by
    simp only [velocity, polynomial, Polynomial.derivative_add,
      Polynomial.derivative_mul, Polynomial.derivative_C,
      Polynomial.derivative_pow, Polynomial.derivative_X, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_zero, Polynomial.eval_one,
      zero_mul, one_mul, zero_add, add_zero, mul_one, one_pow]
    norm_num
  rw [hv]
  norm_num

end GNC.OscillatorCertificate
