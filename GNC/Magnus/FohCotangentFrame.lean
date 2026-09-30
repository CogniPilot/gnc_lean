import GNC.Magnus.FohQuaternionLogSlope
import GNC.Magnus.FohQuaternionRotation
import GNC.Magnus.FohWeberFlow
import GNC.Lie.ExponentialCoordinates

/-! Fixed-frame assembly of actual cotangent slope variations.
The supplied quaternion family solves the original canonical time ODE;
no parameter derivative or target remainder is assumed.
-/
noncomputable section
open Set Filter Matrix
open scoped Topology Quaternion Matrix Matrix.Norms.Operator
namespace GNC.Magnus

def fohQuaternionVec : ℍ →ₗ[ℝ] Vec3 where
  toFun q := ![q.imI, q.imJ, q.imK]
  map_add' q r := by ext i; fin_cases i <;> simp
  map_smul' a q := by ext i; fin_cases i <;> simp

def fohQuaternionVecCLM : ℍ →L[ℝ] Vec3 := fohQuaternionVec.toContinuousLinearMap

@[simp] theorem fohQuaternionVec_fohQ (a b c d : ℝ) :
    fohQuaternionVec (fohQ a b c d) = ![b,c,d] := rfl

def fohFrameQuaternionLog (C : SO3) (q : ℍ) : Vec3 :=
  rotate C (fohQuaternionVec (fohQuaternionRotationVector q))

def fohFrameQuaternionLogLinear (C : SO3) : ℍ →L[ℝ] Vec3 :=
  (Matrix.toLin' C.val).toContinuousLinearMap.comp fohQuaternionVecCLM

theorem fohFrameQuaternionLogLinear_apply (C : SO3) (q : ℍ) :
    fohFrameQuaternionLogLinear C q = rotate C (fohQuaternionVec q) := rfl

set_option maxHeartbeats 2000000 in
/-- The quaternion chart is an actual rotation logarithm, not merely a
coordinate expression having the desired derivatives. -/
theorem foh_quaternion_chart_rotation (q : ℍ) (hn : Quaternion.normSq q = 1)
    (ha : -1 < q.re) (hb : q.re < 1) :
    (rotationExp (fohQuaternionVec (fohQuaternionRotationVector q))).val =
      fohQuaternionMatrix q.re (fohQuaternionVec q) := by
  let r := Real.sqrt (1-q.re^2)
  let z := Real.arccos q.re
  have hr : 0 < r := Real.sqrt_pos.mpr (by nlinarith)
  have hz : 0 < z := Real.arccos_pos.mpr hb
  have hrsq : r^2 = 1-q.re^2 := Real.sq_sqrt (by nlinarith)
  have hv : lengthSq (fohQuaternionVec q) = 1-q.re^2 := by
    simp [Quaternion.normSq_def'] at hn
    simp [fohQuaternionVec, lengthSq]
    linarith
  have hvn : enorm (fohQuaternionVec q) = r := by
    have hh := enorm_sq (fohQuaternionVec q)
    rw [hv] at hh
    nlinarith [enorm_nonneg (fohQuaternionVec q)]
  have hphi : fohQuaternionVec (fohQuaternionRotationVector q) =
      (2*z/r) • fohQuaternionVec q := by
    ext i
    fin_cases i <;> simp [fohQuaternionVec, fohQuaternionRotationVector,
      fohQuaternionLogScale, r, z]
  have hnorm : enorm (fohQuaternionVec (fohQuaternionRotationVector q)) = 2*z := by
    rw [hphi, enorm_smul, hvn, abs_of_pos (by positivity : 0 < 2*z/r)]
    field_simp
  have hs : Real.sin (2*z) = 2*r*q.re := by
    rw [Real.sin_two_mul]
    simp [z, r, Real.sin_arccos, Real.cos_arccos ha.le hb.le]
  have hc : Real.cos (2*z) = 2*q.re^2-1 := by
    rw [Real.cos_two_mul]
    simp [z, Real.cos_arccos ha.le hb.le]
  rw [rotationExp_formula, hnorm, hphi, skew_smul, smul_pow, smul_smul, smul_smul]
  have h1 : (Real.sin (2*z)/(2*z)) * (2*z/r) = 2*q.re := by
    rw [hs]
    field_simp
  have h2 : ((1-Real.cos (2*z))/(2*z)^2) * (2*z/r)^2 = 2 := by
    rw [hc]
    field_simp
    nlinarith
  rw [h1, h2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fohQuaternionMatrix, fohQuaternionVec, lengthSq, skew, pow_two,
      Matrix.mul_apply, Fin.sum_univ_succ, vecMulVec] <;>
    nlinarith [show q.re^2 + q.imI^2 + q.imJ^2 + q.imK^2 = 1 by
      simpa [Quaternion.normSq_def'] using hn]

theorem foh_rotationExp_frame (C : SO3) (x : Vec3) :
    (rotationExp (rotate C x)).val = C.val * (rotationExp x).val * C⁻¹.val := by
  let U : (Matrix (Fin 3) (Fin 3) ℝ)ˣ :=
    { val := C.val
      inv := C⁻¹.val
      val_inv := by change (C*C⁻¹).val = (1 : SO3).val; simp
      inv_val := by change (C⁻¹*C).val = (1 : SO3).val; simp }
  have hs : skew (rotate C x) = C.val * skew x * C⁻¹.val := by
    have hh := congrArg (fun M => M * C⁻¹.val) (skew_rotate C x)
    have hi : C.val * C⁻¹.val = 1 := U.val_inv
    simpa only [Matrix.mul_assoc, hi, Matrix.mul_one] using hh
  change NormedSpace.exp (skew (rotate C x)) = _
  rw [hs]
  exact NormedSpace.exp_units_conj U (skew x)

/-- Projecting the actual quaternion ODE gives the real quaternion kinematics. -/
theorem fohQuaternion_components_ode (q : ℝ → ℍ) (w : Vec3) {t : ℝ}
    (hq : HasDerivAt q (q t * fohQ 0 (w 0/2) (w 1/2) (w 2/2)) t) :
    HasDerivAt (fun s => (q s).re) (-(fohQuaternionVec (q t) ⬝ᵥ w)/2) t ∧
    HasDerivAt (fun s => fohQuaternionVec (q s))
      ((1/2 : ℝ) • ((q t).re • w + fohQuaternionVec (q t) ⨯₃ w)) t := by
  constructor
  · have hh := fohQuaternionReCLM.hasFDerivAt.comp_hasDerivAt t hq
    change HasDerivAt (fun s => (q s).re)
      (q t * fohQ 0 (w 0/2) (w 1/2) (w 2/2)).re t at hh
    convert hh using 1
    simp [fohQ, fohQuaternionVec, dotProduct, Fin.sum_univ_succ]
    ring
  · convert fohQuaternionVecCLM.hasFDerivAt.comp_hasDerivAt t hq using 1
    ext i
    fin_cases i <;>
      simp [fohQuaternionVecCLM, fohQuaternionVec, fohQ, cross_apply,
        Matrix.vecHead, Matrix.vecTail] <;> ring

theorem foh_canonical_quaternion_to_rotation (θ u v : ℝ) (q : ℝ → ℝ → ℍˣ)
    (hq : ∀ e t, HasDerivAt (fun s => (q e s).val)
      ((q e t).val * (fohQ 0 0 0 (θ/2) + e • fohQuaternionSlopeInput u v t)) t)
    (hq0 : ∀ e, q e 0 = 1) (e : ℝ) :
    ∃ R : ℝ → SO3, R 0 = 1 ∧
      (∀ t, (R t).val = fohQuaternionMatrix (q e t).val.re (fohQuaternionVec (q e t).val)) ∧
      (∀ t, HasDerivAt (fun s => (R s).val)
        ((R t).val * skew (![0,0,θ] + e • ((t-1/2) • (![u,0,v] : Vec3)))) t) := by
  have hd (t : ℝ) := fohQuaternion_components_ode (fun t => (q e t).val)
    (![0,0,θ] + e • ((t-1/2) • (![u,0,v] : Vec3))) (t := t) (by
      convert hq e t using 1
      congr 1
      ext <;> simp [fohQ, fohQuaternionSlopeInput] <;> ring)
  exact foh_quaternion_to_rotation (fun t => (q e t).val.re)
    (fun t => fohQuaternionVec (q e t).val)
    (fun t => ![0,0,θ] + e • ((t-1/2) • (![u,0,v] : Vec3)))
    (fun t => (hd t).1) (fun t => (hd t).2) (by simp [hq0]) (by simp [hq0, fohQuaternionVec])

/-- The same canonical quaternion solution represents any supplied physical
SO(3) solution after a fixed frame change. Equality follows from ODE uniqueness. -/
theorem foh_cot_frame_actual_rotation (C : SO3) (F G : Vec3) (θ u v : ℝ)
    (hF : F = rotate C ![0,0,θ]) (hG : G = rotate C ![u,0,v])
    (q : ℝ → ℝ → ℍˣ) (R : ℝ → ℝ → SO3)
    (hq : ∀ e t, HasDerivAt (fun s => (q e s).val)
      ((q e t).val * (fohQ 0 0 0 (θ/2) + e • fohQuaternionSlopeInput u v t)) t)
    (hq0 : ∀ e, q e 0 = 1)
    (hR : ∀ e t, HasDerivAt (fun s => (R e s).val)
      ((R e t).val * skew (F + e • ((t-1/2) • G))) t)
    (hR0 : ∀ e, R e 0 = 1) (e t : ℝ) :
    (R e t).val = C.val *
      fohQuaternionMatrix (q e t).val.re (fohQuaternionVec (q e t).val) * C⁻¹.val := by
  obtain ⟨S, hs0, hsf, hsd⟩ := foh_canonical_quaternion_to_rotation θ u v q hq hq0 e
  have hd (t : ℝ) : HasDerivAt (fun s => (C * S s * C⁻¹).val)
      ((C * S t * C⁻¹).val * skew (F + e • ((t-1/2) • G))) t := by
    convert foh_conjugate_rotation_derivative C S _ (hsd t) using 1
    simp only [hF, hG, rotate, Matrix.mulVec_add, Matrix.mulVec_smul]
  have he := foh_rotation_ode_unique (R e) (fun t => C * S t * C⁻¹)
    (fun t => F + e • ((t-1/2) • G)) (hR e) hd (by simp [hR0, hs0])
  rw [congrFun he t]
  change C.val * (S t).val * C⁻¹.val = _
  rw [hsf]

theorem foh_cot_frame_first_coefficient (C : SO3) (F G : Vec3) (θ u v : ℝ)
    (hF : F = rotate C ![0,0,θ]) (hG : G = rotate C ![u,0,v]) :
    rotate C ![0,θ*u*fohCotC θ,0] = fohCotC θ • (F ⨯₃ G) := by
  rw [hF, hG, ← rotate_cross, ← rotate_smul]
  congr 1
  ext i
  fin_cases i <;> simp [cross_apply, Matrix.vecHead, Matrix.vecTail] <;> ring

theorem foh_cot_frame_second_coefficient (C : SO3) (F G : Vec3)
    {θ : ℝ} (hθ : θ ≠ 0) (u v : ℝ)
    (hF : F = rotate C ![0,0,θ]) (hG : G = rotate C ![u,0,v]) :
    rotate C ![θ*u*v*fohCotBeta θ,0,θ*u^2*fohCotAlpha θ] =
      (fohCotAlpha θ*lengthSq G+fohCotGamma θ*(F ⬝ᵥ G)^2) • F +
      (fohCotBeta θ*(F ⬝ᵥ G)) • G := by
  rw [hF, hG, foh_log_quadratic_rotation_equivariant,
    foh_log_canonical_quadratic_vec hθ]

/-- Arbitrary fixed-frame first variation of the explicit quaternion log chart. -/
theorem foh_cot_frame_actual_first (C : SO3) (F G : Vec3)
    {θ : ℝ} (hθ : 0 < θ) (hπ : θ < 2*Real.pi) (u v : ℝ)
    (hF : F = rotate C ![0,0,θ]) (hG : G = rotate C ![u,0,v])
    (q : ℝ → ℝ → ℍˣ)
    (hq : ∀ e t, HasDerivAt (fun s => (q e s).val)
      ((q e t).val * (fohQ 0 0 0 (θ/2) + e • fohQuaternionSlopeInput u v t)) t)
    (hq0 : ∀ e, q e 0 = 1) :
    HasDerivAt (fun e => fohFrameQuaternionLog C (q e 1).val)
      (fohCotC θ • (F ⨯₃ G)) 0 := by
  have hh := (fohFrameQuaternionLogLinear C).hasFDerivAt.comp_hasDerivAt 0
    (fohQuaternion_actual_log_cot_first hθ hπ u v q hq hq0)
  simpa only [fohFrameQuaternionLogLinear_apply, fohQuaternionVec_fohQ,
    foh_cot_frame_first_coefficient C F G θ u v hF hG] using hh

/-- Actual Peano second coefficient transported to the invariant three-vector
formula. The remainder is a limit proved from the supplied time ODE. -/
theorem foh_cot_frame_actual_second (C : SO3) (F G : Vec3)
    {θ : ℝ} (hθ : 0 < θ) (hπ : θ < 2*Real.pi) (u v : ℝ)
    (hF : F = rotate C ![0,0,θ]) (hG : G = rotate C ![u,0,v])
    (q : ℝ → ℝ → ℍˣ)
    (hq : ∀ e t, HasDerivAt (fun s => (q e s).val)
      ((q e t).val * (fohQ 0 0 0 (θ/2) + e • fohQuaternionSlopeInput u v t)) t)
    (hq0 : ∀ e, q e 0 = 1) :
    Tendsto (fun e : ℝ => (e^2)⁻¹ •
      (fohFrameQuaternionLog C (q e 1).val - F -
        e • (fohCotC θ • (F ⨯₃ G)))) (𝓝[≠] 0)
      (𝓝 ((fohCotAlpha θ*lengthSq G+fohCotGamma θ*(F ⬝ᵥ G)^2) • F +
        (fohCotBeta θ*(F ⬝ᵥ G)) • G)) := by
  have hh := ((fohFrameQuaternionLogLinear C).continuous.tendsto _).comp
    (fohQuaternion_actual_log_cot_second hθ hπ u v q hq hq0)
  simpa only [Function.comp_def, map_smul, map_sub, fohFrameQuaternionLogLinear_apply,
    fohQuaternionVec_fohQ, ← hF,
    foh_cot_frame_first_coefficient C F G θ u v hF hG,
    foh_cot_frame_second_coefficient C F G hθ.ne' u v hF hG] using hh

/-- End-to-end fixed-frame actual rotation logarithm and its first two slope
coefficients. The frame and actual canonical quaternion solution are explicit
hypotheses. The logarithm property and both parameter variations are conclusions;
in particular, no desired logarithm expansion is assumed.

The theorem uses an actual quaternion lift from the identity, so it also states
which continuous local logarithm branch is meant when θ exceeds π. -/
theorem foh_cot_frame_actual_log (C : SO3) (F G : Vec3)
    {θ : ℝ} (hθ : 0 < θ) (hπ : θ < 2*Real.pi) (u v : ℝ)
    (hF : F = rotate C ![0,0,θ]) (hG : G = rotate C ![u,0,v])
    (q : ℝ → ℝ → ℍˣ) (R : ℝ → ℝ → SO3)
    (hq : ∀ e t, HasDerivAt (fun s => (q e s).val)
      ((q e t).val * (fohQ 0 0 0 (θ/2) + e • fohQuaternionSlopeInput u v t)) t)
    (hq0 : ∀ e, q e 0 = 1)
    (hR : ∀ e t, HasDerivAt (fun s => (R e s).val)
      ((R e t).val * skew (F + e • ((t-1/2) • G))) t)
    (hR0 : ∀ e, R e 0 = 1) :
    let φ := fun e => fohFrameQuaternionLog C (q e 1).val
    φ 0 = F ∧
    (∀ᶠ e in 𝓝 (0 : ℝ), rotationExp (φ e) = R e 1) ∧
    HasDerivAt φ (fohCotC θ • (F ⨯₃ G)) 0 ∧
    Tendsto (fun e : ℝ => (e^2)⁻¹ • (φ e - F - e • (fohCotC θ • (F ⨯₃ G))))
      (𝓝[≠] 0) (𝓝 ((fohCotAlpha θ*lengthSq G+fohCotGamma θ*(F ⬝ᵥ G)^2) • F +
        (fohCotBeta θ*(F ⬝ᵥ G)) • G)) := by
  dsimp only
  refine ⟨?_, ?_, foh_cot_frame_actual_first C F G hθ hπ u v hF hG q hq hq0,
    foh_cot_frame_actual_second C F G hθ hπ u v hF hG q hq hq0⟩
  · rw [fohQuaternion_actual_base θ u v q hq hq0]
    unfold fohFrameQuaternionLog
    rw [(fohQuaternionLog_cot_coefficients hθ hπ u v).1, fohQuaternionVec_fohQ, ← hF]
  · have hqc := (foh_parameter_integral_hasDerivAt (fun _ => fohQ 0 0 0 (θ/2))
      (fohQuaternionSlopeInput u v) q continuous_const
      (fohQuaternionSlopeInput_continuous u v) hq hq0 (by norm_num : (0:ℝ) ≤ 1)).continuousAt
    have hrc : ContinuousAt (fun e => (q e 1).val.re) 0 :=
      Quaternion.continuous_re.continuousAt.comp hqc
    have hbase : (q 0 1).val.re = Real.cos (θ/2) := by
      rw [fohQuaternion_actual_base θ u v q hq hq0]
      simp [fohMeanQuaternion, fohQ]
    have hs : 0 < Real.sin (θ/2) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    have hlo : -1 < (q 0 1).val.re := by
      rw [hbase]
      nlinarith [Real.sin_sq_add_cos_sq (θ/2), Real.neg_one_le_cos (θ/2),
        Real.cos_le_one (θ/2), sq_pos_of_pos hs]
    have hhi : (q 0 1).val.re < 1 := by
      rw [hbase]
      nlinarith [Real.sin_sq_add_cos_sq (θ/2), Real.neg_one_le_cos (θ/2),
        Real.cos_le_one (θ/2), sq_pos_of_pos hs]
    filter_upwards [(tendsto_order.1 hrc).1 (-1) hlo,
      (tendsto_order.1 hrc).2 1 hhi] with e helo hehi
    apply Subtype.ext
    rw [fohFrameQuaternionLog, foh_rotationExp_frame,
      foh_quaternion_chart_rotation (q e 1).val
        (fohQuaternion_actual_normSq θ u v q hq hq0 e 1) helo hehi]
    exact (foh_cot_frame_actual_rotation C F G θ u v hF hG q R hq hq0 hR hR0 e 1).symm

end GNC.Magnus
