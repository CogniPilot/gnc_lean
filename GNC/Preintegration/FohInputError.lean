import GNC.Preintegration.CenteredFohBounds
import GNC.Analysis.HoldInterpolation
import Mathlib.Analysis.Calculus.Deriv.Star

/-! # Physical input-error bounds for inertial preintegration

Integration accuracy is relative to the specified input. This module bounds
the additional physical error when the actual gyro/accelerometer differ from
those inputs. The relative-rotation derivative is derived from the two actual
SO(3) ODEs. In particular, no exponential in the nominal angular rate occurs.
-/
noncomputable section
open Set
namespace GNC.Preintegration.CenteredFoh.InputError

theorem star_hat (q : Vec3) : star (hat q) = -hat q := by
  rw [hat, ← map_star]
  have hs : star (skew q) = -(skew q) := by
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      using skew_transpose q
  rw [hs, map_neg]

theorem rotation_star_mul (R : SO3) : star (rotation R) * rotation R = 1 := by
  have ho := (Matrix.mem_specialOrthogonalGroup_iff.mp R.property).1
  have hh := (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp ho
  have hs : star R.val * R.val = 1 := by
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      using hh
  simpa only [rotation, map_mul, map_star, map_one] using congrArg matrixOp hs

theorem rotation_mul_star (R : SO3) : rotation R * star (rotation R) = 1 := by
  have ho := (Matrix.mem_specialOrthogonalGroup_iff.mp R.property).1
  have hh := (Matrix.mem_orthogonalGroup_iff (Fin 3) ℝ).mp ho
  have hs : R.val * star R.val = 1 := by
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      using hh
  simpa only [rotation, map_mul, map_star, map_one] using congrArg matrixOp hs

theorem hat_sub (a b : Vec3) : hat (a-b) = hat a - hat b := by
  have hs : skew (a-b) = skew a - skew b := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [skew] <;> ring
  simp [hat, hs]

/-- The large common angular rate cancels before taking any norm. -/
theorem relative_derivative (R S : ℝ → SO3) (ω ωh : ℝ → Vec3) (t : ℝ)
    (hR : HasDerivAt (fun s => rotation (R s)) (rotation (R t) * hat (ω t)) t)
    (hS : HasDerivAt (fun s => rotation (S s)) (rotation (S t) * hat (ωh t)) t) :
    HasDerivAt (fun s => rotation (R s) * star (rotation (S s)))
      (rotation (R t) * hat (ω t - ωh t) * star (rotation (S t))) t := by
  convert hR.mul hS.star using 1
  rw [StarMul.star_mul (rotation (S t)) (hat (ωh t)), star_hat, hat_sub]
  noncomm_ring

theorem relative_rate_bound (R S : SO3) (q : Vec3) :
    ‖rotation R * hat q * star (rotation S)‖ ≤ enorm q := by
  calc
    _ ≤ ‖rotation R‖ * ‖hat q‖ * ‖star (rotation S)‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ = ‖hat q‖ := by rw [norm_star (rotation S), rotation_norm, rotation_norm]; ring
    _ ≤ _ := hat_norm_le q

/-- Integrate a scalar derivative majorant without a Gronwall factor. -/
theorem norm_le_primitive {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T : ℝ} (e ed : ℝ → E) (q qd : ℝ → ℝ)
    (hd : ∀ t ∈ Icc 0 T, HasDerivAt e (ed t) t)
    (hq : ∀ t : ℝ, HasDerivAt q (qd t) t)
    (h0 : e 0 = 0) (hq0 : q 0 = 0)
    (hb : ∀ t ∈ Icc 0 T, ‖ed t‖ ≤ qd t) :
    ∀ t ∈ Icc 0 T, ‖e t‖ ≤ q t := by
  apply image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hd t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (by simp [h0, hq0]) hq
  exact fun t ht => hb t (Ico_subset_Icc_self ht)

/-- Input-to-attitude bound, derived from the actual right-trivialized ODEs. -/
theorem attitude_input_bound {T : ℝ} (R S : ℝ → SO3) (ω ωh : ℝ → Vec3)
    (q b : ℝ → ℝ)
    (hR : ∀ t ∈ Icc 0 T,
      HasDerivAt (fun s => rotation (R s)) (rotation (R t) * hat (ω t)) t)
    (hS : ∀ t ∈ Icc 0 T,
      HasDerivAt (fun s => rotation (S s)) (rotation (S t) * hat (ωh t)) t)
    (h0 : R 0 = S 0) (hq0 : q 0 = 0)
    (hq : ∀ t, HasDerivAt q (b t) t)
    (hb : ∀ t ∈ Icc 0 T, enorm (ω t - ωh t) ≤ b t) :
    ∀ t ∈ Icc 0 T, ‖rotation (R t) - rotation (S t)‖ ≤ q t := by
  have he := norm_le_primitive
    (fun t => rotation (R t) * star (rotation (S t)) - 1)
    (fun t => rotation (R t) * hat (ω t - ωh t) * star (rotation (S t))) q b
    (fun t ht => (relative_derivative R S ω ωh t (hR t ht) (hS t ht)).sub_const 1)
    hq (by simp only [h0, rotation_mul_star, sub_self]) hq0
    (fun t ht => (relative_rate_bound _ _ _).trans (hb t ht))
  intro t ht
  have hid : rotation (R t) - rotation (S t) =
      (rotation (R t) * star (rotation (S t)) - 1) * rotation (S t) := by
    rw [sub_mul, mul_assoc, rotation_star_mul, mul_one, one_mul]
  calc
    _ = _ := congrArg norm hid
    _ ≤ ‖rotation (R t) * star (rotation (S t)) - 1‖ * ‖rotation (S t)‖ :=
      norm_mul_le _ _
    _ = ‖rotation (R t) * star (rotation (S t)) - 1‖ := by rw [rotation_norm, mul_one]
    _ ≤ _ := he t ht

theorem velocity_input_rate (R S : SO3) (a ah : E3) {ba br abar : ℝ}
    (ha : ‖a-ah‖ ≤ ba) (hr : ‖rotation R - rotation S‖ ≤ br) (hah : ‖ah‖ ≤ abar) :
    ‖rotation R a - rotation S ah‖ ≤ ba + abar * br := by
  have hid : rotation R a - rotation S ah =
      rotation R (a-ah) + (rotation R - rotation S) ah := by simp
  calc
    _ = _ := congrArg norm hid
    _ ≤ ‖rotation R (a-ah)‖ + ‖(rotation R - rotation S) ah‖ := norm_add_le _ _
    _ ≤ ba + br * abar := _root_.add_le_add
      (by simpa only [rotation_norm_apply] using ha)
      (((rotation R - rotation S).le_opNorm ah).trans
        (mul_le_mul hr hah (norm_nonneg _) ((norm_nonneg _).trans hr)))
    _ = _ := by ring

/-- Three scalar primitives bound the complete physical increment error.
The two inputs can be arbitrary functions satisfying the stated envelopes. -/
theorem physical_input_bound {T abar : ℝ}
    (R S : ℝ → SO3) (v vh p ph a ah : ℝ → E3) (ω ωh : ℝ → Vec3)
    (qr qv qp bw ba : ℝ → ℝ)
    (hR : ∀ t ∈ Icc 0 T,
      HasDerivAt (fun s => rotation (R s)) (rotation (R t) * hat (ω t)) t)
    (hS : ∀ t ∈ Icc 0 T,
      HasDerivAt (fun s => rotation (S s)) (rotation (S t) * hat (ωh t)) t)
    (hv : ∀ t ∈ Icc 0 T, HasDerivAt v (rotation (R t) (a t)) t)
    (hvh : ∀ t ∈ Icc 0 T, HasDerivAt vh (rotation (S t) (ah t)) t)
    (hp : ∀ t ∈ Icc 0 T, HasDerivAt p (v t) t)
    (hph : ∀ t ∈ Icc 0 T, HasDerivAt ph (vh t) t)
    (hR0 : R 0 = S 0) (hv0 : v 0 = vh 0) (hp0 : p 0 = ph 0)
    (hqr0 : qr 0 = 0) (hqv0 : qv 0 = 0) (hqp0 : qp 0 = 0)
    (hqr : ∀ t, HasDerivAt qr (bw t) t)
    (hqv : ∀ t, HasDerivAt qv (ba t + abar * qr t) t)
    (hqp : ∀ t, HasDerivAt qp (qv t) t)
    (hbw : ∀ t ∈ Icc 0 T, enorm (ω t - ωh t) ≤ bw t)
    (hba : ∀ t ∈ Icc 0 T, ‖a t - ah t‖ ≤ ba t)
    (hbar : ∀ t ∈ Icc 0 T, ‖ah t‖ ≤ abar) :
    ∀ t ∈ Icc 0 T, ‖rotation (R t) - rotation (S t)‖ ≤ qr t ∧
      ‖v t - vh t‖ ≤ qv t ∧ ‖p t - ph t‖ ≤ qp t := by
  have hr := attitude_input_bound R S ω ωh qr bw hR hS hR0 hqr0 hqr hbw
  have hvb := norm_le_primitive (fun t => v t - vh t)
    (fun t => rotation (R t) (a t) - rotation (S t) (ah t)) qv
    (fun t => ba t + abar * qr t)
    (fun t ht => (hv t ht).sub (hvh t ht)) hqv (by simp [hv0]) hqv0
    (fun t ht => velocity_input_rate _ _ _ _ (hba t ht) (hr t ht) (hbar t ht))
  have hpb := norm_le_primitive (fun t => p t - ph t) (fun t => v t - vh t) qp qv
    (fun t ht => (hp t ht).sub (hph t ht)) hqp (by simp [hp0]) hqp0 hvb
  exact fun t ht => ⟨hr t ht, hvb t ht, hpb t ht⟩

/-- Unit-curvature FOH input-error envelope and its three primitives. -/
def shape0 (T t : ℝ) : ℝ := t * (T-t) / 2
def shape1 (T t : ℝ) : ℝ := T*t^2/4 - t^3/6
def shape2 (T t : ℝ) : ℝ := T*t^3/12 - t^4/24
def shape3 (T t : ℝ) : ℝ := T*t^4/48 - t^5/120

theorem shape1_derivative (T t : ℝ) : HasDerivAt (shape1 T) (shape0 T t) t := by
  convert (((hasDerivAt_pow 2 t).const_mul T).div_const 4).sub
    ((hasDerivAt_pow 3 t).div_const 6) using 1
  simp [shape0]
  ring

theorem shape2_derivative (T t : ℝ) : HasDerivAt (shape2 T) (shape1 T t) t := by
  convert (((hasDerivAt_pow 3 t).const_mul T).div_const 12).sub
    ((hasDerivAt_pow 4 t).div_const 24) using 1
  simp [shape1]
  ring

theorem shape3_derivative (T t : ℝ) : HasDerivAt (shape3 T) (shape2 T t) t := by
  convert (((hasDerivAt_pow 4 t).const_mul T).div_const 48).sub
    ((hasDerivAt_pow 5 t).div_const 120) using 1
  simp [shape2]
  ring

/-- Input interpolation error in physical outputs. The parabolic input
envelopes follow from `Hold.linear_error_le` for twice differentiable signals.
Unlike substituting their uniform maxima, integration retains their zeros
at the sampled endpoints. These bounds concern input error alone. -/
theorem parabolic_input_error {T Mw Ma abar : ℝ} (hT : 0 ≤ T)
    (R S : ℝ → SO3) (v vh p ph a ah : ℝ → E3) (ω ωh : ℝ → Vec3)
    (hR : ∀ t ∈ Icc 0 T,
      HasDerivAt (fun s => rotation (R s)) (rotation (R t) * hat (ω t)) t)
    (hS : ∀ t ∈ Icc 0 T,
      HasDerivAt (fun s => rotation (S s)) (rotation (S t) * hat (ωh t)) t)
    (hv : ∀ t ∈ Icc 0 T, HasDerivAt v (rotation (R t) (a t)) t)
    (hvh : ∀ t ∈ Icc 0 T, HasDerivAt vh (rotation (S t) (ah t)) t)
    (hp : ∀ t ∈ Icc 0 T, HasDerivAt p (v t) t)
    (hph : ∀ t ∈ Icc 0 T, HasDerivAt ph (vh t) t)
    (hR0 : R 0 = S 0) (hv0 : v 0 = vh 0) (hp0 : p 0 = ph 0)
    (hbw : ∀ t ∈ Icc 0 T, enorm (ω t - ωh t) ≤ Mw * shape0 T t)
    (hba : ∀ t ∈ Icc 0 T, ‖a t - ah t‖ ≤ Ma * shape0 T t)
    (hbar : ∀ t ∈ Icc 0 T, ‖ah t‖ ≤ abar) :
    ‖rotation (R T) - rotation (S T)‖ ≤ Mw*T^3/12 ∧
      ‖v T - vh T‖ ≤ Ma*T^3/12 + abar*Mw*T^4/24 ∧
      ‖p T - ph T‖ ≤ Ma*T^4/24 + abar*Mw*T^5/80 := by
  have h := physical_input_bound R S v vh p ph a ah ω ωh
    (fun t => Mw * shape1 T t)
    (fun t => Ma * shape1 T t + (abar*Mw) * shape2 T t)
    (fun t => Ma * shape2 T t + (abar*Mw) * shape3 T t)
    (fun t => Mw * shape0 T t) (fun t => Ma * shape0 T t)
    hR hS hv hvh hp hph hR0 hv0 hp0
    (by simp [shape1]) (by simp [shape1, shape2]) (by simp [shape2, shape3])
    (fun t => (shape1_derivative T t).const_mul Mw)
    (fun t => by
      convert ((shape1_derivative T t).const_mul Ma).add
        ((shape2_derivative T t).const_mul (abar*Mw)) using 1
      ring)
    (fun t => ((shape2_derivative T t).const_mul Ma).add
      ((shape3_derivative T t).const_mul (abar*Mw))) hbw hba hbar T ⟨hT, le_rfl⟩
  dsimp [shape1, shape2, shape3] at h
  ring_nf at h ⊢
  exact h

/-- Direct physical specialization for true smooth inputs and their sampled
FOH interpolants. `Mw` and `Ma` bound the second time derivatives of the true
inputs; they are additional assumptions, not recoverable from two samples.
The maximum endpoint accelerometer norm supplies `abar` automatically. -/
theorem smooth_input_error {T Mw Ma : ℝ} (hT : 0 < T)
    (R S : ℝ → SO3) (v vh p ph ω ω' ω'' a a' a'' : ℝ → E3)
    (hR : ∀ t ∈ Icc 0 T,
      HasDerivAt (fun s => rotation (R s))
        (rotation (R t) * hat (WithLp.ofLp (ω t))) t)
    (hS : ∀ t ∈ Icc 0 T,
      HasDerivAt (fun s => rotation (S s))
        (rotation (S t) * hat (WithLp.ofLp (Hold.linInterp ω T t))) t)
    (hv : ∀ t ∈ Icc 0 T, HasDerivAt v (rotation (R t) (a t)) t)
    (hvh : ∀ t ∈ Icc 0 T,
      HasDerivAt vh (rotation (S t) (Hold.linInterp a T t)) t)
    (hp : ∀ t ∈ Icc 0 T, HasDerivAt p (v t) t)
    (hph : ∀ t ∈ Icc 0 T, HasDerivAt ph (vh t) t)
    (hR0 : R 0 = S 0) (hv0 : v 0 = vh 0) (hp0 : p 0 = ph 0)
    (hw : ∀ t ∈ Icc 0 T, HasDerivAt ω (ω' t) t)
    (hw' : ∀ t ∈ Icc 0 T, HasDerivAt ω' (ω'' t) t)
    (hMw : ∀ t ∈ Icc 0 T, ‖ω'' t‖ ≤ Mw)
    (ha : ∀ t ∈ Icc 0 T, HasDerivAt a (a' t) t)
    (ha' : ∀ t ∈ Icc 0 T, HasDerivAt a' (a'' t) t)
    (hMa : ∀ t ∈ Icc 0 T, ‖a'' t‖ ≤ Ma) :
    let abar := max ‖a 0‖ ‖a T‖
    ‖rotation (R T) - rotation (S T)‖ ≤ Mw*T^3/12 ∧
      ‖v T - vh T‖ ≤ Ma*T^3/12 + abar*Mw*T^4/24 ∧
      ‖p T - ph T‖ ≤ Ma*T^4/24 + abar*Mw*T^5/80 := by
  apply parabolic_input_error hT.le R S v vh p ph a (Hold.linInterp a T)
    (fun t => WithLp.ofLp (ω t)) (fun t => WithLp.ofLp (Hold.linInterp ω T t))
    hR hS hv hvh hp hph hR0 hv0 hp0
  · intro t ht
    have hh := Hold.linear_error_le hT hw hw' hMw ht
    change ‖ω t - Hold.linInterp ω T t‖ ≤ _
    exact hh.trans_eq (by unfold shape0; ring)
  · intro t ht
    exact (Hold.linear_error_le hT ha ha' hMa ht).trans_eq (by unfold shape0; ring)
  · exact fun t ht => Hold.norm_linInterp_le hT ht (le_max_left _ _) (le_max_right _ _)

end GNC.Preintegration.CenteredFoh.InputError
