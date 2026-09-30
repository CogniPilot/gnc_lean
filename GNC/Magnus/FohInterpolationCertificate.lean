import GNC.Magnus.FohDefectCertificate
import GNC.Analysis.HoldInterpolation
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-! Integrated FOH interpolation certificates for norm-one right flows.
The norm-one flow/inverse hypotheses express isometric transport (as for
rotations in their Euclidean operator representation). They are explicit;
no arbitrary full SE₂(3) matrix is assumed to have norm one. -/
noncomputable section
namespace GNC.Magnus
open Set
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

/-- Inverse derivative of an actual right-composed unit-valued flow. -/
theorem foh_unit_inverse_derivative (S : ℝ → Aˣ) (N : A) (t : ℝ)
    (hS : HasDerivAt (fun s => (S s : A)) ((S t : A)*N) t) :
    HasDerivAt (fun s => ((S s)⁻¹).val) (-N*((S t)⁻¹).val) t := by
  have hd := (hasFDerivAt_ringInverse (𝕜 := ℝ) (S t)).comp_hasDerivAt t hS
  simp only [Function.comp_def, Ring.inverse_unit, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.mulLeftRight_apply] at hd
  have hi : ((S t)⁻¹).val*(S t : A) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  convert hd using 1
  simp only [← mul_assoc, hi, one_mul, neg_mul]

/-- Integrate the pointwise interpolation parabola rather than multiplying
its maximum by the interval length. The result concerns actual ODE flows,
not an assumed first-order error model. -/
theorem foh_interpolation_flow_bound (R S : ℝ → Aˣ) (N H : ℝ → A)
    {T M : ℝ} (hT : 0 ≤ T) (hR0 : R 0 = 1) (hS0 : S 0 = 1)
    (hR : ∀ t ∈ Icc 0 T, HasDerivAt (fun s => (R s : A)) ((R t : A)*N t) t)
    (hS : ∀ t ∈ Icc 0 T, HasDerivAt (fun s => (S s : A)) ((S t : A)*H t) t)
    (hRn : ∀ t ∈ Icc 0 T, ‖(R t : A)‖ ≤ 1)
    (hSin : ∀ t ∈ Icc 0 T, ‖((S t)⁻¹).val‖ ≤ 1)
    (hSn : ‖(S T : A)‖ ≤ 1)
    (hNH : ∀ t ∈ Icc 0 T, ‖N t-H t‖ ≤ M/2*t*(T-t)) :
    ‖(R T : A)-(S T : A)‖ ≤ M*T^3/12 := by
  let f := fun t => (R t : A)*((S t)⁻¹).val-1
  let df := fun t => (R t : A)*(N t-H t)*((S t)⁻¹).val
  have hd (t : ℝ) (ht : t ∈ Icc 0 T) : HasDerivAt f (df t) t := by
    have hi := foh_unit_inverse_derivative S (H t) t (hS t ht)
    convert ((hR t ht).mul hi).sub_const (1:A) using 1
    dsimp [df]
    noncomm_ring
  have hc : ContinuousOn f (Icc 0 T) := fun t ht =>
    (hd t ht).continuousAt.continuousWithinAt
  have hb (t : ℝ) (ht : t ∈ Ico 0 T) : ‖df t‖ ≤ M/2*t*(T-t) := by
    have ht' : t ∈ Icc 0 T := ⟨ht.1, ht.2.le⟩
    calc ‖df t‖ ≤ (‖(R t : A)‖*‖N t-H t‖)*‖((S t)⁻¹).val‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ (1*‖N t-H t‖)*1 := mul_le_mul
        (mul_le_mul_of_nonneg_right (hRn t ht') (norm_nonneg _)) (hSin t ht')
        (norm_nonneg _) (by positivity)
      _ ≤ M/2*t*(T-t) := by simpa using hNH t ht'
  have hpoly (t : ℝ) : HasDerivAt (fun s : ℝ => M*(T*s^2/4-s^3/6))
      (M/2*t*(T-t)) t := by
    convert ((((hasDerivAt_id t).pow 2).const_mul T).div_const 4 |>.sub
      (((hasDerivAt_id t).pow 3).div_const 6)).const_mul M using 1
    simp only [id_eq]
    ring
  have hi : ‖f 0‖ ≤ M*(T*0^2/4-0^3/6) := by simp [f, hR0, hS0]
  have hf := image_norm_le_of_norm_deriv_right_le_deriv_boundary hc
    (fun t ht => (hd t ⟨ht.1, ht.2.le⟩).hasDerivWithinAt) hi hpoly hb ⟨hT, le_rfl⟩
  have hiS : ((S T)⁻¹).val*(S T : A) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have he : (R T : A)-(S T : A) = f T*(S T : A) := by
    dsimp [f]
    rw [sub_mul, mul_assoc, hiS, mul_one, one_mul]
  calc ‖(R T : A)-(S T : A)‖ = ‖f T*(S T : A)‖ := by rw [he]
    _ ≤ ‖f T‖*‖(S T : A)‖ := norm_mul_le _ _
    _ ≤ ‖f T‖ := (mul_le_mul_of_nonneg_left hSn (norm_nonneg _)).trans_eq (mul_one _)
    _ ≤ M*T^3/12 := hf.trans_eq (by ring)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- From actual twice-differentiable rate data, via a contractive linear
rate-to-generator map and the actual two right-flow ODEs, to the integrated
M₂ T³/12 interpolation budget. -/
theorem foh_interpolation_from_curvature (L : E →L[ℝ] A) (hL : ‖L‖ ≤ 1)
    (U U₁ U₂ : ℝ → E) (R S : ℝ → Aˣ) {T M : ℝ} (hT : 0 < T)
    (hU : ∀ t ∈ Icc 0 T, HasDerivAt U (U₁ t) t)
    (hU₁ : ∀ t ∈ Icc 0 T, HasDerivAt U₁ (U₂ t) t)
    (hU₂ : ∀ t ∈ Icc 0 T, ‖U₂ t‖ ≤ M)
    (hR0 : R 0 = 1) (hS0 : S 0 = 1)
    (hR : ∀ t ∈ Icc 0 T,
      HasDerivAt (fun s => (R s : A)) ((R t : A)*L (U t)) t)
    (hS : ∀ t ∈ Icc 0 T,
      HasDerivAt (fun s => (S s : A)) ((S t : A)*L (GNC.Hold.linInterp U T t)) t)
    (hRn : ∀ t ∈ Icc 0 T, ‖(R t : A)‖ ≤ 1)
    (hSin : ∀ t ∈ Icc 0 T, ‖((S t)⁻¹).val‖ ≤ 1)
    (hSn : ‖(S T : A)‖ ≤ 1) :
    ‖(R T : A)-(S T : A)‖ ≤ M*T^3/12 := by
  apply foh_interpolation_flow_bound R S (fun t => L (U t))
    (fun t => L (GNC.Hold.linInterp U T t)) hT.le hR0 hS0 hR hS hRn hSin hSn
  intro t ht
  rw [← map_sub]
  calc ‖L (U t-GNC.Hold.linInterp U T t)‖ ≤ ‖L‖*‖U t-GNC.Hold.linInterp U T t‖ := L.le_opNorm _
    _ ≤ ‖U t-GNC.Hold.linInterp U T t‖ :=
      (mul_le_mul_of_nonneg_right hL (norm_nonneg _)).trans_eq (one_mul _)
    _ ≤ M/2*t*(T-t) := GNC.Hold.linear_error_le hT hU hU₁ hU₂ ht

omit [CompleteSpace A] in
/-- The linearly interpolated input becomes exactly the affine generator
used by the finite-defect certificate. -/
theorem foh_lift_linear_input (L : E →L[ℝ] A) (U : ℝ → E) (T t : ℝ) :
    L (GNC.Hold.linInterp U T t) =
      L (U 0)+t • (T⁻¹ • (L (U T)-L (U 0))) := by
  simp [GNC.Hold.linInterp, map_add, map_smul, smul_sub, smul_smul,
    sub_smul, div_eq_mul_inv]
  module

/-- End-to-end deterministic local certificate: actual smooth input,
its endpoint linear interpolant, and the one-exponential FOH update.
The norm-one transport and contractive input lift are explicit geometric
hypotheses. The measured waveform error is not replaced by a truncation
coefficient or a fitted remainder. -/
theorem foh_physical_input_certificate [NormOneClass A]
    (L : E →L[ℝ] A) (hL : ‖L‖ ≤ 1)
    (U U₁ U₂ : ℝ → E) (R S : ℝ → Aˣ) (n m : ℕ) {T M r : ℝ}
    (hT : 0 < T)
    (hU : ∀ t ∈ Icc 0 T, HasDerivAt U (U₁ t) t)
    (hU₁ : ∀ t ∈ Icc 0 T, HasDerivAt U₁ (U₂ t) t)
    (hU₂ : ∀ t ∈ Icc 0 T, ‖U₂ t‖ ≤ M)
    (hR0 : R 0 = 1) (hS0 : S 0 = 1)
    (hR : ∀ t ∈ Icc 0 T,
      HasDerivAt (fun s => (R s : A)) ((R t : A)*L (U t)) t)
    (hS : ∀ t ∈ Icc 0 T,
      HasDerivAt (fun s => (S s : A)) ((S t : A)*L (GNC.Hold.linInterp U T t)) t)
    (hRn : ∀ t ∈ Icc 0 T, ‖(R t : A)‖ ≤ 1)
    (hSin : ∀ t ∈ Icc 0 T, ‖((S t)⁻¹).val‖ ≤ 1)
    (hSn : ‖(S T : A)‖ ≤ 1)
    (hr : ‖fohRetainedExponent (L (U 0)) (T⁻¹ • (L (U T)-L (U 0))) T‖ ≤ r)
    (hr1 : r ≤ 1) (hm : 0 < m) :
    let a := L (U 0)
    let b := T⁻¹ • (L (U T)-L (U 0))
    ‖(R T : A)-NormedSpace.exp (fohRetainedExponent a b T)‖ ≤ M*T^3/12 +
      (AlgebraPolynomial.majorant (fohFiniteDifference a b n m) T +
       Real.exp ((‖a‖+T*‖b‖)*T) * (fohDefectRadius a b n T*T) +
       r^m*(m+1)/(Nat.factorial m*m)) := by
  dsimp only
  have hi := foh_interpolation_from_curvature L hL U U₁ U₂ R S hT
    hU hU₁ hU₂ hR0 hS0 hR hS hRn hSin hSn
  have hs0 : (S 0 : A) = 1 := by rw [hS0, Units.val_one]
  have hs : ∀ t ∈ Icc 0 T, HasDerivAt (fun s => (S s : A))
      ((S t : A)*(L (U 0)+t • (T⁻¹ • (L (U T)-L (U 0))))) t := by
    intro t ht
    simpa only [foh_lift_linear_input] using hS t ht
  have ht := foh_defect_coefficient_certificate (L (U 0))
    (T⁻¹ • (L (U T)-L (U 0))) (fun t => (S t : A)) n m hT.le hs0 hs hr hr1 hm
  exact (norm_sub_le_norm_sub_add_norm_sub _ (S T : A) _).trans (add_le_add hi ht)

/-- Scalar chord-to-angle conversion on the principal angle range. To use
this for SO(3), its spectral chord identity must be supplied separately;
the theorem does not silently identify a matrix norm with an angle. -/
theorem foh_angle_of_chord_bound {θ b : ℝ} (hθ0 : 0 ≤ θ) (hθπ : θ ≤ Real.pi)
    (hb : 2*Real.sin (θ/2) ≤ b) :
    θ ≤ 2*Real.arcsin (min 1 (b/2)) := by
  have hs : Real.sin (θ/2) ≤ min 1 (b/2) := le_min (Real.sin_le_one _) (by linarith)
  have ha := Real.arcsin_le_arcsin hs
  rw [Real.arcsin_sin (by linarith [Real.pi_pos] : -(Real.pi/2) ≤ θ/2)
    (by linarith : θ/2 ≤ Real.pi/2)] at ha
  linarith

end GNC.Magnus
