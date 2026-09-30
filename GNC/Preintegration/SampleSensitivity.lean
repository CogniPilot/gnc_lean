import GNC.Preintegration.ErrorDynamics
import GNC.Dynamics.MixedLogLinear

/-! Actual-flow initial and sample sensitivities. All statements concern
the original right-flow ODE, not derivatives assumed for a proposed update.
-/
noncomputable section
namespace GNC.Preintegration.Uncertainty
open GNC.Magnus
variable {E : Type*} [NormedRing E] [NormedAlgebra ℝ E] [CompleteSpace E]

def initialTransition (U : ℝ → Eˣ) (Z : E) (t : ℝ) : E :=
  ((U t)⁻¹).val * Z * (U t).val

theorem initialTransition_derivative (U : ℝ → Eˣ) (N : ℝ → E)
    (hU : ∀ t, HasDerivAt (fun s => (U s).val) ((U t).val*N t) t)
    (Z : E) (t : ℝ) :
    HasDerivAt (initialTransition U Z)
      (initialTransition U Z t*N t-N t*initialTransition U Z t) t := by
  convert ((foh_inverse_derivative U N hU t).mul_const Z).mul (hU t) using 1
  dsimp [initialTransition]
  noncomm_ring

theorem initialTransition_zero (U : ℝ → Eˣ) (h0 : U 0 = 1) (Z : E) :
    initialTransition U Z 0 = Z := by simp [initialTransition, h0]

def leftResponse (U : ℝ → Eˣ) (B : ℝ → E) (t : ℝ) : E :=
  ((U t)⁻¹).val * fohSensitivityIntegral U B t

theorem leftResponse_derivative (U : ℝ → Eˣ) (N B : ℝ → E)
    (hU : ∀ t, HasDerivAt (fun s => (U s).val) ((U t).val*N t) t)
    (hB : Continuous B) (t : ℝ) :
    HasDerivAt (leftResponse U B)
      (leftResponse U B t*N t-N t*leftResponse U B t+B t) t := by
  convert (foh_inverse_derivative U N hU t).mul
    (foh_sensitivityIntegral_derivative U N B hU hB t) using 1
  dsimp [leftResponse]
  simp only [mul_add, ← mul_assoc, Units.inv_mul, one_mul]
  noncomm_ring

theorem leftResponse_zero (U : ℝ → Eˣ) (B : ℝ → E) :
    leftResponse U B 0 = 0 := by simp [leftResponse, fohSensitivityIntegral]

/-- The derivative is expressed in the left error at the fixed endpoint. -/
theorem actual_left_sample_derivative (N B : ℝ → E) (U : ℝ → ℝ → Eˣ)
    (hN : Continuous N) (hB : Continuous B)
    (hU : ∀ q t, HasDerivAt (fun s => (U q s).val) ((U q t).val*(N t+q • B t)) t)
    (h0 : ∀ q, U q 0 = 1) {T : ℝ} (hT : 0 ≤ T) :
    HasDerivAt (fun q => ((U 0 T)⁻¹*U q T).val) (leftResponse (U 0) B T) 0 := by
  simpa [leftResponse, Units.val_mul] using
    (foh_parameter_integral_hasDerivAt N B U hN hB hU h0 hT).const_mul ((U 0 T)⁻¹).val

theorem leftResponse_add (U : ℝ → Eˣ) (N B C : ℝ → E)
    (hU : ∀ t, HasDerivAt (fun s => (U s).val) ((U t).val*N t) t)
    (hB : Continuous B) (hC : Continuous C) (T : ℝ) :
    leftResponse U (fun t => B t+C t) T = leftResponse U B T+leftResponse U C T := by
  have hb := (foh_conjugatedInput_continuous U N B hU hB).intervalIntegrable
    (μ := MeasureTheory.volume) 0 T
  have hc := (foh_conjugatedInput_continuous U N C hU hC).intervalIntegrable
    (μ := MeasureTheory.volume) 0 T
  have he : fohConjugatedInput U (fun t => B t+C t) =
      fun t => fohConjugatedInput U B t+fohConjugatedInput U C t := by
    funext t; simp [fohConjugatedInput, mul_add, add_mul]
  simp only [leftResponse, fohSensitivityIntegral, he,
    intervalIntegral.integral_add hb hc, add_mul, mul_add]

theorem leftResponse_neg (U : ℝ → Eˣ) (B : ℝ → E) (T : ℝ) :
    leftResponse U (fun t => -B t) T = -leftResponse U B T := by
  simp [leftResponse, fohSensitivityIntegral, fohConjugatedInput,
    intervalIntegral.integral_neg]

/-- Both endpoint sensitivity columns sum to the constant-input column.
This holds for a time-varying nominal flow as well as ZOH. -/
theorem endpoint_partition (U : ℝ → Eˣ) (N : ℝ → E)
    (hU : ∀ t, HasDerivAt (fun s => (U s).val) ((U t).val*N t) t)
    (B : E) (T : ℝ) :
    leftResponse U (fun t => (1-t/T) • B) T +
      leftResponse U (fun t => (t/T) • B) T = leftResponse U (fun _ => B) T := by
  rw [← leftResponse_add U N _ _ hU (by fun_prop) (by fun_prop)]
  congr 1
  funext t
  rw [← add_smul]; simp

/-- A bias subtracted from both samples has sensitivity minus the sum of
the sample columns. It must not be added as two independent random biases. -/
theorem constant_bias_response (U : ℝ → Eˣ) (N : ℝ → E)
    (hU : ∀ t, HasDerivAt (fun s => (U s).val) ((U t).val*N t) t)
    (B : E) (T : ℝ) :
    leftResponse U (fun _ => -B) T =
      -(leftResponse U (fun t => (1-t/T) • B) T +
        leftResponse U (fun t => (t/T) • B) T) := by
  rw [endpoint_partition U N hU, leftResponse_neg]

/-- ZOH's actual exponential has the same proved parameter sensitivity.
No finite-difference derivative or inverse of a possibly singular generator
is used. -/
theorem zoh_exponential_sensitivity (N B : E) {T : ℝ} (hT : 0 ≤ T) :
    HasDerivAt (fun q : ℝ => NormedSpace.exp (T • (N+q • B)))
      (fohSensitivityIntegral (fun t => GNC.MixedInvariant.expUnit (t • N))
        (fun _ => B) T) 0 := by
  let U : ℝ → ℝ → Eˣ := fun q t => GNC.MixedInvariant.expUnit (t • (N+q • B))
  have hU (q t : ℝ) : HasDerivAt (fun s => (U q s).val)
      ((U q t).val*(N+q • B)) t := by
    simpa [U, GNC.MixedInvariant.expUnit] using
      hasDerivAt_exp_smul_const (N+q • B) t
  have hz (q : ℝ) : U q 0 = 1 := by
    apply Units.ext; simp [U, GNC.MixedInvariant.expUnit]
  simpa [U, GNC.MixedInvariant.expUnit] using
    foh_parameter_integral_hasDerivAt (fun _ => N) (fun _ => B) U
      continuous_const continuous_const hU hz hT

end GNC.Preintegration.Uncertainty
