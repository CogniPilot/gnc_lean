import GNC.Magnus.MagnusAlgebra
import GNC.Magnus.FohParameterSensitivity
import GNC.Magnus.MagnusFlow

/-! Error and sample sensitivity derivations for held-input preintegration.
The coordinate order here is GNC's `(position, velocity, rotation)`.
The nonlinear noisy group error is not asserted to be log-linear. Its
first variation is derived, and the discarded bilinear term is explicit.
-/
noncomputable section
open Matrix
namespace GNC.Preintegration.Uncertainty

section Algebra
variable {E : Type*} [NormedRing E] [NormedAlgebra ℝ E] [CompleteSpace E]

/-- Exact left error for nominal `M X + X N` and perturbed
`M Y + Y (N+B)`. The common world generator cancels. -/
theorem noisy_left_error_derivative (X Y : ℝ → Eˣ) {M N B : E} {t : ℝ}
    (hX : HasDerivAt (fun s => (X s).val) (M*(X t).val+(X t).val*N) t)
    (hY : HasDerivAt (fun s => (Y s).val) (M*(Y t).val+(Y t).val*(N+B)) t) :
    HasDerivAt (fun s => ((X s)⁻¹*Y s).val)
      (((X t)⁻¹*Y t).val*N-N*((X t)⁻¹*Y t).val+((X t)⁻¹*Y t).val*B) t := by
  have hi := (hasFDerivAt_ringInverse (𝕜 := ℝ) (X t)).comp_hasDerivAt t hX
  simp only [Function.comp_def, Ring.inverse_unit, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.mulLeftRight_apply] at hi
  convert hi.mul hY using 1
  simp only [Units.val_mul, add_mul, mul_add, neg_mul, mul_neg, mul_assoc,
    Units.mul_inv, mul_one]
  simp only [← mul_assoc, Units.inv_mul, one_mul]
  noncomm_ring

/-- Exact polynomial identity behind the first variation, with the omitted
state/input product retained. This is an ambient tangent computation. -/
theorem noisy_error_expansion (N Z B : E) (q : ℝ) :
    (1+q • Z)*N-N*(1+q • Z)+(1+q • Z)*(q • B) =
      q • (Z*N-N*Z+B) + q^2 • (Z*B) := by
  simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc,
    mul_smul_comm, smul_smul, smul_add, smul_sub, pow_two]
  abel

theorem noisy_error_first_variation (N Z B : E) :
    HasDerivAt (fun q : ℝ =>
      (1+q • Z)*N-N*(1+q • Z)+(1+q • Z)*(q • B)) (Z*N-N*Z+B) 0 := by
  simp_rw [noisy_error_expansion]
  convert ((hasDerivAt_id (0:ℝ)).smul_const (Z*N-N*Z+B)).add
    (((hasDerivAt_id (0:ℝ)).pow 2).smul_const (Z*B)) using 1 <;> simp

/-- Two sample perturbations interpolated over the hold. -/
def sampleHold (T : ℝ) (B₀ B₁ : E) (t : ℝ) : E :=
  (1-t/T) • B₀ + (t/T) • B₁

theorem sampleHold_continuous (T : ℝ) (B₀ B₁ : E) :
    Continuous (sampleHold T B₀ B₁) := by unfold sampleHold; fun_prop

theorem sampleHold_same (T : ℝ) (B : E) (t : ℝ) :
    sampleHold T B B t = B := by
  rw [sampleHold, ← add_smul]; simp

theorem sampleHold_bias (T : ℝ) (B₀ B₁ b : E) (t : ℝ) :
    sampleHold T (B₀-b) (B₁-b) t = sampleHold T B₀ B₁ t-b := by
  unfold sampleHold
  module

/-- Construct actual perturbed flows, then prove their endpoint derivative.
No parameter regularity or desired sensitivity is assumed. The same theorem
includes ZOH by taking equal endpoint perturbations. -/
theorem exists_sample_sensitivity (N : ℝ → E) (hN : Continuous N)
    (T : ℝ) (hT : 0 ≤ T) (B₀ B₁ : E) :
    ∃ U : ℝ → ℝ → Eˣ,
      (∀ q, U q 0 = 1) ∧
      (∀ q t, HasDerivAt (fun s => (U q s).val)
        ((U q t).val*(N t+q • sampleHold T B₀ B₁ t)) t) ∧
      HasDerivAt (fun q => (U q T).val)
        (GNC.Magnus.fohSensitivityIntegral (U 0) (sampleHold T B₀ B₁) T) 0 := by
  have hex (q : ℝ) := GNC.Magnus.exists_right_unit_flow
    (fun t => N t+q • sampleHold T B₀ B₁ t)
    (hN.add ((sampleHold_continuous T B₀ B₁).const_smul q))
  choose U h0 hU using hex
  exact ⟨U,h0,hU,GNC.Magnus.foh_parameter_integral_hasDerivAt N _ U
    hN (sampleHold_continuous T B₀ B₁) hU h0 hT⟩

end Algebra

/-- Left logarithmic-error first-variation generator; order `(p,v,theta)`.
Gyro and accelerometer are body-frame specific inputs. -/
def errorGenerator (ω a : Vec3) (x : LogState) : LogState :=
  ![x 1 - ω ⨯₃ x 0, -(a ⨯₃ x 2) - ω ⨯₃ x 1, -(ω ⨯₃ x 2)]

def inputDirection (δω δa : Vec3) : LogState := ![0, δa, δω]

/-- The coordinate error matrix is derived from the actual extended
commutator; its signs and time/position coupling are checked. -/
theorem errorGenerator_hat (ω a : Vec3) (x : LogState) :
    hat (errorGenerator ω a x) =
      hat x * GNC.Magnus.extended ![0,a,ω] 1 -
      GNC.Magnus.extended ![0,a,ω] 1 * hat x := by
  have h := GNC.Magnus.extended_commutator x ![0,a,ω] 0 1
  have he : GNC.Magnus.extendedBracket x ![0,a,ω] 0 1 = errorGenerator ω a x := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [GNC.Magnus.extendedBracket, errorGenerator, ad, crossProduct,
        vecHead, vecTail] <;> ring
  rw [he] at h
  simpa [GNC.Magnus.extended] using h.symm

/-- FOH inputs produce an affine error operator, including acceleration. -/
theorem errorGenerator_affine (ω a s b : Vec3) (x : LogState) (t : ℝ) :
    errorGenerator (ω+t • s) (a+t • b) x =
      errorGenerator ω a x + t • (errorGenerator s b x - ![x 1,0,0]) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [errorGenerator, crossProduct] <;> ring

end GNC.Preintegration.Uncertainty
