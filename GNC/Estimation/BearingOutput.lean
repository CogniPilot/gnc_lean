import GNC.Lie.Euclidean
import GNC.Control.ReferenceTube
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Quantitative noiseless output-approximation comparisons for a bearing.

Rotating a unit bearing through theta in a fixed great circle gives an
explicit instance of the EqF paper's output construction. The comparison
isolates output residuals, not complete-filter stochastic performance.
-/
noncomputable section
open Matrix Real Set
namespace GNC.BearingOutput

def bearing (θ : ℝ) : Vec3 := ![cos θ,sin θ,0]
def standardResidual (θ : ℝ) : Vec3 := ![cos θ-1,sin θ-θ,0]
def embeddedResidual (θ : ℝ) : Vec3 := ![cos θ-1,0,0]
def averagedResidual (θ : ℝ) : Vec3 :=
  ![cos θ-1+θ*sin θ/2,sin θ-θ*(1+cos θ)/2,0]
def amplitude (θ : ℝ) : ℝ := 2*sin (θ/2)-θ*cos (θ/2)

theorem bearing_unit (θ : ℝ) : lengthSq (bearing θ)=1 := by
  simpa [lengthSq,bearing,add_comm] using sin_sq_add_cos_sq θ

/-- Average the output derivatives at the two endpoints of the same
rotation orbit. This is the concrete EqF-star output construction. -/
theorem averaged_residual_identity (θ : ℝ) :
    bearing θ-bearing 0-(θ/2) • ![-sin θ,1+cos θ,0] = averagedResidual θ := by
  ext i
  fin_cases i <;> simp [bearing,averagedResidual] <;> ring

theorem amplitude_derivative (θ : ℝ) :
    HasDerivAt amplitude (θ*sin (θ/2)/2) θ := by
  have hh : HasDerivAt (fun s : ℝ => s/2) (1/2) θ := (hasDerivAt_id θ).div_const 2
  convert (hh.sin.const_mul 2).sub ((hasDerivAt_id θ).mul hh.cos) using 1
  simp only [id_eq]
  ring

/-- Explicit cubic bound; there is no unspecified big-O constant. -/
theorem amplitude_cubic_bound {θ : ℝ} (hθ : 0 ≤ θ) : amplitude θ ≤ θ^3/12 := by
  apply image_le_of_deriv_right_le_deriv_boundary
    (fun s _ => (amplitude_derivative s).continuousAt.continuousWithinAt)
    (fun s _ => (amplitude_derivative s).hasDerivWithinAt)
    (by simp [amplitude])
    (f := amplitude) (B := fun s : ℝ => s^3/12) (a := 0) (b := θ)
    (by fun_prop)
    (fun s _ => (((hasDerivAt_id s).pow 3).div_const 12).hasDerivWithinAt)
    (by
      intro s hs
      have h := mul_le_mul_of_nonneg_left (sin_le (by linarith [hs.1] : 0≤s/2)) hs.1
      dsimp
      nlinarith) ⟨hθ,le_rfl⟩

theorem amplitude_nonneg {θ : ℝ} (hθ : 0 ≤ θ) (hπ : θ ≤ π) : 0 ≤ amplitude θ := by
  apply image_le_of_deriv_right_le_deriv_boundary
    (f := fun _ : ℝ => 0) (B := amplitude) (a := 0) (b := θ)
    continuous_const.continuousOn
    (fun s _ => (hasDerivAt_const s (0:ℝ)).hasDerivWithinAt)
    (by simp [amplitude])
    (fun s _ => (amplitude_derivative s).continuousAt.continuousWithinAt)
    (fun s _ => (amplitude_derivative s).hasDerivWithinAt)
    (by
      intro s hs
      have hsin := sin_nonneg_of_nonneg_of_le_pi (by linarith [hs.1] : 0≤s/2)
        (by linarith [pi_pos,hs.2] : s/2≤π)
      exact div_nonneg (mul_nonneg hs.1 hsin) (by norm_num)) ⟨hθ,le_rfl⟩

theorem averaged_factorization (θ : ℝ) :
    averagedResidual θ = amplitude θ • ![-sin (θ/2),cos (θ/2),0] := by
  have hc := cos_two_mul (θ/2)
  have hs := sin_two_mul (θ/2)
  have hi := sin_sq_add_cos_sq (θ/2)
  rw [show 2*(θ/2)=θ by ring] at hc hs
  ext i
  fin_cases i <;> simp [averagedResidual,amplitude,hc,hs] <;> nlinarith

theorem averaged_norm {θ : ℝ} (hθ : 0 ≤ θ) (hπ : θ ≤ π) :
    enorm (averagedResidual θ) = amplitude θ := by
  have hn : enorm (![-sin (θ/2),cos (θ/2),0] : Vec3)=1 := by
    have hsq := enorm_sq (![-sin (θ/2),cos (θ/2),0] : Vec3)
    simp [lengthSq] at hsq
    rcases hsq with hsq | hsq
    · exact hsq
    · exfalso
      linarith [enorm_nonneg (![-sin (θ/2),cos (θ/2),0] : Vec3)]
  rw [averaged_factorization,enorm_smul,hn,mul_one,abs_of_nonneg (amplitude_nonneg hθ hπ)]

theorem averaged_cubic_bound {θ : ℝ} (hθ : 0 ≤ θ) (hπ : θ ≤ π) :
    enorm (averagedResidual θ) ≤ θ^3/12 := by
  rw [averaged_norm hθ hπ]
  exact amplitude_cubic_bound hθ

/-- The paper's normalized embedded EKF and the ordinary EqF use different
error variables. On unit endpoints the embedded residual is never larger
than the standard EqF residual. This is not a filter-MSE comparison. -/
theorem embedded_le_standard (θ : ℝ) :
    enorm (embeddedResidual θ) ≤ enorm (standardResidual θ) := by
  have h₁ := enorm_sq (embeddedResidual θ)
  have h₂ := enorm_sq (standardResidual θ)
  have hn₁ := enorm_nonneg (embeddedResidual θ)
  have hn₂ := enorm_nonneg (standardResidual θ)
  dsimp [embeddedResidual,standardResidual] at *
  simp [lengthSq] at h₁ h₂
  nlinarith [sq_nonneg (sin θ-θ)]

theorem embedded_norm (θ : ℝ) : enorm (embeddedResidual θ)=1-cos θ := by
  have hsq := enorm_sq (embeddedResidual θ)
  have hn := enorm_nonneg (embeddedResidual θ)
  have hc := cos_le_one θ
  dsimp [embeddedResidual] at *
  simp [lengthSq] at hsq
  nlinarith

/-- A quantified noiseless output advantage: averaging is no worse than
the normalized embedded EKF on unit endpoints in this great circle.
This compares output residuals, not complete-filter performance. -/
theorem averaged_le_embedded {θ : ℝ} (hθ : 0 ≤ θ) (hπ : θ ≤ π) :
    enorm (averagedResidual θ) ≤ enorm (embeddedResidual θ) := by
  rw [averaged_norm hθ hπ,embedded_norm]
  have hs := sin_nonneg_of_nonneg_of_le_pi (by linarith : 0≤θ/2)
    (by linarith [pi_pos] : θ/2≤π)
  have hc := cos_nonneg_of_neg_pi_div_two_le_of_le
    (by linarith [pi_pos] : -(π/2)≤θ/2) (by linarith : θ/2≤π/2)
  have hi := sin_sq_add_cos_sq (θ/2)
  have hsum : 1 ≤ sin (θ/2)+cos (θ/2) := by
    nlinarith [mul_nonneg hs hc]
  have hprod := mul_nonneg hs (sub_nonneg.mpr hsum)
  have hsin := mul_le_mul_of_nonneg_right (sin_le (by linarith : 0≤θ/2)) hc
  have hcos := cos_two_mul (θ/2)
  rw [show 2*(θ/2)=θ by ring] at hcos
  dsimp [amplitude]
  nlinarith

/-- Linear ambient measurement is another valid extension of the same
unit-bearing output. Its output approximation residual is exactly zero;
state-constraint handling and covariance consistency remain separate. -/
theorem ambient_output_exact (true estimate : Vec3) :
    true-estimate-(true-estimate) = 0 := sub_self _

/-- Measurement noise entering an endpoint-averaged rotational Jacobian
introduces an additional error/noise product, even though the noiseless
output residual is cubic. -/
theorem averaged_noise_term (noise error : Vec3) :
    enorm ((1/2 : ℝ) • (noise ⨯₃ error)) ≤ enorm noise*enorm error/2 := by
  rw [enorm_smul]
  norm_num
  have h := cross_enorm_le noise error
  linarith

/-- For an isotropic output weight, the continuous-time standard and
endpoint-averaged bearing Jacobians give the SAME raw innovation
correction. Multiplication by the same prior covariance and lift preserves
this equality. Their Riccati matrices can still evolve differently. -/
theorem averaged_correction_identity (measurement predicted : Vec3) :
    ((1/2 : ℝ) • (measurement+predicted)) ⨯₃ (measurement-predicted) =
      predicted ⨯₃ (measurement-predicted) := by
  ext i
  fin_cases i <;> simp [crossProduct,vecHead,vecTail] <;> ring

/-- The one-dimensional great-circle information coefficient is reduced
from one to cos(theta/2)^2 by endpoint averaging. -/
theorem averaged_information (θ : ℝ) :
    ((-sin θ)/2)^2+((1+cos θ)/2)^2 = (1+cos θ)/2 := by
  nlinarith [sin_sq_add_cos_sq θ]

/-- At an identical prior covariance, the averaged Jacobian increases
the scalar Riccati derivative by this explicit nonnegative amount. This
is a mechanism for changed gains, not a theorem of smaller MSE. -/
theorem riccati_derivative_difference (σ q : ℝ) {n : ℝ} (hn : 0 < n) (θ : ℝ) :
    (q-σ^2*((1+cos θ)/2)/n)-(q-σ^2/n) = σ^2*(1-cos θ)/(2*n) ∧
      0 ≤ σ^2*(1-cos θ)/(2*n) := by
  constructor
  · ring
  · positivity [sub_nonneg.mpr (cos_le_one θ)]

end GNC.BearingOutput
