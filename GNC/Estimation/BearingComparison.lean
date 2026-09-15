import GNC.Estimation.BearingOutput
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Prod

/-! Matched endpoint averaging for the embedded EKF and rotational error
coordinates. These are output approximation errors, not filter MSE.
Noiseless unit endpoints make the true-endpoint derivative observable. -/
noncomputable section
open Matrix Real Set
namespace GNC.BearingComparison

section Normalization
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Actual derivative of normalization at a unit endpoint, along any
differentiable curve. This justifies the embedded measurement Jacobian. -/
theorem normalization_derivative {f : ℝ → E} {v : E} {t : ℝ}
    (hf : HasDerivAt f v t) (hunit : ‖f t‖ = 1) :
    HasDerivAt (fun s => (1/‖f s‖) • f s)
      (v-(inner ℝ (f t) v) • f t) t := by
  have hn : HasDerivAt (fun s => ‖f s‖) (inner ℝ (f t) v) t := by
    have h := hf.norm_sq.sqrt (by rw [hunit]; norm_num)
    simpa [Real.sqrt_sq (norm_nonneg _), hunit] using h
  have hi := (hasDerivAt_const t (1:ℝ)).div hn (by rw [hunit]; norm_num)
  convert hi.smul hf using 1
  simp [Pi.div_apply, hunit, neg_smul]
  module
end Normalization

def unitJacobian (q v : Vec3) : Vec3 := v-(q ⬝ᵥ v) • q
def averagedEmbedded (q y v : Vec3) : Vec3 :=
  (1/2 : ℝ) • (unitJacobian q v+unitJacobian y v)
def embeddedResidual (q y : Vec3) : Vec3 := y-q-averagedEmbedded q y (y-q)

/-- Endpoint averaging is exact for the quadratic norm constraint too;
this is separate from the normalized bearing output. -/
theorem constraint_secant (q y : Vec3) :
    lengthSq y-lengthSq q = (q+y) ⬝ᵥ (y-q) := by
  simp [lengthSq, dotProduct, Fin.sum_univ_succ]
  ring

/-- The midpoint average of the two correct normalized-output Jacobians
is an implementable noiseless endpoint rule, with an exact cubic residual
in chord length. It is not the Jacobian at the midpoint state. -/
theorem embedded_residual_factorization (q y : Vec3)
    (hq : q ⬝ᵥ q = 1) (hy : y ⬝ᵥ y = 1) :
    embeddedResidual q y = ((1-q ⬝ᵥ y)/2) • (y-q) := by
  simp only [embeddedResidual, averagedEmbedded, unitJacobian, dotProduct_sub,
    dotProduct_comm y q, hq, hy]
  module

open GNC.BearingOutput

theorem chord_norm {θ : ℝ} (hθ : 0 ≤ θ) (hπ : θ ≤ π) :
    enorm (bearing θ-bearing 0) = 2*sin (θ/2) := by
  have hsq : enorm (bearing θ-bearing 0)^2 = (cos θ-1)^2+sin θ^2 := by
    rw [enorm_sq]
    simp [lengthSq, bearing]
  have hn := enorm_nonneg (bearing θ-bearing 0)
  have hs := sin_nonneg_of_nonneg_of_le_pi (by linarith : 0≤θ/2)
    (by linarith [pi_pos] : θ/2≤π)
  have hc := cos_two_mul (θ/2)
  have hcircle := sin_sq_add_cos_sq θ
  have hhalf := sin_sq_add_cos_sq (θ/2)
  rw [show 2*(θ/2)=θ by ring] at hc
  nlinarith

theorem embedded_averaged_norm {θ : ℝ} (hθ : 0 ≤ θ) (hπ : θ ≤ π) :
    enorm (embeddedResidual (bearing 0) (bearing θ)) = 2*sin (θ/2)^3 := by
  rw [embedded_residual_factorization _ _
    (by rw [dot_self_lengthSq]; exact bearing_unit 0)
    (by rw [dot_self_lengthSq]; exact bearing_unit θ)]
  have hdot : bearing 0 ⬝ᵥ bearing θ = cos θ := by
    simp [bearing, dotProduct, Fin.sum_univ_succ]
  rw [enorm_smul, hdot, abs_of_nonneg (by positivity [sub_nonneg.mpr (cos_le_one θ)]),
    chord_norm hθ hπ]
  have hc := cos_two_mul (θ/2)
  have hs := sin_sq_add_cos_sq (θ/2)
  rw [show 2*(θ/2)=θ by ring] at hc
  have hid : 1-cos θ = 2*sin (θ/2)^2 := by nlinarith
  rw [hid]
  ring

theorem embedded_averaged_cubic_bound {θ : ℝ} (hθ : 0 ≤ θ) (hπ : θ ≤ π) :
    enorm (embeddedResidual (bearing 0) (bearing θ)) ≤ θ^3/4 := by
  rw [embedded_averaged_norm hθ hπ]
  have hs := sin_nonneg_of_nonneg_of_le_pi (by linarith : 0≤θ/2)
    (by linarith [pi_pos] : θ/2≤π)
  have hb := pow_le_pow_left₀ hs (sin_le (by linarith : 0≤θ/2)) 3
  nlinarith

/-- Averaging the embedded EKF Jacobians improves its output remainder by
an exact factor sin(theta/2), including the endpoints. -/
theorem embedded_improvement_factor {θ : ℝ} (hθ : 0 ≤ θ) (hπ : θ ≤ π) :
    enorm (embeddedResidual (bearing 0) (bearing θ)) =
      sin (θ/2)*enorm (GNC.BearingOutput.embeddedResidual θ) := by
  rw [embedded_averaged_norm hθ hπ, GNC.BearingOutput.embedded_norm]
  have hc := cos_two_mul (θ/2)
  have hs := sin_sq_add_cos_sq (θ/2)
  rw [show 2*(θ/2)=θ by ring] at hc
  have hid : 1-cos θ = 2*sin (θ/2)^2 := by nlinarith
  rw [hid]
  ring

theorem averaged_embedded_le_ordinary {θ : ℝ} (hθ : 0 ≤ θ) (hπ : θ ≤ π) :
    enorm (embeddedResidual (bearing 0) (bearing θ)) ≤
      enorm (GNC.BearingOutput.embeddedResidual θ) := by
  rw [embedded_improvement_factor hθ hπ]
  exact mul_le_of_le_one_left (enorm_nonneg _) (sin_le_one _)

/-- The residual advantage remaining after embedded averaging is an exact
coordinate-path effect, not a remaining difference of approximation order. -/
theorem advantage_identity {θ : ℝ} (hθ : 0 ≤ θ) (hπ : θ ≤ π) :
    enorm (embeddedResidual (bearing 0) (bearing θ))-
      enorm (GNC.BearingOutput.averagedResidual θ) = cos (θ/2)*(θ-sin θ) := by
  rw [embedded_averaged_norm hθ hπ, averaged_norm hθ hπ]
  have hs := sin_two_mul (θ/2)
  rw [show 2*(θ/2)=θ by ring] at hs
  have hc := congrArg (fun z : ℝ => sin (θ/2)*z) (sin_sq_add_cos_sq (θ/2))
  dsimp [amplitude] at *
  rw [hs]
  nlinarith

theorem eqf_star_le_averaged_embedded {θ : ℝ} (hθ : 0 ≤ θ) (hπ : θ ≤ π) :
    enorm (GNC.BearingOutput.averagedResidual θ) ≤
      enorm (embeddedResidual (bearing 0) (bearing θ)) := by
  have hc := cos_nonneg_of_neg_pi_div_two_le_of_le
    (by linarith [pi_pos] : -(π/2)≤θ/2) (by linarith : θ/2≤π/2)
  have h := mul_nonneg hc (sub_nonneg.mpr (sin_le hθ))
  linarith [advantage_identity hθ hπ]

theorem bearing_derivative (θ : ℝ) :
    HasDerivAt bearing (![-sin θ,cos θ,0] : Vec3) θ := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa [bearing] using hasDerivAt_cos θ
  · simpa [bearing] using hasDerivAt_sin θ
  · simpa [bearing] using hasDerivAt_const θ (0:ℝ)

/-- Residual in rotational error coordinates for a retraction EKF using
the same endpoint average. The tangent direction is the same physical
rotation path used by EqF-star. -/
def retractionResidual (θ : ℝ) : Vec3 :=
  bearing θ-bearing 0-(θ/2) • ![-sin θ,1+cos θ,0]

theorem retraction_eq_eqf_star (θ : ℝ) :
    retractionResidual θ = GNC.BearingOutput.averagedResidual θ :=
  averaged_residual_identity θ

theorem retraction_cubic_bound {θ : ℝ} (hθ : 0 ≤ θ) (hπ : θ ≤ π) :
    enorm (retractionResidual θ) ≤ θ^3/12 := by
  rw [retraction_eq_eqf_star]
  exact averaged_cubic_bound hθ hπ

end GNC.BearingComparison
