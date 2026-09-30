import GNC.Analysis.PolynomialResponseTransfer
import GNC.Applications.OrbitalComparison.CompressedCartesian
import GNC.Applications.OrbitalComparison.PoweredCircularExistence

/-! Mixed-degree geometric and Cartesian responses. Every removed term is
charged by a uniform coefficient bound, including the geometric output gain.
The same physical orbit and uncertainty ball are used for both predictors.
-/
noncomputable section
namespace GNC.OrbitalComparison.PrunedFinitePrediction
open LinearResponsePolynomial PolynomialResponseTransfer Set Matrix
open FiniteResponseData (horizon theta)
open PoweredCircularLogTube (rate angleRadius reference)
open FiniteCircularResponse (basis basis_norm)
open GeometricSTMPrediction (E)

def geometric : Coefficients 3 3 := fun i j =>
  (FiniteResponseData.coefficients i j).take (if i=2 ∧ j=0 then 6 else 8)

def cartesianKeep : Fin 3 → Fin 6 → ℕ :=
  ![![5,6,6,0,9,9],![0,7,7,4,9,9],![9,9,9,9,7,6]]

def cartesian : Coefficients 3 6 := fun i j =>
  (CompressedCartesian.six i j).take (cartesianKeep i j)

def geometricLoss : ℚ := LinearResponsePolynomial.budget
  (difference FiniteResponseData.coefficients geometric) (fun _ => theta) horizon
def cartesianLoss : ℚ := LinearResponsePolynomial.budget
  (difference CompressedCartesian.six cartesian) (FiniteCartesianData.featureRadii .quadratic) horizon
def geometricBudget : ℚ := FiniteResponseData.predictionBudget+
  FiniteResponseData.reconstructionTail*FiniteResponseData.responseRadius+(1+theta/2)*geometricLoss
def cartesianBudget : ℚ := CompressedCartesian.budget+cartesianLoss

def geometricPosition (φ : Vec3) (t : ℝ) : E :=
  WithLp.toLp 2 (JacobianAffine.apply φ (response basis geometric φ (rate*t)).ofLp)
def cartesianPosition (φ : Vec3) (t : ℝ) : E :=
  response basis cartesian (FiniteCartesianResponse.features .quadratic φ) (rate*t)

theorem targets : 7000000*geometricBudget<963/1000000 ∧
    7000000*cartesianBudget<974/1000000 := by decide +kernel

theorem phase_bound {t : ℝ} (ht : t∈Icc (0:ℝ) 1) : |rate*t|≤(horizon:ℝ) := by
  rw [abs_mul]
  have hh : (0:ℝ)≤horizon := by exact_mod_cast CompressedCartesian.horizon_pos.le
  exact (mul_le_mul FiniteCircularResponse.rate_bound
    (show |t|≤1 by rw [abs_of_nonneg ht.1]; exact ht.2) (abs_nonneg _) hh).trans_eq (mul_one _)

theorem affine_difference_bound (φ u v : Vec3) :
    enorm (JacobianAffine.apply φ u-JacobianAffine.apply φ v)≤
      (1+enorm φ/2)*enorm (u-v) := by
  have he : JacobianAffine.apply φ u-JacobianAffine.apply φ v=
      (u-v)+(1/2:ℝ) • (φ ⨯₃ (u-v)) := by
    simp only [JacobianAffine.apply, map_sub]
    module
  rw [he]
  apply (enorm_add_le _ _).trans
  rw [enorm_smul, abs_of_pos (by norm_num : (0:ℝ)<1/2)]
  have h := cross_enorm_le φ (u-v)
  nlinarith

theorem differences (φ : Vec3) (hφ : enorm φ≤angleRadius) {t : ℝ}
    (ht : t∈Icc (0:ℝ) 1) :
    ‖WithLp.toLp 2 (JacobianAffine.apply φ (FiniteCircularResponse.position φ t).ofLp)-
      geometricPosition φ t‖≤((1+theta/2)*geometricLoss:ℚ) ∧
    ‖CompressedCartesian.position φ t-cartesianPosition φ t‖≤(cartesianLoss:ℝ) := by
  have hh := CompressedCartesian.horizon_pos.le
  have hg := difference_bound basis basis_norm FiniteResponseData.coefficients geometric φ
    (fun _ => theta) (FiniteCircularResponse.feature_bound φ hφ) hh (phase_bound ht)
  have hc := difference_bound basis basis_norm CompressedCartesian.six cartesian
    (FiniteCartesianResponse.features .quadratic φ) (FiniteCartesianData.featureRadii .quadratic)
    (FiniteCartesianResponse.feature_bound .quadratic φ hφ) hh (phase_bound ht)
  refine ⟨?_,hc⟩
  have hθ : enorm φ≤(theta:ℝ) := hφ.trans_eq FiniteCircularCertificate.input_casts.2.2.symm
  have hb := affine_difference_bound φ (FiniteCircularResponse.position φ t).ofLp
    (response basis geometric φ (rate*t)).ofLp
  change enorm ((FiniteCircularResponse.position φ t).ofLp-
    (response basis geometric φ (rate*t)).ofLp)≤(geometricLoss:ℝ) at hg
  change enorm _≤_
  exact hb.trans ((mul_le_mul (by linarith : 1+enorm φ/2≤1+(theta:ℝ)/2) hg
    (enorm_nonneg _) (by norm_num [theta])).trans_eq (by push_cast; rfl))

/-- Same full inverse-square physical solution; no extra residual hypothesis. -/
theorem certificates (φ : Vec3) (hφ : enorm φ≤angleRadius)
    (X : PoweredCircularExistence.Motion φ) {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    ‖X.p t-(reference t+geometricPosition φ t)‖≤(geometricBudget:ℝ) ∧
    ‖X.p t-(reference t+cartesianPosition φ t)‖≤(cartesianBudget:ℝ) := by
  have hg := FiniteCircularCertificate.certificate φ hφ X.p X.v X.continuous_p
    X.continuous_v X.derivative_p X.derivative_v X.initial_p X.initial_v t ht
  have hc := CompressedCartesian.certificate φ hφ X.p X.v X.continuous_p
    X.continuous_v X.derivative_p X.derivative_v X.initial_p X.initial_v t ht
  have hd := differences φ hφ ht
  constructor
  · have hn := dist_triangle (X.p t) (FiniteCircularCertificate.prediction φ t)
      (reference t+geometricPosition φ t)
    simp only [dist_eq_norm, FiniteCircularCertificate.prediction, add_sub_add_left_eq_sub] at hn
    exact hn.trans (by simpa [geometricBudget, Rat.cast_add, Rat.cast_mul, add_assoc] using add_le_add hg hd.1)
  · have hn := dist_triangle (X.p t) (reference t+CompressedCartesian.position φ t)
      (reference t+cartesianPosition φ t)
    simp only [dist_eq_norm, add_sub_add_left_eq_sub] at hn
    exact hn.trans (by simpa [cartesianBudget, Rat.cast_add] using add_le_add hc hd.2)

end GNC.OrbitalComparison.PrunedFinitePrediction
