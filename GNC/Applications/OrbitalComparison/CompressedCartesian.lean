import GNC.Analysis.ChebyshevCompression
import GNC.Applications.OrbitalComparison.FiniteCartesianCertificate

/-! A stronger Cartesian comparator: transfer the checked degree-eight
physical certificate to a degree-six whole-interval approximation. The
transfer charges both Chebyshev compression losses, with no new ODE solve.
-/
namespace GNC.OrbitalComparison.CompressedCartesian
open ChebyshevCompression LinearResponsePolynomial Set
open FiniteResponseData (horizon)
open PoweredCircularLogTube (rate angleRadius μ reference referenceVelocity thrust lengthScale)
open GeometricSTMPrediction (E force)
open FiniteCircularResponse (basis basis_norm)

def seven : Coefficients 3 6 := fun i j =>
  compress 8 (annihilator horizon) (FiniteCartesianData.coefficients i j)
def six : Coefficients 3 6 := fun i j => compress 7 (annihilator7 horizon) (seven i j)
def loss8 : ℚ := loss FiniteCartesianData.coefficients
  (FiniteCartesianData.featureRadii .quadratic) 8 (horizon^8/32)
def loss7 : ℚ := loss seven (FiniteCartesianData.featureRadii .quadratic) 7 (horizon^7/8)
def budget : ℚ := FiniteCartesianData.predictionBudget .quadratic+loss8+loss7

/-- The two canceled highest coefficients are exactly zero, and the
initial value and slope remain zero. Thus six is of degree at most six. -/
theorem degree_and_initial : ∀ i j,
    (six i j).drop 7=[0,0] ∧ PolynomialTimeProfile.zeroPrefix 2 (six i j) := by
  decide +kernel

theorem target : 7000000*budget<749/1000000 := by decide +kernel
theorem horizon_pos : 0<horizon := by decide +kernel

noncomputable def position (φ : Vec3) (t : ℝ) : E :=
  response basis six (FiniteCartesianResponse.features .quadratic φ) (rate*t)

theorem difference (φ : Vec3) (hφ : enorm φ≤angleRadius)
    {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    ‖FiniteCartesianResponse.position .quadratic φ t-position φ t‖≤(loss8+loss7:ℚ) := by
  have hh : (0:ℝ)≤horizon := by exact_mod_cast horizon_pos.le
  have hs : |rate*t|≤(horizon:ℝ) := by
    rw [abs_mul]
    exact (mul_le_mul FiniteCircularResponse.rate_bound
      (show |t|≤1 by rw [abs_of_nonneg ht.1]; exact ht.2)
      (abs_nonneg _) hh).trans_eq (mul_one _)
  have hs0 : 0≤rate*t := mul_nonneg (Real.sqrt_nonneg _) ht.1
  have hw8 : |PolynomialOrder.value (annihilator horizon) (rate*t)|≤(horizon^8/32:ℚ) := by
    simpa only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat] using annihilator_bound horizon_pos hs
  have hw7 : |PolynomialOrder.value (annihilator7 horizon) (rate*t)|≤(horizon^7/8:ℚ) := by
    simpa only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat] using
      annihilator7_bound horizon_pos hs0 ((le_abs_self _).trans hs)
  have h8 := response_difference_bound basis basis_norm FiniteCartesianData.coefficients
    (FiniteCartesianResponse.features .quadratic φ) (FiniteCartesianData.featureRadii .quadratic)
    (FiniteCartesianResponse.feature_bound .quadratic φ hφ) 8 (annihilator horizon) hw8
  have h7 := response_difference_bound basis basis_norm seven
    (FiniteCartesianResponse.features .quadratic φ) (FiniteCartesianData.featureRadii .quadratic)
    (FiniteCartesianResponse.feature_bound .quadratic φ hφ) 7 (annihilator7 horizon) hw7
  have hn := dist_triangle (FiniteCartesianResponse.position .quadratic φ t)
    (response basis seven (FiniteCartesianResponse.features .quadratic φ) (rate*t)) (position φ t)
  simp only [dist_eq_norm] at hn
  exact hn.trans (by
    simpa [loss8, loss7, seven, six, position, FiniteCartesianResponse.position]
      using add_le_add h8 h7)

/-- Uniform physical certificate inherited from the degree-eight witness,
not a claimed small differential residual of the compressed candidate. -/
theorem certificate (φ : Vec3) (hφ : enorm φ≤angleRadius) (x xv : ℝ → E)
    (hx : Continuous x) (hxv : Continuous xv)
    (hdx : ∀ t∈Icc (0:ℝ) 1, HasDerivAt x (xv t) t)
    (hdxv : ∀ t∈Icc (0:ℝ) 1, HasDerivAt xv (Gravity.field μ (x t)+force φ (thrust t)) t)
    (hix : x 0=reference 0) (hixv : xv 0=referenceVelocity 0) :
    ∀ t∈Icc (0:ℝ) 1, ‖x t-(reference t+position φ t)‖≤(budget:ℝ) := by
  intro t ht
  have hc := FiniteCartesianCertificate.certificate .quadratic φ hφ x xv hx hxv hdx hdxv hix hixv t ht
  have hd := difference φ hφ ht
  have hn := dist_triangle (x t) (FiniteCartesianCertificate.prediction .quadratic φ t)
    (reference t+position φ t)
  have he : ‖FiniteCartesianCertificate.prediction .quadratic φ t-(reference t+position φ t)‖≤(loss8+loss7:ℚ) := by
    simpa only [FiniteCartesianCertificate.prediction, add_sub_add_left_eq_sub] using hd
  simp only [dist_eq_norm] at hn
  exact hn.trans (by simpa [budget, add_assoc] using add_le_add hc he)

end GNC.OrbitalComparison.CompressedCartesian
