import GNC.Analysis.FiniteAngleSpan
import GNC.Applications.OrbitalComparison.SpatialPolynomialObstruction

/-! The checked sub-micrometre spatial predictor uses five fixed angular
functions. Time dependence, including exact reference-frame reconstruction,
is carried entirely by their vector amplitudes. Ordinary angle polynomials
of degree six fail on the same physical family, as proved separately. -/
noncomputable section
namespace GNC.OrbitalComparison.SpatialFiniteAngleSpan
open SpatialBurn SpatialRotatingFrame FiniteAngleSpan SpatialPolynomialObstruction
open RotatingBernsteinData.SecondCircleTime12Inverse10 (data)

theorem quadratic_data : ∀ i, FiniteAngleSpan.quadratic (data.q i) := by
  decide +kernel

def amplitudeVector (j : Fin 5) (t : ℝ) : E3 :=
  (7000000:ℝ) • mix ((UniformCertificate.omega:ℝ)*t)
    (amplitudes (data.q 0) t j) (amplitudes (data.q 1) t j) (amplitudes (data.q 2) t j)

theorem reconstruction (a : Fin 3 → Fin 5 → ℝ) (s c φ scale : ℝ) :
    scale • mix φ
      (a 0 0+s*a 0 1+c*a 0 2+(s*c)*a 0 3+c^2*a 0 4)
      (a 1 0+s*a 1 1+c*a 1 2+(s*c)*a 1 3+c^2*a 1 4)
      (a 2 0+s*a 2 1+c*a 2 2+(s*c)*a 2 3+c^2*a 2 4) =
      scale • mix φ (a 0 0) (a 1 0) (a 2 0)+
      s • (scale • mix φ (a 0 1) (a 1 1) (a 2 1))+
      c • (scale • mix φ (a 0 2) (a 1 2) (a 2 2))+
      (s*c) • (scale • mix φ (a 0 3) (a 1 3) (a 2 3))+
      c^2 • (scale • mix φ (a 0 4) (a 1 4) (a 2 4)) := by
  dsimp [mix,pack]
  module

/-- Exact representation for all times and angles. Only the subsequent
physical error certificate restricts the time and angle domain. -/
theorem retained_decomposition (θ t : ℝ) :
    retainedDeviation θ t = (amplitudeVector 0 t-SpatialExactNominal.nominal.p t)+
      Real.sin θ • amplitudeVector 1 t+(1-Real.cos θ) • amplitudeVector 2 t+
      (Real.sin θ*(1-Real.cos θ)) • amplitudeVector 3 t+
      (1-Real.cos θ)^2 • amplitudeVector 4 t := by
  change (7000000:ℝ) • mix ((UniformCertificate.omega:ℝ)*t)
    (CirclePolynomial.value (data.q 0) t θ) (CirclePolynomial.value (data.q 1) t θ)
    (CirclePolynomial.value (data.q 2) t θ)-SpatialExactNominal.nominal.p t = _
  rw [value_five _ (quadratic_data 0),value_five _ (quadratic_data 1),
    value_five _ (quadratic_data 2)]
  rw [reconstruction (fun i => amplitudes (data.q i) t)]
  change amplitudeVector 0 t+Real.sin θ • amplitudeVector 1 t+
    (1-Real.cos θ) • amplitudeVector 2 t+
    (Real.sin θ*(1-Real.cos θ)) • amplitudeVector 3 t+
    (1-Real.cos θ)^2 • amplitudeVector 4 t-SpatialExactNominal.nominal.p t = _
  abel

end GNC.OrbitalComparison.SpatialFiniteAngleSpan
