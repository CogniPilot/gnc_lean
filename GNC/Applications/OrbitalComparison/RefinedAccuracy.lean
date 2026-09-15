import GNC.Analysis.BivariateDegree
import GNC.Applications.OrbitalComparison.SpatialFiniteAngleSpan
import GNC.Applications.OrbitalComparison.ExactNominalData.SecondCHEB8Time12Inverse10
import GNC.Applications.OrbitalComparison.ExactNominalData.FullSTT8Time12Inverse10
import GNC.Applications.OrbitalComparison.ExactNominalData.FullCHEB7Time12Inverse10

/-! Matched physical certificates permitting higher-degree polynomials.
The physical solution is constructed, not assumed. Degree seven suffices
for the one-micrometre endpoint requirement and degree six cannot suffice.
Operation counts are separate reproducible measurements, not Lean claims. -/
noncomputable section
namespace GNC.OrbitalComparison.RefinedAccuracy
open Set SpatialBurn SpatialRotatingFrame SpatialPolynomialObstruction
open RotatingBernsteinData.FullCHEB7Time12Inverse10 (data)

theorem chebyshev_eight {θ : ℝ} (hθ : |θ| ≤ 7/20) :
    ∀ t ∈ Icc (0:ℝ) 1,
      ‖physicalDeviation θ t-(SpatialRotatingCertificate.position SpatialSources.ordinary
        RotatingBernsteinData.SecondCHEB8Time12Inverse10.data.q θ t-
          SpatialExactNominal.nominal.p t)‖ ≤ (123021/125000000000:ℝ) := by
  intro t ht
  exact (ExactNominalData.SecondCHEB8Time12Inverse10.relative_prediction
    (SpatialExistence.trajectory .rtnReferenceOffset θ) SpatialExactNominal.nominal hθ t ht).1

theorem taylor_eight {θ : ℝ} (hθ : |θ| ≤ 7/20) :
    ∀ t ∈ Icc (0:ℝ) 1,
      ‖physicalDeviation θ t-(SpatialRotatingCertificate.position SpatialSources.ordinary
        RotatingBernsteinData.FullSTT8Time12Inverse10.data.q θ t-
          SpatialExactNominal.nominal.p t)‖ ≤ (957869/1000000000000:ℝ) := by
  intro t ht
  exact (ExactNominalData.FullSTT8Time12Inverse10.relative_prediction
    (SpatialExistence.trajectory .rtnReferenceOffset θ) SpatialExactNominal.nominal hθ t ht).1

theorem width_data : ∀ i, ∀ a ∈ data.q i, a.length ≤ 8 := by decide +kernel

def coordinate (j : Fin 3) (t : ℝ) : Polynomial ℝ := BivariateDegree.atTime (data.q j) t

def predictor (t : ℝ) : Fin 3 → Polynomial ℝ :=
  let C := Polynomial.C
  let c := Real.cos ((UniformCertificate.omega:ℝ)*t)
  let s := Real.sin ((UniformCertificate.omega:ℝ)*t)
  ![C (7000000*c)*coordinate 0 t-C (7000000*s)*coordinate 1 t-C (SpatialExactNominal.nominal.p t 0),
    C (7000000*s)*coordinate 0 t+C (7000000*c)*coordinate 1 t-C (SpatialExactNominal.nominal.p t 1),
    C 7000000*coordinate 2 t-C (SpatialExactNominal.nominal.p t 2)]

theorem predictor_degree (t : ℝ) (j : Fin 3) : (predictor t j).natDegree ≤ 7 := by
  have hc (j : Fin 3) : (coordinate j t).natDegree ≤ 7 :=
    BivariateDegree.degree (data.q j) (width_data j) t
  have hmul (a : ℝ) (j : Fin 3) : (Polynomial.C a*coordinate j t).natDegree ≤ 7 :=
    (Polynomial.natDegree_C_mul_le _ _).trans (hc j)
  have hconst (a : ℝ) : (Polynomial.C a).natDegree ≤ 7 := by simp
  fin_cases j
  · exact (Polynomial.natDegree_sub_le _ _).trans (max_le
      ((Polynomial.natDegree_sub_le _ _).trans (max_le (hmul _ 0) (hmul _ 1))) (hconst _))
  · exact (Polynomial.natDegree_sub_le _ _).trans (max_le
      ((Polynomial.natDegree_add_le _ _).trans (max_le (hmul _ 0) (hmul _ 1))) (hconst _))
  · exact (Polynomial.natDegree_sub_le _ _).trans (max_le (hmul _ 2) (hconst _))

theorem predictor_evaluation (t θ : ℝ) :
    WithLp.toLp 2 (fun j => (predictor t j).eval θ) =
      SpatialRotatingCertificate.position SpatialSources.ordinary data.q θ t-
        SpatialExactNominal.nominal.p t := by
  change WithLp.toLp 2 (fun j => (predictor t j).eval θ) =
    (7000000:ℝ) • mix ((UniformCertificate.omega:ℝ)*t)
      (BivariatePolynomial.value (data.q 0) t θ) (BivariatePolynomial.value (data.q 1) t θ)
      (BivariatePolynomial.value (data.q 2) t θ)-SpatialExactNominal.nominal.p t
  ext j
  fin_cases j <;>
    simp [predictor,coordinate,BivariateDegree.evaluation,mix,pack,e0,e1,e2,
      Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail] <;> ring

theorem predictor_error {θ : ℝ} (hθ : |θ| ≤ 7/20) :
    ∀ t ∈ Icc (0:ℝ) 1,
      ‖physicalDeviation θ t-WithLp.toLp 2 (fun j => (predictor t j).eval θ)‖ ≤
        (822049/1000000000000:ℝ) := by
  intro t ht
  rw [predictor_evaluation]
  exact (ExactNominalData.FullCHEB7Time12Inverse10.relative_prediction
    (SpatialExistence.trajectory .rtnReferenceOffset θ) SpatialExactNominal.nominal hθ t ht).1

/-- The minimum ordinary-polynomial degree for a uniform one-micrometre
endpoint predictor is exactly seven, allowing arbitrary real coefficients.
This concerns polynomial degree, not sparse coefficient count or runtime. -/
theorem minimum_degree (d : ℕ) :
    (∃ p : Fin 3 → Polynomial ℝ, (∀ j, (p j).natDegree ≤ d) ∧
      ∀ θ : ℝ, |θ| ≤ 7/20 →
        ‖physicalDeviation θ 1-WithLp.toLp 2 (fun j => (p j).eval θ)‖ ≤ (1/1000000:ℝ)) ↔
      7 ≤ d := by
  constructor
  · rintro ⟨p,hdegree,herror⟩
    by_contra h
    have hd : d ≤ 6 := by omega
    obtain ⟨θ,hθ,hbad⟩ := (physical_comparison p ((hdegree 1).trans hd)).2
    linarith [herror θ hθ]
  · intro hd
    refine ⟨predictor 1,fun j => (predictor_degree 1 j).trans hd,?_⟩
    intro θ hθ
    exact (predictor_error hθ 1 (by norm_num)).trans (by norm_num)

end GNC.OrbitalComparison.RefinedAccuracy
