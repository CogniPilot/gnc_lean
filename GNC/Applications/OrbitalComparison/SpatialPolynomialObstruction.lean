import GNC.Analysis.PolynomialObstruction
import GNC.Applications.OrbitalComparison.PolynomialObstructionData
import GNC.Applications.OrbitalComparison.SpatialTerminalCertificate
import GNC.Applications.OrbitalComparison.ExactNominalData.SecondCircleTime12Inverse10
import GNC.Applications.OrbitalComparison.SpatialExistence

/-! An obstruction for the entire degree-six polynomial endpoint class.
The finite witness uses the certified physical trajectory, not a selected
Taylor or Chebyshev coefficient set. Arbitrary real polynomial coefficients
are allowed. The retained-angle candidate, checked separately against full
gravity, uniformly beats this class's lower bound.
-/
noncomputable section
namespace GNC.OrbitalComparison.SpatialPolynomialObstruction
open Set SpatialBurn SpatialFieldCertificate CircleEvaluation PolynomialObstructionData

/-- The paper's explicit barycentric construction of the eight-node witness. -/
def barycentric (i : Fin 8) : ℚ :=
  (∏ j ∈ Finset.univ.erase i, (nodes i-nodes j))⁻¹

theorem weights_barycentric : ∀ i : Fin 8,
    weights i = barycentric i / ∑ j, |barycentric j| := by decide +kernel

/-- Outward display bounds for the witness signal and its complete charged
error, in metres. Neither constant is a physical or integration allowance. -/
theorem witness_signal_lower :
    (410175/100000000000:ℚ) < |∑ i, weights i*reported i| := by decide +kernel

theorem witness_error_upper :
    ∑ i, |weights i| * (sampleError i+physicalError) < (22084/100000000000:ℚ) :=
  by decide +kernel

theorem moments_real : ∀ k ≤ 6,
    ∑ i, (weights i:ℝ)*(nodes i:ℝ)^k = 0 := by
  intro k hk
  exact_mod_cast moments ⟨k,by omega⟩

theorem variation_real : ∑ i, |(weights i:ℝ)| = 1 := by
  exact_mod_cast total_variation

theorem sample_bound (i : Fin 8) :
    |(position SpatialSources.circle SpatialData.RTNFrameCircleTime14.data.q
        (nodes i:ℝ) 1) 1-(reported i:ℝ)| ≤ (sampleError i:ℝ) := by
  have h := pointExpr.rounded_evaluation_error (center (nodes i)) (fun _ => 1)
    (fun _ => radius (nodes i)) (fun _ => by norm_num)
    (fun _ => by unfold radius; positivity) (regions i)
    (reported i) (sampleError i) (samples_checked i)
    (inputs (nodes i:ℝ)) (input_error (nodes i))
  rw [SpatialTerminalCertificate.position_component]
  simpa only [pointExpr,PolynomialODE.Expr.value,expression_value,Rat.cast_ofNat,
    Rat.cast_one] using h

theorem physical_sample_bound (i : Fin 8)
    (X : PhysicalOrbit .rtnReferenceOffset (nodes i:ℝ)) :
    |X.p 1 1-(reported i:ℝ)| ≤ (sampleError i+physicalError:ℚ) := by
  have hθ : |(nodes i:ℝ)| ≤ 7/20 := by
    have h : |(nodes i:ℝ)| ≤ ((7/20:ℚ):ℝ) := by exact_mod_cast angles i
    norm_num at h
    exact h
  have h := (SpatialData.RTNFrameCircleTime14.prediction X hθ 1 (by norm_num)).1
  have hc := (PiLp.norm_apply_le
    (X.p 1-position SpatialSources.circle SpatialData.RTNFrameCircleTime14.data.q
      (nodes i:ℝ) 1) 1).trans h
  change |X.p 1 1-(position SpatialSources.circle
    SpatialData.RTNFrameCircleTime14.data.q (nodes i:ℝ) 1) 1| ≤ _ at hc
  have ht := abs_sub_le (X.p 1 1)
    ((position SpatialSources.circle SpatialData.RTNFrameCircleTime14.data.q
      (nodes i:ℝ) 1) 1) (reported i:ℝ)
  have hs := sample_bound i
  push_cast
  dsimp [physicalError]
  linarith

/-- No polynomial of degree at most six approximates even this single
inertial position component to 3.88 micrometres on the entire angle interval.
Subtracting any common reference position does not remove the obstruction. -/
theorem coordinate_error_gt
    (X : ∀ i : Fin 8, PhysicalOrbit .rtnReferenceOffset (nodes i:ℝ))
    (reference : ℝ) (p : Polynomial ℝ) (hp : p.natDegree ≤ 6) :
    ∃ i, (388/100000000:ℝ) < |((X i).p 1 1-reference)-p.eval (nodes i:ℝ)| := by
  let p' := p+Polynomial.C reference
  have hp' : p'.natDegree ≤ 6 :=
    (Polynomial.natDegree_add_le p (Polynomial.C reference)).trans (max_le hp (by simp))
  have hscore : (388/100000000:ℝ) <
      |∑ i, (weights i:ℝ)*(reported i:ℝ)|-
        ∑ i, |(weights i:ℝ)| * ((sampleError i+physicalError:ℚ):ℝ) := by
    have h : ((388/100000000:ℚ):ℝ) < (lowerBound:ℝ) := by
      exact_mod_cast lower_bound_checked
    simpa [lowerBound] using h
  obtain ⟨i,hi⟩ := PolynomialObstruction.exists_error_gt
    (fun i => (nodes i:ℝ)) (fun i => (weights i:ℝ))
    (fun i => (X i).p 1 1) (fun i => (reported i:ℝ))
    (fun i => ((sampleError i+physicalError:ℚ):ℝ))
    moments_real variation_real (fun i => physical_sample_bound i (X i)) p' hp' hscore
  refine ⟨i,?_⟩
  simpa only [p',Polynomial.eval_add,Polynomial.eval_C,sub_add_eq_sub_sub,
    sub_right_comm] using hi

/-- In particular, every vector-valued degree-six endpoint polynomial has
an actual Euclidean error above the stated threshold at an admitted angle. -/
theorem endpoint_error_gt
    (X : ∀ i : Fin 8, PhysicalOrbit .rtnReferenceOffset (nodes i:ℝ))
    (reference : E3) (p : Fin 3 → Polynomial ℝ)
    (hp : (p 1).natDegree ≤ 6) :
    ∃ i, (388/100000000:ℝ) <
      ‖((X i).p 1-reference)-WithLp.toLp 2 (fun j => (p j).eval (nodes i:ℝ))‖ := by
  obtain ⟨i,hi⟩ := coordinate_error_gt X (reference 1) (p 1) hp
  refine ⟨i,hi.trans_le ?_⟩
  exact PiLp.norm_apply_le
    (((X i).p 1-reference)-WithLp.toLp 2 (fun j : Fin 3 => (p j).eval (nodes i:ℝ))) 1

/-- The structured time-12/inverse-10 predictor is uniformly below one
micrometre, including full gravity and its exact physical nominal. -/
theorem structured_error_lt
    {θ : ℝ} (X : PhysicalOrbit .rtnReferenceOffset θ)
    (X₀ : PhysicalOrbit .rtnReferenceOffset 0) (hθ : |θ| ≤ 7/20) :
    ∀ t ∈ Icc (0:ℝ) 1,
      ‖(X.p t-X₀.p t)-
        (SpatialRotatingCertificate.position SpatialSources.circle
          RotatingBernsteinData.SecondCircleTime12Inverse10.data.q θ t-
          SpatialExactNominal.nominal.p t)‖ < (1/1000000:ℝ) := by
  intro t ht
  exact (ExactNominalData.SecondCircleTime12Inverse10.relative_prediction
    X X₀ hθ t ht).1.trans_lt (by norm_num)

/-- The actual physical deviation is defined using a constructed solution.
`SpatialExistence.trajectory_unique` proves independence of the selection. -/
def physicalDeviation (θ t : ℝ) : E3 :=
  (SpatialExistence.trajectory .rtnReferenceOffset θ).p t-SpatialExactNominal.nominal.p t

def retainedDeviation (θ t : ℝ) : E3 :=
  SpatialRotatingCertificate.position SpatialSources.circle
    RotatingBernsteinData.SecondCircleTime12Inverse10.data.q θ t-SpatialExactNominal.nominal.p t

/-- The error separation with no physical trajectory, existence, radius,
or noncollision assumptions. All physical parameters and initial data are
fixed by the benchmark; the polynomial coefficients remain arbitrary. -/
theorem physical_comparison (p : Fin 3 → Polynomial ℝ) (hp : (p 1).natDegree ≤ 6) :
    (∀ θ : ℝ, |θ| ≤ 7/20 → ∀ t ∈ Icc (0:ℝ) 1,
      ‖physicalDeviation θ t-retainedDeviation θ t‖ ≤ (989067/1000000000000:ℝ)) ∧
    ∃ θ : ℝ, |θ| ≤ 7/20 ∧ (388/100000000:ℝ) <
      ‖physicalDeviation θ 1-WithLp.toLp 2 (fun j => (p j).eval θ)‖ := by
  constructor
  · intro θ hθ t ht
    exact (ExactNominalData.SecondCircleTime12Inverse10.relative_prediction
      (SpatialExistence.trajectory .rtnReferenceOffset θ) SpatialExactNominal.nominal hθ t ht).1
  · obtain ⟨i,hi⟩ := endpoint_error_gt
      (fun i => SpatialExistence.trajectory .rtnReferenceOffset (nodes i:ℝ))
      (SpatialExactNominal.nominal.p 1) p hp
    refine ⟨(nodes i:ℝ),?_,hi⟩
    have h : |(nodes i:ℝ)| ≤ ((7/20:ℚ):ℝ) := by exact_mod_cast angles i
    norm_num at h
    exact h

end GNC.OrbitalComparison.SpatialPolynomialObstruction
