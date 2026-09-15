import GNC.Analysis.DiskPolynomial
import GNC.Applications.OrbitalComparison.PointingCapRefinement

/-! Apply checked disk decompositions to the existing physical predictors.
The original coefficients and physical solution are reused. Every replacement
range estimate is proved on the complete pointing cap and time interval. -/
namespace GNC.OrbitalComparison.PointingCapDisk
open PointingCapCertificate PointingCapPolynomial PointingCapBurn
open PointingCapRefinement SpatialBurn Set

def depth (σ : ℚ) : ℚ := σ^2/(2-σ^2)

structure Models where
  position : DiskPolynomial.Certificate 3
  first : DiskPolynomial.Certificate 3
  second : DiskPolynomial.Certificate 3
  remainder : DiskPolynomial.Certificate 3

def Models.rawBounds (M : Models) (D : Data) : Bounds :=
  ⟨M.position.bound D.sigma (depth D.sigma),M.first.bound D.sigma (depth D.sigma),
    M.second.bound D.sigma (depth D.sigma),M.remainder.bound D.sigma (depth D.sigma)⟩

def Models.refinedBounds (M : Models) (D : Data) : Bounds :=
  (coefficientBounds D).minimum (M.rawBounds D)

structure Models.Valid (M : Models) (D : Data) : Prop where
  position : M.position.Valid D.q D.sigma (depth D.sigma) (M.rawBounds D).position
  first : M.first.Valid D.first D.sigma (depth D.sigma) (M.rawBounds D).first
  second : M.second.Valid (difference D.q D.first) D.sigma (depth D.sigma) (M.rawBounds D).second
  remainder : M.remainder.Valid D.remainder D.sigma (depth D.sigma) (M.rawBounds D).remainder

noncomputable section

theorem vector_value_eq (p : PointingCapPolynomial.Vector) (x : Fin 3 → ℝ) (t : ℝ) :
    DiskPolynomial.vectorValue p x t=vectorValue p x t := by
  ext i
  fin_cases i <;> simp [DiskPolynomial.vectorValue,vectorValue,pack_eq]

theorem certified_vector_bound (M : DiskPolynomial.Certificate 3)
    (p : PointingCapPolynomial.Vector) {σ B : ℚ}
    (hM : M.Valid p σ (depth σ) B) (hσ : 0≤σ) (hs : σ^2<1)
    {x : Fin 3 → ℝ} (hx : Admissible (σ:ℝ) x) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ‖vectorValue p x t‖≤(B:ℝ) := by
  have hr := parameter_bounds (show (0:ℝ)≤σ by exact_mod_cast hσ)
    (show (σ:ℝ)^2<1 by exact_mod_cast hs) hx
  have hc : |x 2|≤(depth σ:ℝ) := by simpa [depth] using hr.2.2
  simpa only [vector_value_eq] using M.certifies p hM hσ hx.2.2.2 hc ht

theorem Models.rawBounds_sound (M : Models) (D : Data) (hD : D.Valid)
    (hM : M.Valid D) : (M.rawBounds D).Sound D := by
  have h (model : DiskPolynomial.Certificate 3) (p : PointingCapPolynomial.Vector) (B : ℚ)
      (hv : model.Valid p D.sigma (depth D.sigma) B)
      (x : Fin 3 → ℝ) (hx : Admissible (D.sigma:ℝ) x) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :=
    certified_vector_bound model p hv hD.sigma_pos.le (D.valid_sigma hD) hx ht
  refine ⟨h _ _ _ hM.position,h _ _ _ hM.first,?_,h _ _ _ hM.remainder⟩
  intro x hx t ht
  simpa only [vector_difference] using h _ _ _ hM.second x hx t ht

theorem Models.refinedBounds_sound (M : Models) (D : Data) (hD : D.Valid)
    (hM : M.Valid D) : (M.refinedBounds D).Sound D :=
  Bounds.minimum_sound _ _ D (coefficientBounds_sound D hD) (M.rawBounds_sound D hD hM)

/-- New disk estimates retain the complete inverse-square physical guarantee.
The region and scalar comparison checks remain explicit obligations. -/
theorem Models.physical_prediction (M : Models) (D : Data) (hD : D.Valid)
    (hM : M.Valid D) (hC : (M.refinedBounds D).Checks D)
    {x : Fin 3 → ℝ} (hx : Admissible (D.sigma:ℝ) x) :
    ∀ t ∈ Icc (0:ℝ) 1,
      ‖(D.trajectory hD x hx).p t-D.position x t‖≤((M.refinedBounds D).positionError D:ℝ) ∧
      ‖(D.trajectory hD x hx).v t-D.velocity x t‖/(600*(D.alpha:ℝ))≤
        ((M.refinedBounds D).velocityError D:ℝ) :=
  Bounds.physical_prediction _ D hD (M.refinedBounds_sound D hD hM) hC hx

end
end GNC.OrbitalComparison.PointingCapDisk
