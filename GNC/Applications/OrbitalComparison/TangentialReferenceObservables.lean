import GNC.Applications.OrbitalComparison.TangentialReference
import GNC.Dynamics.PolynomialGravityObservable

/-! Certified coefficients along a computed, noncircular reference.
Both the force history and the full three-dimensional gravity gradient
include the reference integration error. This does not yet certify a deputy.
-/
noncomputable section
namespace GNC.OrbitalComparison.TangentialReference
open PolynomialODE PolynomialOrbit PolynomialOrbitTransition TangentialReferenceData Set
open Planning.PolynomialKernel

def observable (e : Expr 5) (j : ℕ) (u : ℝ) : ℝ :=
  evaluate ((e.coefficients (sequence j).coefficients).map (Rat.castHom ℝ)) u

def observableBudget (e : Expr 5) : ℚ := e.slope (4/3+errorBound)*errorBound
def gradientBudget : ℚ := (21*(4/3+errorBound)^6+3*(4/3+errorBound)^2)*errorBound
def thrustBudget : ℚ := (2*|alpha| *(4/3+errorBound))*errorBound

theorem observable_pieces (w : ℝ → Fin 4 → ℝ) (hw : Continuous w)
    (hr : ∀ t, 0<radius (w t))
    (hd : ∀ t ∈ Icc (0:ℝ) (13/20), HasDerivAt w (physicalRate (alpha:ℝ) (w t)) t)
    (hi : w 0=![1,0,0,1]) (e : Expr 5) (j : ℕ) (hj : j<32)
    (u : ℝ) (hu : u ∈ Icc (0:ℝ) (13/640)) :
    |e.value (lift (w ((j:ℝ)*(13/640)+u)))-observable e j u|≤(observableBudget e:ℝ) := by
  have he : 0≤errorBound := by norm_num [errorBound]
  have hs := (sequence j).observable_error (sequence_valid j hj)
    (by rw [sequence_duration j hj]; norm_num at hu ⊢; exact hu)
    (lift (w ((j:ℝ)*(13/640)+u))) he
    (physical_pieces w hw hr hd hi j hj u hu).le e
  have hregion : (sequence j).region=(4/3:ℚ) := by simp [sequence,hj,regions]
  simpa only [hregion,observable,observableBudget] using hs

/-- Every gravity-gradient entry, including the normal component, has an
explicit error budget inherited from the validated reference. -/
theorem gradient_pieces (w : ℝ → Fin 4 → ℝ) (hw : Continuous w)
    (hr : ∀ t, 0<radius (w t))
    (hd : ∀ t ∈ Icc (0:ℝ) (13/20), HasDerivAt w (physicalRate (alpha:ℝ) (w t)) t)
    (hi : w 0=![1,0,0,1]) (j : ℕ) (hj : j<32)
    (u : ℝ) (hu : u ∈ Icc (0:ℝ) (13/640)) (k l : Fin 3) :
    |gravityMatrix (lift (w ((j:ℝ)*(13/640)+u))) k l-
      observable (PolynomialGravityObservable.gradient k l) j u|≤(gradientBudget:ℝ) := by
  have h := observable_pieces w hw hr hd hi (PolynomialGravityObservable.gradient k l) j hj u hu
  rw [PolynomialGravityObservable.gradient_value] at h
  apply h.trans
  exact_mod_cast mul_le_mul_of_nonneg_right
    (PolynomialGravityObservable.gradient_slope
      (by norm_num [errorBound] : (0:ℚ)≤4/3+errorBound) k l)
    (by norm_num [errorBound] : (0:ℚ)≤errorBound)

theorem thrust_pieces (w : ℝ → Fin 4 → ℝ) (hw : Continuous w)
    (hr : ∀ t, 0<radius (w t))
    (hd : ∀ t ∈ Icc (0:ℝ) (13/20), HasDerivAt w (physicalRate (alpha:ℝ) (w t)) t)
    (hi : w 0=![1,0,0,1]) (j : ℕ) (hj : j<32)
    (u : ℝ) (hu : u ∈ Icc (0:ℝ) (13/640)) (k : Fin 3) :
    |PlanarChaserError.referenceThrust (alpha:ℝ) (w ((j:ℝ)*(13/640)+u)) k-
      observable (PolynomialGravityObservable.thrust alpha k) j u|≤(thrustBudget:ℝ) := by
  have h := observable_pieces w hw hr hd hi (PolynomialGravityObservable.thrust alpha k) j hj u hu
  rw [PolynomialGravityObservable.thrust_value] at h
  apply h.trans
  exact_mod_cast mul_le_mul_of_nonneg_right
    (PolynomialGravityObservable.thrust_slope alpha
      (by norm_num [errorBound] : (0:ℚ)≤4/3+errorBound) k)
    (by norm_num [errorBound] : (0:ℚ)≤errorBound)

/-- All three response forcing columns inherit the reference error. -/
theorem frameInput_pieces (w : ℝ → Fin 4 → ℝ) (hw : Continuous w)
    (hr : ∀ t, 0<radius (w t))
    (hd : ∀ t ∈ Icc (0:ℝ) (13/20), HasDerivAt w (physicalRate (alpha:ℝ) (w t)) t)
    (hi : w 0=![1,0,0,1]) (j : ℕ) (hj : j<32)
    (u : ℝ) (hu : u ∈ Icc (0:ℝ) (13/640)) (k l : Fin 3) :
    |(alpha:ℝ)*polynomialFrame (lift (w ((j:ℝ)*(13/640)+u))) k l-
      observable (PolynomialGravityObservable.frameInput alpha k l) j u|≤(thrustBudget:ℝ) := by
  have h := observable_pieces w hw hr hd hi
    (PolynomialGravityObservable.frameInput alpha k l) j hj u hu
  rw [PolynomialGravityObservable.frameInput_value] at h
  apply h.trans
  exact_mod_cast mul_le_mul_of_nonneg_right
    (PolynomialGravityObservable.frameInput_slope alpha
      (by norm_num [errorBound] : (0:ℚ)≤4/3+errorBound) k l)
    (by norm_num [errorBound] : (0:ℚ)≤errorBound)

/-- Existence and the numerical enclosure are combined; no exact numerical
ephemeris or noncollision assumption is needed to obtain this witness. -/
theorem exists_certified_reference :
    ∃ w : ℝ → Fin 4 → ℝ, Continuous w ∧ (∀ t, 0<radius (w t)) ∧
      w 0=![1,0,0,1] ∧
      (∀ t ∈ Icc (0:ℝ) (13/20), HasDerivAt w (physicalRate (alpha:ℝ) (w t)) t) ∧
      (∀ t ∈ Icc (0:ℝ) (13/20), ∃ j : ℕ, j<32 ∧ ∃ u ∈ Icc (0:ℝ) (13/640),
        t=(j:ℝ)*(13/640)+u ∧
          ‖lift (w t)-curve (sequence j).coefficients u‖<(errorBound:ℝ)) ∧
      (7712524/1000000:ℝ)<7000000*(radius (w (13/20))-1) ∧
      7000000*(radius (w (13/20))-1)<7712531/1000000 := by
  obtain ⟨w,hw,hr,hi,hd⟩ := exists_physical
  refine ⟨w,hw,hr,hi,hd,physical_enclosure w hw hr hd hi,?_⟩
  obtain ⟨hl,hu⟩ := endpoint_radius w hw hr hd hi
  have hs : (7712524/1000000:ℝ)<7000000*((radialLower:ℝ)-1) ∧
      7000000*((radialUpper:ℝ)-1)<7712531/1000000 := by
    norm_num [radialLower,radialUpper]
  constructor <;> linarith

end GNC.OrbitalComparison.TangentialReference
