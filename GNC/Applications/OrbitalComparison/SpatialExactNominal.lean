import GNC.Applications.OrbitalComparison.SpatialRotatingCertificate

/-! An exact physical nominal for the powered-circle spatial benchmark.
The circle's inverse-square-plus-thrust dynamics were already proved in
`PoweredCircle`. This file connects that solution to `PhysicalOrbit`, proves
uniqueness using the existing candidate-derived region, and removes the
unnecessary sum of two absolute prediction budgets. Both representations
use the same analytic nominal; no numerical nominal is silently trusted.
-/
noncomputable section
namespace GNC.OrbitalComparison.SpatialExactNominal
open Set SpatialBurn SpatialFieldCertificate SpatialRotatingFrame
open UniformCertificate WeightedCertificate
open scoped RealInnerProductSpace

def plane : PoweredCircle.Plane E3 where
  x := e0
  y := e1
  norm_x := by
    have h := pack_norm_sq 1 0 0
    simp only [pack, zero_smul, one_smul, add_zero] at h
    nlinarith [norm_nonneg e0]
  norm_y := by
    have h := pack_norm_sq 0 1 0
    simp only [pack, zero_smul, one_smul, add_zero, zero_add] at h
    nlinarith [norm_nonneg e1]
  orthogonal := by
    norm_num [e0, e1, PiLp.inner_apply, Fin.sum_univ_succ]

theorem source_zero (t : ℝ) :
    SpatialBurn.source .rtnReferenceOffset 0 t =
      plane.radial (PoweredCircle.rate*t) := by
  rw [rtn_source, UniformCertificate.constants.1]
  simp [mix, pack, PoweredCircle.Plane.radial, plane]

/-- A globally defined, nonsingular nominal with the exact physical data. -/
def nominal : PhysicalOrbit .rtnReferenceOffset 0 where
  p := plane.reference
  v := plane.velocity
  continuous_p := continuous_iff_continuousAt.mpr fun t =>
    (plane.physical_reference t).1.continuousAt
  continuous_v := continuous_iff_continuousAt.mpr fun t =>
    (plane.physical_reference t).2.continuousAt
  initial_p := by simp [PoweredCircle.Plane.reference, PoweredCircle.Plane.radial, plane]
  initial_v := by
    rw [UniformCertificate.constants.1]
    simp [PoweredCircle.Plane.velocity, PoweredCircle.Plane.tangent, plane]
  derivative_p := fun t _ => (plane.physical_reference t).1
  derivative_v := by
    intro t _
    simpa only [physicalAcceleration, source_zero, PoweredCircle.thrust_bounds.2.1] using
      (plane.physical_reference t).2

theorem nominal_norm (t : ℝ) : ‖nominal.p t‖ = 7000000 := plane.reference_norm t

theorem nominal_position (t : ℝ) :
    nominal.p t = (7000000:ℝ) • mix ((omega:ℝ)*t) 1 0 0 := by
  simp [nominal, PoweredCircle.Plane.reference, PoweredCircle.Plane.radial,
    UniformCertificate.constants.1, plane, mix, pack]

/-- The supplied region is only a uniqueness domain, not an error allowance.
Zero differential defect and equal initial data imply zero trajectory error. -/
theorem nominal_unique_of_region (X : PhysicalOrbit .rtnReferenceOffset 0)
    {r M : ℝ} (hr : 0 < r) (hM : 0 < M)
    (hlip : 360000*(2*mu/r^3) ≤ 17/20) (hgap : r+M ≤ 7000000) :
    ∀ t ∈ Icc (0:ℝ) 1, X.p t = nominal.p t ∧ X.v t = nominal.v t := by
  have h := orbital_prediction mu 360000 (by norm_num [mu]) (by norm_num)
    X.p X.v nominal.p nominal.v
    (fun t => physicalAcceleration .rtnReferenceOffset 0 t (nominal.p t))
    (fun t => (Direct.thrust:ℝ) • SpatialBurn.source .rtnReferenceOffset 0 t)
    [] [] (by decide +kernel) (by simp [PolynomialOrder.nonnegative]) hr
    (by simpa [Planning.PolynomialKernel.evaluate] using hM) hlip
    (fun t _ => by simpa only [nominal_norm] using hgap)
    X.continuous_p X.continuous_v nominal.continuous_p nominal.continuous_v
    X.derivative_p X.derivative_v nominal.derivative_p nominal.derivative_v
    (X.initial_p.trans nominal.initial_p.symm) (X.initial_v.trans nominal.initial_v.symm)
    (by intro t _; simp [physicalAcceleration, PolynomialOrder.value,
      Planning.PolynomialKernel.evaluate])
  intro t ht
  have hp := (h t ht).1
  have hv := (h t ht).2
  simp [Planning.PolynomialKernel.evaluate, Planning.PolynomialKernel.differentiate,
    Planning.PolynomialKernel.weighted, sub_eq_zero] at hp hv
  exact ⟨hp, hv⟩

variable {C : Type} (A : SpatialSources.Algebra C) (S : TimeRepresentation A.base)

/-- An online deviation query subtracts the reference in rotating coordinates;
it does not need a second trajectory propagation. -/
theorem position_deviation (q : Fin 3 → C) (θ t : ℝ) :
    SpatialRotatingCertificate.position A q θ t - nominal.p t =
      (7000000:ℝ) • mix ((omega:ℝ)*t)
        (A.base.value (q 0) t θ - 1) (A.base.value (q 1) t θ)
        (A.base.value (q 2) t θ) := by
  rw [SpatialRotatingCertificate.position, nominal_position, ← smul_sub, ← mix_sub]
  simp only [sub_zero]

/-- Reuse the already checked candidate-derived radius instead of inventing
an additional tolerance to establish uniqueness of the nominal. -/
theorem nominal_unique (D : SpatialRotatingCertificate.Data (C := C))
    (hD : D.Valid A S) (X : PhysicalOrbit .rtnReferenceOffset 0) :
    ∀ t ∈ Icc (0:ℝ) 1, X.p t = nominal.p t ∧ X.v t = nominal.v t := by
  rcases hD with ⟨hb, hb', _, _, _, _, _, _, hlip, _⟩
  have hb0 : (0:ℝ) < D.radiusVariation := by exact_mod_cast hb
  have hb1 : (D.radiusVariation:ℝ) < ((1/2:ℚ):ℝ) := by exact_mod_cast hb'
  norm_num at hb1
  apply nominal_unique_of_region X
    (r := 7000000*(1-2*(D.radiusVariation:ℝ))) (M := 7000000*(D.radiusVariation:ℝ))
  · nlinarith
  · positivity
  · have hc : ((360000*(2*Direct.gravityParameter/(7000000*(1-2*D.radiusVariation))^3):ℚ):ℝ) ≤
        ((17/20:ℚ):ℝ) := by exact_mod_cast hlip
    simpa [mu, Direct.gravityParameter] using hc
  · nlinarith

/-- Deviation from the analytic nominal needs only the perturbed trajectory's
absolute prediction bound. This conclusion holds for every physical nominal
solution, and for either coefficient representation. -/
theorem relative_certifies (D : SpatialRotatingCertificate.Data (C := C))
    (hD : D.Valid A S) {θ : ℝ} (X : PhysicalOrbit .rtnReferenceOffset θ)
    (X₀ : PhysicalOrbit .rtnReferenceOffset 0) (hθ : |θ| ≤ (angle:ℝ)) :
    ∀ t ∈ Icc (0:ℝ) 1,
      ‖(X.p t-X₀.p t)-(SpatialRotatingCertificate.position A D.q θ t-nominal.p t)‖ ≤
        (D.positionLimit:ℝ) ∧
      ‖(X.v t-X₀.v t)-(SpatialRotatingCertificate.velocity A D.q θ t-nominal.v t)‖/600 ≤
        (D.velocityLimit:ℝ) := by
  intro t ht
  have hn := nominal_unique A S D hD X₀ t ht
  simpa only [hn.1, hn.2, sub_sub_sub_cancel_right] using D.certifies A S hD X hθ t ht

end GNC.OrbitalComparison.SpatialExactNominal
