import GNC.Applications.OrbitalComparison.TangentialResponseCertificate

/-! Three reusable responses retain every finite body-mounted direction.
The number of columns does not increase with the number of queries or the
angular Taylor order, because there is no angular Taylor truncation here.
This identity is equally implementable in Cartesian coordinates. -/
noncomputable section
namespace GNC.OrbitalComparison.TangentialResponseCertificate
open TangentialReferenceMotion TangentialMountingMotion
open ThrustSupport (euclideanEquiv)

def direction (φ : Vec3) : Vec3 :=
  rotate (rotationExp φ) PlanarReferenceMotion.tangent-PlanarReferenceMotion.tangent

def columnForce (r : Reference) (i : Fin 3) (t : ℝ) : E :=
  acceleration • rotationIsometry (r.frame t) (euclideanEquiv (Pi.single i 1))

theorem forcing_columns (r : Reference) (φ : Vec3) (t : ℝ) :
    forcing r φ t=∑ i : Fin 3, direction φ i • columnForce r i t := by
  have he : direction φ=∑ i : Fin 3, direction φ i • (Pi.single i 1 : Vec3) := by
    ext j
    simp [Pi.single_apply]
  change acceleration • rotationIsometry (r.frame t)
      (euclideanEquiv (rotate (rotationExp φ) PlanarReferenceMotion.tangent))-
    acceleration • rotationIsometry (r.frame t) (euclideanEquiv PlanarReferenceMotion.tangent)=_
  rw [←smul_sub,←map_sub,←map_sub]
  change acceleration • rotationIsometry (r.frame t) (euclideanEquiv (direction φ))=_
  calc
    _ = acceleration • rotationIsometry (r.frame t)
        (euclideanEquiv (∑ i : Fin 3, direction φ i • (Pi.single i 1 : Vec3))) :=
      congrArg (fun v => acceleration • rotationIsometry (r.frame t) (euclideanEquiv v)) he
    _ = _ := by simp only [map_sum,map_smul,Finset.smul_sum,columnForce,smul_comm acceleration]

abbrev Columns (r : Reference) :=
  ∀ i : Fin 3, GravityLinearResponse.Response mu 1 r.q (columnForce r i)

theorem exists_columns (r : Reference) : Nonempty (Columns r) := by
  have hi (i : Fin 3) : Nonempty (GravityLinearResponse.Response mu 1 r.q (columnForce r i)) := by
    apply GravityLinearResponse.Response.exists mu 1 (q_continuous r) _
      ((rotated_continuous r (Pi.single i 1)).const_smul acceleration)
    intro t
    apply norm_ne_zero_iff.mp
    change enorm (PolynomialOrbitTransition.position (r.w (horizon*t)))≠0
    rw [PolynomialOrbitTransition.position_norm]
    exact (r.positive _).ne'
  exact ⟨fun i => Classical.choice (hi i)⟩

def from_columns (r : Reference) (S : Columns r) (φ : Vec3) : Response r φ :=
  let C := GravityLinearResponse.Response.combine mu 1 r.q (columnForce r) S (direction φ)
  { p := C.p
    v := C.v
    continuous_p := C.continuous_p
    continuous_v := C.continuous_v
    initial_p := C.initial_p
    initial_v := C.initial_v
    derivative_p := C.derivative_p
    derivative_v := fun t ht => by
      simpa only [forcing_columns] using C.derivative_v t ht }

theorem from_columns_position (r : Reference) (S : Columns r) (φ : Vec3) (t : ℝ) :
    (from_columns r S φ).p t=∑ i : Fin 3, direction φ i • (S i).p t := rfl

/-- One reference and just three response histories serve the entire angle
ball. The conclusion bounds the actual nonlinear orbit, not a sampled cloud. -/
theorem common_columns_certificate (r : Reference) :
    ∃ S : Columns r, ∀ φ : Vec3, enorm φ≤angleRadius →
      ∃ X : Motion r φ, ∀ t ∈ Set.Icc (0:ℝ) 1,
        ‖X.p t-(r.q t+∑ i : Fin 3, direction φ i • (S i).p t)‖≤positionError t ∧
        ‖X.v t-(r.v t+∑ i : Fin 3, direction φ i • (S i).v t)‖≤velocityError t := by
  obtain ⟨S⟩ := exists_columns r
  refine ⟨S,fun φ hφ => ⟨trajectory r φ hφ,?_⟩⟩
  exact prediction r φ hφ _ (from_columns r S φ)

end GNC.OrbitalComparison.TangentialResponseCertificate
