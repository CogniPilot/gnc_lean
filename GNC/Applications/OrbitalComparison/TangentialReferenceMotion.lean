import GNC.Applications.OrbitalComparison.TangentialReferenceObservables
import GNC.Dynamics.PlanarReferenceMotion
import GNC.Control.ThrustIntegral

/-! A normalized three-dimensional physical reference, constructed from the
validated planar orbit. The lower radius is computed from the full polynomial
inverse-radius enclosure, rather than chosen as a guessed gravity allowance.
-/
noncomputable section
namespace GNC.OrbitalComparison.TangentialReferenceMotion
open PolynomialODE PolynomialOrbit PolynomialOrbitTransition TangentialReferenceData Set
open ThrustSupport (euclideanEquiv)
abbrev E := Jacobian.E3

def horizon : ℝ := 13/20
def mu : ℝ := horizon^2
def acceleration : ℝ := horizon^2*(alpha:ℝ)
def lowerRadius : ℚ := 1/inverseBound

structure Reference where
  w : ℝ → Fin 4 → ℝ
  continuous : Continuous w
  positive : ∀ t, 0<radius (w t)
  initial : w 0=![1,0,0,1]
  derivative : ∀ t ∈ Icc (0:ℝ) (13/20),
    HasDerivAt w (physicalRate (alpha:ℝ) (w t)) t

theorem exists_reference : Nonempty Reference := by
  obtain ⟨w,hw,hr,hi,hd⟩ := TangentialReference.exists_physical
  exact ⟨⟨w,hw,hr,hi,hd⟩⟩

theorem radius_lower (r : Reference) {t : ℝ} (ht : t ∈ Icc (0:ℝ) (13/20)) :
    (lowerRadius:ℝ)≤radius (r.w t) := by
  obtain ⟨j,hj,u,hu,htj,he⟩ := TangentialReference.physical_enclosure
    r.w r.continuous r.positive r.derivative r.initial t ht
  have hp := PolynomialBounds.bound_sound ((TangentialReference.sequence j).coefficients 4)
    (show |u|≤(stepLength:ℝ) by rw [abs_of_nonneg hu.1]; norm_num [stepLength] at hu ⊢; exact hu.2)
  have hb : (PolynomialBounds.bound ((TangentialReference.sequence j).coefficients 4)
      stepLength:ℝ)+(errorBound:ℝ)≤(inverseBound:ℝ) := by
    have h := inverse_bounds ⟨j,hj⟩
    simp only [TangentialReference.sequence,dif_pos hj] at ⊢
    exact_mod_cast h
  have hdiff := (norm_le_pi_norm
    (lift (r.w t)-curve (TangentialReference.sequence j).coefficients u) 4).trans he.le
  change |(radius (r.w t))⁻¹-curve (TangentialReference.sequence j).coefficients u 4|≤_ at hdiff
  change |curve (TangentialReference.sequence j).coefficients u 4|≤_ at hp
  have hab := abs_le.mp hdiff
  have hval := (le_abs_self _).trans hp
  have hinv : 1/radius (r.w t)≤(inverseBound:ℝ) := by
    rw [one_div]; linarith
  have hprod := (div_le_iff₀ (r.positive t)).mp hinv
  have hB : (0:ℝ)<(inverseBound:ℝ) := by norm_num [inverseBound]
  simp only [lowerRadius,Rat.cast_div,Rat.cast_one]
  exact (div_le_iff₀ hB).mpr (by nlinarith)

def Reference.q (r : Reference) (t : ℝ) : E :=
  euclideanEquiv (position (r.w (horizon*t)))
def Reference.v (r : Reference) (t : ℝ) : E :=
  horizon • euclideanEquiv (velocity (r.w (horizon*t)))
def Reference.frame (r : Reference) (t : ℝ) : SO3 :=
  PlanarAttitudeFrame.rotation (r.w (horizon*t)) (r.positive _)
def Reference.thrust (r : Reference) (t : ℝ) : E :=
  acceleration • rotationIsometry (r.frame t) (euclideanEquiv PlanarReferenceMotion.tangent)

theorem time_mem {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    horizon*t ∈ Icc (0:ℝ) (13/20) := by dsimp [horizon]; constructor <;> linarith [ht.1,ht.2]

theorem q_continuous (r : Reference) : Continuous r.q :=
  euclideanEquiv.continuous.comp
    ((PlanarReferenceMotion.position_continuous r.continuous).comp (continuous_const.mul continuous_id))
theorem v_continuous (r : Reference) : Continuous r.v :=
  (euclideanEquiv.continuous.comp
    ((PlanarReferenceMotion.velocity_continuous r.continuous).comp
      (continuous_const.mul continuous_id))).const_smul _

theorem q_radius (r : Reference) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    (lowerRadius:ℝ)≤‖r.q t‖ := by
  change (lowerRadius:ℝ)≤enorm (position (r.w (horizon*t)))
  rw [position_norm]
  exact radius_lower r (time_mem ht)

theorem q_derivative (r : Reference) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    HasDerivAt r.q (r.v t) t := by
  have h := euclideanEquiv.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt (horizon*t)
    (PlanarReferenceMotion.position_derivative (r.derivative _ (time_mem ht)))
  simpa only [Reference.q,Reference.v,mul_one] using
    h.scomp t ((hasDerivAt_id t).const_mul horizon)

theorem v_derivative (r : Reference) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    HasDerivAt r.v (Gravity.field mu (r.q t)+r.thrust t) t := by
  have h := euclideanEquiv.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt (horizon*t)
    (PlanarReferenceMotion.velocity_derivative (r.derivative _ (time_mem ht)))
  have hh := (h.scomp t ((hasDerivAt_id t).const_mul horizon)).const_smul horizon
  convert hh using 1
  simp only [mul_one,map_add,map_smul,smul_add,smul_smul]
  rw [PlanarReferenceMotion.thrust_rotation _ _ (r.positive _)]
  simp only [map_smul]
  change Gravity.field mu (r.q t)+r.thrust t = _
  congr 1
  · simp [Gravity.field,Gravity.field3,Reference.q,mu,pow_two,ThrustSupport.euclideanEquiv,
      smul_smul,mul_div_assoc]
    congr 1 <;> ring
  · simp [Reference.thrust,Reference.frame,acceleration,rotationIsometry,pow_two,
      smul_smul,ThrustSupport.euclideanEquiv,mul_assoc]

theorem rotated_continuous (r : Reference) (v : Vec3) :
    Continuous (fun t => rotationIsometry (r.frame t) (euclideanEquiv v)) := by
  exact euclideanEquiv.continuous.comp
    ((PlanarReferenceMotion.rotated_continuous r.continuous r.positive v).comp
      (continuous_const.mul continuous_id))

theorem thrust_continuous (r : Reference) : Continuous r.thrust :=
  (rotated_continuous r PlanarReferenceMotion.tangent).const_smul _

theorem thrust_norm (r : Reference) (t : ℝ) : ‖r.thrust t‖=acceleration := by
  rw [Reference.thrust,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (by norm_num [acceleration,horizon,alpha]),LinearIsometryEquiv.norm_map]
  change acceleration*enorm PlanarReferenceMotion.tangent=acceleration
  rw [PlanarReferenceMotion.tangent_norm,mul_one]

end GNC.OrbitalComparison.TangentialReferenceMotion
