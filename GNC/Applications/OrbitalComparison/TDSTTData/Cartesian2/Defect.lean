import GNC.Applications.OrbitalComparison.TDSTTData.Cartesian2.Ranges
import GNC.Applications.OrbitalComparison.TDSTTData.Cartesian2.Constraint
import GNC.Applications.OrbitalComparison.TDSTTData.Cartesian2.Residual
import GNC.Applications.OrbitalComparison.TDSTTReference
import GNC.Analysis.QuadraticTimeProfile

/-! The full-field Cartesian acceleration defect of the actual rank-two
polynomial query. Retained coefficient products are checked exactly;
higher products have explicit, proved time-dependent bounds. Physical trajectory existence and integration of this profile
are separate obligations. -/
namespace GNC.OrbitalComparison.TDSTTData.Cartesian2
open ParameterPolynomial LieSTTOutput Planning.PolynomialKernel Set

def sigma : ℚ := 1/10
def displacementMaximum : ℚ := evaluate (positionRange.bound 1) 1
def offsetMaximum : ℚ := evaluate (inverseOffsetRange.bound 1) 1

set_option maxHeartbeats 0 in
theorem uniform_ranges_checked :
    PolynomialOrder.nonnegative (positionRange.bound 1) ∧
    PolynomialOrder.nonnegative (inverseOffsetRange.bound 1) ∧
    0<displacementMaximum ∧ 2*displacementMaximum<1 ∧ 0≤offsetMaximum ∧ offsetMaximum<1 := by
  decide +kernel

def jacobianTail : ℚ := sigma^9/3628800+sigma^10/39916800
def radiusUpper : ℚ := (1+displacementMaximum)*(1+offsetMaximum)
def gravityFactor : ℚ := physicalInput.K/(1-displacementMaximum)^2*
  (radiusUpper^2+radiusUpper+1)/(radiusUpper+1)
def forceError : ℚ := sigma*TDSTTReference.forceBound*TDSTTReference.phaseBound+
  jacobianTail*sigma*TDSTTReference.forceBound*(1+TDSTTReference.phaseBound)
def constantTail : ℚ := forceError+
  physicalInput.K*(3*offsetMaximum+3*offsetMaximum^2+offsetMaximum^3)*TDSTTReference.phaseBound+
  gravityFactor*(2*TDSTTReference.phaseBound*displacementMaximum)*(1+offsetMaximum)^2
def qhatMaximum : ℚ := 1+TDSTTReference.phaseBound
def residualRemainder : List ℚ := [0,0,0,0,
  3*physicalInput.K*offsetMaximum*displacementMaximum+
    3*physicalInput.K*offsetMaximum^2*qhatMaximum,0,
  physicalInput.K*offsetMaximum^3*qhatMaximum+
    3*physicalInput.K*offsetMaximum^2*displacementMaximum,0,
  physicalInput.K*offsetMaximum^3*displacementMaximum]
def constraintRemainder : List ℚ := [0,0,0,0,
  4*qhatMaximum*displacementMaximum*offsetMaximum+offsetMaximum^2,0,
  2*displacementMaximum^2*offsetMaximum+2*qhatMaximum*displacementMaximum*offsetMaximum^2,0,
  displacementMaximum^2*offsetMaximum^2]
def rawForcing : List ℚ := PolynomialBounds.add residualBound
  (PolynomialBounds.add residualRemainder
    (PolynomialBounds.add (PolynomialBounds.scale gravityFactor
      (PolynomialBounds.add constraintBound constraintRemainder)) [constantTail]))

set_option maxHeartbeats 0 in
theorem quadratic_profiles_checked :
    positionRange.bound 1=0::0::(positionRange.bound 1).drop 2 ∧
    PolynomialOrder.nonnegative ((positionRange.bound 1).drop 2) ∧
    inverseOffsetRange.bound 1=0::0::(inverseOffsetRange.bound 1).drop 2 ∧
    PolynomialOrder.nonnegative ((inverseOffsetRange.bound 1).drop 2) := by
  decide +kernel

noncomputable section

theorem displacement_uniform {x : Vec3} {t : ℝ}
    (hx : x 0^2+x 1^2+x 2^2≤(sigma:ℝ)^2) (ht : t ∈ Icc (0:ℝ) 1) :
    enorm (value3 physicalInput.rho x t)≤(displacementMaximum:ℝ) := by
  have h := position_range_bound hx ht.1
  have h1 := h.trans (PolynomialOrder.value_le_endpoint _ uniform_ranges_checked.1 ht)
  have he := PolynomialOrder.value_at_rational (positionRange.bound 1) 1
  norm_num only [Rat.cast_one] at he
  rw [he] at h1
  exact h1

theorem offset_uniform {x : Vec3} {t : ℝ}
    (hx : x 0^2+x 1^2+x 2^2≤(sigma:ℝ)^2) (ht : t ∈ Icc (0:ℝ) 1) :
    |value physicalInput.h x t|≤(offsetMaximum:ℝ) := by
  have hc : |value inverseOffset x t|≤‖DiskPolynomial.vectorValue ![inverseOffset] x t‖ := by
    simpa [DiskPolynomial.vectorValue,Real.norm_eq_abs] using
      PiLp.norm_apply_le (DiskPolynomial.vectorValue ![inverseOffset] x t) (0 : Fin 1)
  have h := hc.trans (inverseOffset_range_bound hx ht.1)
  have h1 := h.trans (PolynomialOrder.value_le_endpoint _ uniform_ranges_checked.2.1 ht)
  have he := PolynomialOrder.value_at_rational (inverseOffsetRange.bound 1) 1
  norm_num only [Rat.cast_one] at he
  rw [he] at h1
  exact h1

theorem attitude_bound {x : Vec3} (hx : x 0^2+x 1^2+x 2^2≤(sigma:ℝ)^2) :
    enorm x≤(sigma:ℝ) ∧ enorm x<2*Real.pi := by
  have hn := enorm_sq x
  change enorm x^2=x 0^2+x 1^2+x 2^2 at hn
  have hb : enorm x≤(sigma:ℝ) := by
    have hs : (0:ℝ)≤sigma := by norm_num [sigma]
    nlinarith [enorm_nonneg x]
  refine ⟨hb,hb.trans_lt ?_⟩
  norm_num only [sigma,Rat.cast_div,Rat.cast_ofNat]
  linarith [Real.two_le_pi]

theorem position_growth {x : Vec3} {t : ℝ}
    (hx : x 0^2+x 1^2+x 2^2≤(sigma:ℝ)^2) (ht : t ∈ Icc (0:ℝ) 1) :
    enorm (value3 physicalInput.rho x t)≤(displacementMaximum:ℝ)*t^2 := by
  have h := QuadraticTimeProfile.bound _ quadratic_profiles_checked.2.1 ht
  rw [←quadratic_profiles_checked.1] at h
  have he := PolynomialOrder.value_at_rational (positionRange.bound 1) 1
  norm_num only [Rat.cast_one] at he
  rw [he] at h
  exact (position_range_bound hx ht.1).trans h

theorem offset_growth {x : Vec3} {t : ℝ}
    (hx : x 0^2+x 1^2+x 2^2≤(sigma:ℝ)^2) (ht : t ∈ Icc (0:ℝ) 1) :
    |value physicalInput.h x t|≤(offsetMaximum:ℝ)*t^2 := by
  have hc : |value inverseOffset x t|≤‖DiskPolynomial.vectorValue ![inverseOffset] x t‖ := by
    simpa [DiskPolynomial.vectorValue,Real.norm_eq_abs] using
      PiLp.norm_apply_le (DiskPolynomial.vectorValue ![inverseOffset] x t) (0 : Fin 1)
  have h := QuadraticTimeProfile.bound _ quadratic_profiles_checked.2.2.2 ht
  rw [←quadratic_profiles_checked.2.2.1] at h
  have he := PolynomialOrder.value_at_rational (inverseOffsetRange.bound 1) 1
  norm_num only [Rat.cast_one] at he
  rw [he] at h
  exact (hc.trans (inverseOffset_range_bound hx ht.1)).trans h

theorem polynomial_reference_bound (x : Vec3) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    enorm (value3 physicalInput.reference x t)≤(qhatMaximum:ℝ) := by
  have h := LieRadiusApproximation.approximate_axis_norm (JointErrorData.exactReference t)
    (value3 physicalInput.reference x t)
    (le_of_eq (JointErrorData.exactReference_norm t)) (TDSTTReference.reference_error x ht)
  simpa only [qhatMaximum,Rat.cast_add,Rat.cast_one] using h

theorem retained_constraint_bound {x : Vec3} {t : ℝ}
    (hx : x 0^2+x 1^2+x 2^2≤(sigma:ℝ)^2) (ht : 0≤t) :
    |value (CartesianReducedPolynomial.constraint physicalInput) x t|≤
      PolynomialOrder.value constraintBound t := by
  rw [←scalarConstraint_value]
  have hc : |value scalarConstraint x t|≤‖DiskPolynomial.vectorValue ![scalarConstraint] x t‖ := by
    simpa [DiskPolynomial.vectorValue,Real.norm_eq_abs] using
      PiLp.norm_apply_le (DiskPolynomial.vectorValue ![scalarConstraint] x t) (0 : Fin 1)
  exact hc.trans (constraint_range_bound hx ht)

theorem retained_residual_bound {x : Vec3} {t : ℝ}
    (hx : x 0^2+x 1^2+x 2^2≤(sigma:ℝ)^2) (ht : 0≤t) :
    enorm (value3 (CartesianReducedPolynomial.residual physicalInput) x t)≤
      PolynomialOrder.value residualBound t := by
  rw [←residual_value]
  exact residual_range_bound hx ht

theorem residualRemainder_value (t : ℝ) : PolynomialOrder.value residualRemainder t=
    (3*(physicalInput.K:ℝ)*offsetMaximum*displacementMaximum+
      3*(physicalInput.K:ℝ)*(offsetMaximum:ℝ)^2*qhatMaximum)*t^4+
    ((physicalInput.K:ℝ)*(offsetMaximum:ℝ)^3*qhatMaximum+
      3*(physicalInput.K:ℝ)*(offsetMaximum:ℝ)^2*displacementMaximum)*t^6+
    ((physicalInput.K:ℝ)*(offsetMaximum:ℝ)^3*displacementMaximum)*t^8 := by
  simp only [residualRemainder,PolynomialOrder.value,List.map_cons,List.map_nil,evaluate,
    Rat.coe_castHom,Rat.cast_add,Rat.cast_mul,Rat.cast_pow,Rat.cast_zero,Rat.cast_ofNat]
  ring

theorem constraintRemainder_value (t : ℝ) : PolynomialOrder.value constraintRemainder t=
    (4*(qhatMaximum:ℝ)*displacementMaximum*offsetMaximum+(offsetMaximum:ℝ)^2)*t^4+
    (2*(displacementMaximum:ℝ)^2*offsetMaximum+
      2*(qhatMaximum:ℝ)*displacementMaximum*(offsetMaximum:ℝ)^2)*t^6+
    ((displacementMaximum:ℝ)^2*(offsetMaximum:ℝ)^2)*t^8 := by
  simp only [constraintRemainder,PolynomialOrder.value,List.map_cons,List.map_nil,evaluate,
    Rat.coe_castHom,Rat.cast_add,Rat.cast_mul,Rat.cast_pow,Rat.cast_zero,Rat.cast_ofNat]
  ring

theorem constraint_bound {x : Vec3} {t : ℝ}
    (hx : x 0^2+x 1^2+x 2^2≤(sigma:ℝ)^2) (ht : t ∈ Icc (0:ℝ) 1) :
    |value (CartesianErrorPolynomial.constraint physicalInput) x t|≤
      PolynomialOrder.value constraintBound t+PolynomialOrder.value constraintRemainder t := by
  have hr := SmallOffsetDefect.radius_difference_growth
    (value3 physicalInput.reference x t) (value3 physicalInput.rho x t) t
    (polynomial_reference_bound x ht) (position_growth hx ht)
  rw [←CartesianErrorPolynomial.radius_value] at hr
  have hc := retained_constraint_bound hx ht.1
  rw [CartesianReducedPolynomial.constraint_value] at hc
  have h := SmallOffsetDefect.constraint_growth t hr (offset_growth hx ht) hc
  rw [CartesianErrorPolynomial.constraint_value,constraintRemainder_value]
  simpa only [add_assoc] using h

theorem residual_bound {x : Vec3} {t : ℝ}
    (hx : x 0^2+x 1^2+x 2^2≤(sigma:ℝ)^2) (ht : t ∈ Icc (0:ℝ) 1) :
    enorm (value3 (CartesianErrorPolynomial.residualWith physicalInput offsetCube) x t)≤
      PolynomialOrder.value residualBound t+PolynomialOrder.value residualRemainder t := by
  have hK : 0≤(physicalInput.K:ℝ) := by exact_mod_cast JointErrorData.model_K_nonnegative
  have hc := retained_residual_bound hx ht.1
  rw [CartesianReducedPolynomial.residual_value] at hc
  have h := SmallOffsetDefect.residual_growth
    (value3 (PointingCapPolynomial.derivative (PointingCapPolynomial.derivative physicalInput.rho)) x t)
    (value3 physicalInput.rho x t) (value3 physicalInput.reference x t)
    (JacobianPolynomial.apply x (crossProduct x (value3 physicalInput.force x t))) t
    hK (position_growth hx ht) (offset_growth hx ht) (polynomial_reference_bound x ht) hc
  rw [CartesianErrorPolynomial.residualWith_value,offsetCube_value,residualRemainder_value]
  simpa only [SmallOffsetDefect.full,add_assoc] using h

theorem rawForcing_value (t : ℝ) : PolynomialOrder.value rawForcing t=
    CartesianRadiusDefect.budget (physicalInput.K:ℝ) 1
      (displacementMaximum:ℝ) (offsetMaximum:ℝ) (TDSTTReference.phaseBound:ℝ)
      ((sigma:ℝ)*(TDSTTReference.forceBound:ℝ)*(TDSTTReference.phaseBound:ℝ)+
        JacobianPolynomial.tail (sigma:ℝ)*(sigma:ℝ)*
          ((TDSTTReference.forceBound:ℝ)*(1+(TDSTTReference.phaseBound:ℝ))))
      (2*(TDSTTReference.phaseBound:ℝ)*(displacementMaximum:ℝ))
      (PolynomialOrder.value constraintBound t+PolynomialOrder.value constraintRemainder t)
      (PolynomialOrder.value residualBound t+PolynomialOrder.value residualRemainder t) := by
  simp only [rawForcing,PolynomialOrder.value_add,PolynomialOrder.value_scale]
  simp only [PolynomialOrder.value,List.map_cons,List.map_nil,evaluate,Rat.coe_castHom]
  simp only [CartesianRadiusDefect.budget,constantTail,forceError,gravityFactor,radiusUpper,
    jacobianTail,JacobianPolynomial.tail,Gravity.inverseRadiusFactor,
    Rat.cast_add,Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat]
  ring

/-- All polynomial and geometric inputs to this full inverse-square defect
have been checked for every attitude in the ball and every burn time. -/
theorem physical_defect_profile {x : Vec3} {t : ℝ}
    (hx : x 0^2+x 1^2+x 2^2≤(sigma:ℝ)^2) (ht : t ∈ Icc (0:ℝ) 1) :
    enorm (Gravity.field3 (physicalInput.K:ℝ) (JointErrorData.exactReference t)+
      JointErrorData.exactForce t+
      value3 (PointingCapPolynomial.derivative (PointingCapPolynomial.derivative physicalInput.rho)) x t-
      (Gravity.field3 (physicalInput.K:ℝ) (JointErrorData.exactReference t+value3 physicalInput.rho x t)+
        rotate (rotationExp x) (JointErrorData.exactForce t)))≤PolynomialOrder.value rawForcing t := by
  have hK : 0≤(physicalInput.K:ℝ) := by exact_mod_cast JointErrorData.model_K_nonnegative
  have hP : (displacementMaximum:ℝ)<1 := by
    have h0 : (0:ℝ)<displacementMaximum := by exact_mod_cast uniform_ranges_checked.2.2.1
    have h2 : 2*(displacementMaximum:ℝ)<1 := by exact_mod_cast uniform_ranges_checked.2.2.2.1
    linarith
  have hH : (offsetMaximum:ℝ)<1 := by exact_mod_cast uniform_ranges_checked.2.2.2.2.2
  have h := CartesianErrorPolynomial.physical_defect physicalInput x t
    (JointErrorData.exactReference t) (JointErrorData.exactForce t) offsetCube
    hK (JointErrorData.exactReference_norm t) (attitude_bound hx).2
    (attitude_bound hx).1 (displacement_uniform hx ht) hP (offset_uniform hx ht) hH
    (TDSTTReference.reference_error x ht) (TDSTTReference.force_error x ht)
    (TDSTTReference.polynomial_force_bound x ht) (constraint_bound hx ht)
    (offsetCube_value x t) (residual_bound hx ht)
  rw [rawForcing_value]
  simpa only [mul_assoc] using h

end
end GNC.OrbitalComparison.TDSTTData.Cartesian2
