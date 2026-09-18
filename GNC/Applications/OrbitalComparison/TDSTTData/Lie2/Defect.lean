import GNC.Applications.OrbitalComparison.TDSTTData.Lie2.Ranges
import GNC.Applications.OrbitalComparison.TDSTTData.Lie2.Constraint
import GNC.Applications.OrbitalComparison.TDSTTData.Lie2.Residual
import GNC.Applications.OrbitalComparison.TDSTTReference
import GNC.Analysis.QuadraticTimeProfile

/-! The full-field Lie-coordinate acceleration defect of the actual rank-two
polynomial query. Retained coefficient products are checked exactly;
higher products have explicit, proved time-dependent bounds. Physical trajectory existence and integration of this profile
are separate obligations. -/
namespace GNC.OrbitalComparison.TDSTTData.Lie2
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

def jacobianTail : ℚ := sigma^3/24+sigma^4/120
def inverseTail : ℚ := sigma^4/720+sigma^5/1440+sigma^6/5040+
  sigma^7/24192+sigma^8/241920+sigma^9/483840+
  (sigma^8/362880+sigma^9/3628800)*(1+sigma/2+sigma^2/12)
def radiusUpper : ℚ := (1+displacementMaximum)*(1+offsetMaximum)
def gravityFactor : ℚ := physicalInput.K/(1-displacementMaximum)^2*
  (radiusUpper^2+radiusUpper+1)/(radiusUpper+1)
def constantTail : ℚ := sigma*TDSTTReference.forceBound*TDSTTReference.phaseBound+
  physicalInput.K*(3*offsetMaximum+3*offsetMaximum^2+offsetMaximum^3)*
    (inverseTail+(1+sigma/2+sigma^2/12)*TDSTTReference.phaseBound)
def radiusError : List ℚ := [0,0,
  2*TDSTTReference.phaseBound*(1+jacobianTail)*displacementMaximum+
    2*jacobianTail*displacementMaximum,0,sigma^2/12*displacementMaximum^2]
def qhatMaximum : ℚ := 1+TDSTTReference.phaseBound
def inverseMaximum : ℚ := (1+sigma/2+sigma^2/12)*qhatMaximum
def quadraticFactor : ℚ := 1+sigma/2+sigma^2/6
def radiusReferenceMaximum : ℚ := qhatMaximum*quadraticFactor
def residualRemainder : List ℚ := [0,0,0,0,
  3*physicalInput.K*offsetMaximum*displacementMaximum+
    3*physicalInput.K*offsetMaximum^2*inverseMaximum,0,
  physicalInput.K*offsetMaximum^3*inverseMaximum+
    3*physicalInput.K*offsetMaximum^2*displacementMaximum,0,
  physicalInput.K*offsetMaximum^3*displacementMaximum]
def constraintRemainder : List ℚ := [0,0,0,0,
  4*radiusReferenceMaximum*displacementMaximum*offsetMaximum+offsetMaximum^2,0,
  2*displacementMaximum^2*offsetMaximum+2*radiusReferenceMaximum*displacementMaximum*offsetMaximum^2,0,
  displacementMaximum^2*offsetMaximum^2]
def rawForcing : List ℚ := PolynomialBounds.add residualBound
  (PolynomialBounds.add residualRemainder
    (PolynomialBounds.add (PolynomialBounds.scale gravityFactor
      (PolynomialBounds.add constraintBound (PolynomialBounds.add constraintRemainder
        (PolynomialBounds.scale ((1+offsetMaximum)^2) radiusError)))) [constantTail]))

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
    |value (LieReducedPolynomial.constraint physicalInput) x t|≤
      PolynomialOrder.value constraintBound t := by
  rw [←scalarConstraint_value]
  have hc : |value scalarConstraint x t|≤‖DiskPolynomial.vectorValue ![scalarConstraint] x t‖ := by
    simpa [DiskPolynomial.vectorValue,Real.norm_eq_abs] using
      PiLp.norm_apply_le (DiskPolynomial.vectorValue ![scalarConstraint] x t) (0 : Fin 1)
  exact hc.trans (constraint_range_bound hx ht)

theorem retained_residual_bound {x : Vec3} {t : ℝ}
    (hx : x 0^2+x 1^2+x 2^2≤(sigma:ℝ)^2) (ht : 0≤t) :
    enorm (value3 (LieReducedPolynomial.residual physicalInput) x t)≤
      PolynomialOrder.value residualBound t := by
  rw [←residual_value]
  exact residual_range_bound hx ht

theorem residualRemainder_value (t : ℝ) : PolynomialOrder.value residualRemainder t=
    (3*(physicalInput.K:ℝ)*offsetMaximum*displacementMaximum+
      3*(physicalInput.K:ℝ)*(offsetMaximum:ℝ)^2*inverseMaximum)*t^4+
    ((physicalInput.K:ℝ)*(offsetMaximum:ℝ)^3*inverseMaximum+
      3*(physicalInput.K:ℝ)*(offsetMaximum:ℝ)^2*displacementMaximum)*t^6+
    ((physicalInput.K:ℝ)*(offsetMaximum:ℝ)^3*displacementMaximum)*t^8 := by
  simp only [residualRemainder,PolynomialOrder.value,List.map_cons,List.map_nil,evaluate,
    Rat.coe_castHom,Rat.cast_add,Rat.cast_mul,Rat.cast_pow,Rat.cast_zero,Rat.cast_ofNat]
  ring

theorem constraintRemainder_value (t : ℝ) : PolynomialOrder.value constraintRemainder t=
    (4*(radiusReferenceMaximum:ℝ)*displacementMaximum*offsetMaximum+(offsetMaximum:ℝ)^2)*t^4+
    (2*(displacementMaximum:ℝ)^2*offsetMaximum+
      2*(radiusReferenceMaximum:ℝ)*displacementMaximum*(offsetMaximum:ℝ)^2)*t^6+
    ((displacementMaximum:ℝ)^2*(offsetMaximum:ℝ)^2)*t^8 := by
  simp only [constraintRemainder,PolynomialOrder.value,List.map_cons,List.map_nil,evaluate,
    Rat.coe_castHom,Rat.cast_add,Rat.cast_mul,Rat.cast_pow,Rat.cast_zero,Rat.cast_ofNat]
  ring

theorem inverse_reference_norm {x : Vec3} {t : ℝ}
    (hx : x 0^2+x 1^2+x 2^2≤(sigma:ℝ)^2) (ht : t ∈ Icc (0:ℝ) 1) :
    enorm (jacobianInverseQuadratic x (value3 physicalInput.reference x t))≤(inverseMaximum:ℝ) := by
  apply (jacobianInverseQuadratic_bound _ _).trans
  simp only [inverseMaximum,Rat.cast_mul,Rat.cast_add,Rat.cast_one,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat]
  have hb := (attitude_bound hx).1
  have hs := pow_le_pow_left₀ (enorm_nonneg x) hb 2
  have hσ : (0:ℝ)≤sigma := by norm_num [sigma]
  apply mul_le_mul _ (polynomial_reference_bound x ht) (enorm_nonneg _) (by positivity)
  linarith

theorem quadratic_displacement_growth {x : Vec3} {t : ℝ}
    (hx : x 0^2+x 1^2+x 2^2≤(sigma:ℝ)^2) (ht : t ∈ Icc (0:ℝ) 1) :
    enorm (LieRadiusQuadratic.apply x (value3 physicalInput.rho x t))≤
      (quadraticFactor:ℝ)*((displacementMaximum:ℝ)*t^2) := by
  apply (LieReducedPolynomial.quadratic_norm _ _).trans
  simp only [quadraticFactor,Rat.cast_add,Rat.cast_one,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat]
  have hb := (attitude_bound hx).1
  have hs := pow_le_pow_left₀ (enorm_nonneg x) hb 2
  have hσ : (0:ℝ)≤sigma := by norm_num [sigma]
  apply mul_le_mul _ (position_growth hx ht) (enorm_nonneg _) (by positivity)
  linarith

theorem constraint_bound {x : Vec3} {t : ℝ}
    (hx : x 0^2+x 1^2+x 2^2≤(sigma:ℝ)^2) (ht : t ∈ Icc (0:ℝ) 1) :
    |value (LieRadiusQuadraticPolynomial.constraint physicalInput) x t|≤
      PolynomialOrder.value constraintBound t+PolynomialOrder.value constraintRemainder t := by
  have hr := LieReducedPolynomial.radius_difference_growth
    (value3 physicalInput.reference x t) x (value3 physicalInput.rho x t) t
    (polynomial_reference_bound x ht) (position_growth hx ht) (quadratic_displacement_growth hx ht)
  rw [←LieRadiusQuadraticPolynomial.radius_value] at hr
  have hc := retained_constraint_bound hx ht.1
  rw [LieReducedPolynomial.constraint_value] at hc
  have h := SmallOffsetDefect.constraint_growth t hr (offset_growth hx ht) hc
  rw [LieRadiusQuadraticPolynomial.constraint_value,constraintRemainder_value]
  simpa only [radiusReferenceMaximum,Rat.cast_mul,add_assoc] using h

theorem residual_bound {x : Vec3} {t : ℝ}
    (hx : x 0^2+x 1^2+x 2^2≤(sigma:ℝ)^2) (ht : t ∈ Icc (0:ℝ) 1) :
    enorm (SmallOffsetDefect.full
      (value3 (PointingCapPolynomial.derivative (PointingCapPolynomial.derivative physicalInput.rho)) x t)
      (value3 physicalInput.rho x t) (jacobianInverseQuadratic x (value3 physicalInput.reference x t))
      (crossProduct x (value3 physicalInput.force x t)) (physicalInput.K:ℝ) (value physicalInput.h x t))≤
      PolynomialOrder.value residualBound t+PolynomialOrder.value residualRemainder t := by
  have hK : 0≤(physicalInput.K:ℝ) := by exact_mod_cast JointErrorData.model_K_nonnegative
  have hc := retained_residual_bound hx ht.1
  rw [LieReducedPolynomial.residual_value] at hc
  have h := SmallOffsetDefect.residual_growth
    (value3 (PointingCapPolynomial.derivative (PointingCapPolynomial.derivative physicalInput.rho)) x t)
    (value3 physicalInput.rho x t) (jacobianInverseQuadratic x (value3 physicalInput.reference x t))
    (crossProduct x (value3 physicalInput.force x t)) t
    hK (position_growth hx ht) (offset_growth hx ht) (inverse_reference_norm hx ht) hc
  rw [residualRemainder_value]
  simpa only [add_assoc] using h

theorem radiusError_value (t : ℝ) : PolynomialOrder.value radiusError t=
    (2*(TDSTTReference.phaseBound:ℝ)*(1+LieRadiusQuadratic.tail (sigma:ℝ))*(displacementMaximum:ℝ)+
      2*LieRadiusQuadratic.tail (sigma:ℝ)*(displacementMaximum:ℝ))*t^2+
      ((sigma:ℝ)^2/12*(displacementMaximum:ℝ)^2)*t^4 := by
  simp only [radiusError,PolynomialOrder.value,List.map_cons,List.map_nil,evaluate,
    Rat.coe_castHom,Rat.cast_add,Rat.cast_mul,Rat.cast_pow,Rat.cast_div,Rat.cast_zero,Rat.cast_ofNat,
    jacobianTail,LieRadiusQuadratic.tail]
  push_cast
  ring

theorem radius_error_growth {x : Vec3} {t : ℝ}
    (hx : x 0^2+x 1^2+x 2^2≤(sigma:ℝ)^2) (ht : t ∈ Icc (0:ℝ) 1) :
    |enorm (JointErrorData.exactReference t+Jacobian.leftAt x (value3 physicalInput.rho x t))^2-
      value (LieRadiusQuadraticPolynomial.radius physicalInput) x t|≤PolynomialOrder.value radiusError t := by
  have h := LieRadiusQuadratic.radius_error_growth (JointErrorData.exactReference t)
    (value3 physicalInput.reference x t) x (value3 physicalInput.rho x t) t
    (attitude_bound hx).2 (attitude_bound hx).1 (position_growth hx ht) (TDSTTReference.reference_error x ht)
  rw [LieRadiusQuadraticPolynomial.radius_value,radiusError_value]
  simpa only [LieRadiusQuadratic.radiusApprox,JointErrorData.exactReference_norm,one_pow,mul_one] using h

theorem rawForcing_value (t : ℝ) : PolynomialOrder.value rawForcing t=
    LieRadiusFullDefect.budget (physicalInput.K:ℝ) 1 (sigma:ℝ)
      (displacementMaximum:ℝ) (offsetMaximum:ℝ) (TDSTTReference.phaseBound:ℝ)
      ((TDSTTReference.forceBound:ℝ)*(TDSTTReference.phaseBound:ℝ))
      (PolynomialOrder.value radiusError t)
      (PolynomialOrder.value constraintBound t+PolynomialOrder.value constraintRemainder t)
      (PolynomialOrder.value residualBound t+PolynomialOrder.value residualRemainder t) := by
  simp only [rawForcing,PolynomialOrder.value_add,PolynomialOrder.value_scale]
  simp only [PolynomialOrder.value,List.map_cons,List.map_nil,evaluate,Rat.coe_castHom]
  simp only [LieRadiusFullDefect.budget,constantTail,gravityFactor,radiusUpper,
    inverseTail,inverseQuadraticBudget,Gravity.inverseRadiusFactor,
    Rat.cast_add,Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat]
  ring

/-- Full inverse-square acceleration defect for every attitude and burn time. -/
theorem physical_defect_profile {x : Vec3} {t : ℝ}
    (hx : x 0^2+x 1^2+x 2^2≤(sigma:ℝ)^2) (ht : t ∈ Icc (0:ℝ) 1) :
    enorm (Gravity.field3 (physicalInput.K:ℝ) (JointErrorData.exactReference t)+
      JointErrorData.exactForce t+
      Jacobian.leftAt x (value3 (PointingCapPolynomial.derivative
        (PointingCapPolynomial.derivative physicalInput.rho)) x t)-
      (Gravity.field3 (physicalInput.K:ℝ) (JointErrorData.exactReference t+
        Jacobian.leftAt x (value3 physicalInput.rho x t))+
        rotate (rotationExp x) (JointErrorData.exactForce t)))≤PolynomialOrder.value rawForcing t := by
  have hK : 0≤(physicalInput.K:ℝ) := by exact_mod_cast JointErrorData.model_K_nonnegative
  have hP : (displacementMaximum:ℝ)<1 := by
    have h0 : (0:ℝ)<displacementMaximum := by exact_mod_cast uniform_ranges_checked.2.2.1
    have h2 : 2*(displacementMaximum:ℝ)<1 := by exact_mod_cast uniform_ranges_checked.2.2.2.1
    linarith
  have hH : (offsetMaximum:ℝ)<1 := by exact_mod_cast uniform_ranges_checked.2.2.2.2.2
  have he := radius_error_growth hx ht
  have hc := constraint_bound hx ht
  have hR := residual_bound hx ht
  have hr : 0<enorm (JointErrorData.exactReference t) := by rw [JointErrorData.exactReference_norm]; norm_num
  have hp : (displacementMaximum:ℝ)<enorm (JointErrorData.exactReference t) := by
    simpa only [JointErrorData.exactReference_norm] using hP
  have he' : |(enorm (JointErrorData.exactReference t+
      Jacobian.leftAt x (value3 physicalInput.rho x t))^2/enorm (JointErrorData.exactReference t)^2-1)-
      (value (LieRadiusQuadraticPolynomial.radius physicalInput) x t-1)|≤PolynomialOrder.value radiusError t := by
    simpa only [JointErrorData.exactReference_norm,one_pow,div_one,sub_sub_sub_cancel_right] using he
  have hc' : |(1+(value (LieRadiusQuadraticPolynomial.radius physicalInput) x t-1))*(1+value physicalInput.h x t)^2-1|≤
      PolynomialOrder.value constraintBound t+PolynomialOrder.value constraintRemainder t := by
    rw [show 1+(value (LieRadiusQuadraticPolynomial.radius physicalInput) x t-1)=
      value (LieRadiusQuadraticPolynomial.radius physicalInput) x t by ring,
      ←LieRadiusQuadraticPolynomial.constraint_value]
    exact hc
  have hr' : enorm (value3 (PointingCapPolynomial.derivative
      (PointingCapPolynomial.derivative physicalInput.rho)) x t+
      ((physicalInput.K:ℝ)/enorm (JointErrorData.exactReference t)^3*(1+value physicalInput.h x t)^3) •
        value3 physicalInput.rho x t-crossProduct x (value3 physicalInput.force x t)+
      ((physicalInput.K:ℝ)/enorm (JointErrorData.exactReference t)^3*((1+value physicalInput.h x t)^3-1)) •
        jacobianInverseQuadratic x (value3 physicalInput.reference x t))≤
      PolynomialOrder.value residualBound t+PolynomialOrder.value residualRemainder t := by
    simpa only [JointErrorData.exactReference_norm,one_pow,div_one,SmallOffsetDefect.full,
      sub_add_eq_add_sub] using hR
  have h := LieRadiusFullDefect.physical_defect_bound (physicalInput.K:ℝ) hK x
    (JointErrorData.exactReference t) (value3 physicalInput.reference x t)
    (value3 physicalInput.rho x t)
    (value3 (PointingCapPolynomial.derivative (PointingCapPolynomial.derivative physicalInput.rho)) x t)
    (JointErrorData.exactForce t) (value3 physicalInput.force x t) (value physicalInput.h x t)
    (value (LieRadiusQuadraticPolynomial.radius physicalInput) x t-1)
    hr (attitude_bound hx).2 (attitude_bound hx).1 (displacement_uniform hx ht) hp
    (offset_uniform hx ht) hH (TDSTTReference.reference_error x ht) (TDSTTReference.force_error x ht) he' hc' hr'
  rw [rawForcing_value]
  simpa only [JointErrorData.exactReference_norm] using h

end
end GNC.OrbitalComparison.TDSTTData.Lie2
